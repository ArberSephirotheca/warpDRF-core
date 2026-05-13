Require Import Pure.NExp.
Require Import Pure.BExp.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.
Require Import AVal.

Import ListNotations.
Section Defs.

  Record access_exp := {
    ae_owner: nexp;
    ae_index: nexp;
    ae_mode: mode;
  }.

  Definition ae_write (owner:nexp) (index:nexp) := {|
    ae_owner := owner;
    ae_index := index;
    ae_mode := m_write;
  |}.

  Definition ae_read (owner:nexp) (index:nexp) := {|
    ae_owner := owner;
    ae_index := index;
    ae_mode := m_write;
  |}.

  Definition a_subst x v e :=
  {|
    ae_owner := n_subst x v (ae_owner e);
    ae_index := n_subst x v (ae_index e);
    ae_mode := ae_mode e
  |}.

  Inductive AStep : access_exp -> access_val -> Prop :=
  | a_step_def:
    forall e_index n_index m e_owner n_owner,
    NStep e_owner n_owner ->
    NStep e_index n_index ->
    AStep {| ae_owner := e_owner; ae_index := e_index; ae_mode := m |}
          {| av_owner := n_owner; av_index := n_index; av_mode := m |}.

  Definition AFree x (e:access_exp) :=
    NFree x (ae_owner e) \/ NFree x (ae_index e).

  Definition access_eq x y :=
    ae_mode x = ae_mode y /\
    NEq (ae_owner x) (ae_owner y) /\
    NEq (ae_index x) (ae_index y).

  Lemma a_step_write:
    forall e_owner n_owner e_index n_index,
    NStep e_owner n_owner ->
    NStep e_index n_index ->
    AStep (ae_write e_owner e_index) (av_write n_owner n_index).
  Proof.
    unfold ae_write, av_write.
    intros.
    constructor.
    all: assumption.
  Qed.

  Lemma a_step_read:
    forall e_owner n_owner e_index n_index,
    NStep e_owner n_owner ->
    NStep e_index n_index ->
    AStep (ae_read e_owner e_index) (av_read n_owner n_index).
  Proof.
    unfold ae_read, av_read.
    intros.
    constructor.
    all: assumption.
  Qed.

(*
  Lemma ae_read_subst_commute:
    forall x v e,
    ae_read (n_subst x v e) =
    a_subst x v (ae_read e).
  Proof.
    intros.
    unfold ae_read, a_subst.
    reflexivity.
  Qed.

  Notation n_step := (n_step tid).

  Definition a_step (e:access_exp) : option access_val :=
    match n_step (ae_index e) with
    | Some n =>
      Some {|
        av_index := n;
        av_owner := tid;
        av_mode := ae_mode e
      |}
    | None => None
    end.

  Lemma a_step_to_prop:
    forall e l,
    a_step e = Some l ->
    AStep e l.
   Proof.
    intros.
    destruct e as (ae, t).
    unfold a_step in *.
    simpl in *.
    destruct (n_step ae) eqn:Hi.
    all: invc H.
    constructor.
    apply n_step_to_prop.
    assumption.
  Qed.

  Lemma prop_to_a_step:
    forall e l,
    AStep e l ->
    a_step e = Some l.
  Proof.
    intros.
    invc H.
    unfold a_step.
    simpl.
    apply prop_to_n_step in H0.
    rewrite H0.
    reflexivity.
  Qed.
*)
  Lemma a_step_fun:
    forall e v1 v2,
    AStep e v1 ->
    AStep e v2 ->
    v1 = v2.
  Proof.
    intros.
    invc H.
    invc H0.
    f_equal.
    all: eauto using n_step_fun.
  Qed.
(*
  Lemma a_safe_eq_tid:
    forall v1 v2,
    av_owner v1 = av_owner v2 -> 
    Safe v1 v2.
  Proof.
    intros.
    destruct v1 as (n1, n2, n3);
    destruct v2 as (n4, n5, n6).
    simpl in *; subst.
    unfold Safe.
    unfold not.
    intros N.
    unfold Conflict in *.
    destruct N as (N1,N2).
    simpl in *.
    intuition.
  Qed.
(*
  Lemma a_step_inv_tid:
    forall e en n (l:list A),
    AStep (e, en) l ->
    NStep en n -> 
    Forall (fun a=> av_owner a = n) l.
  Proof.
    intros.
    rewrite Forall_forall; intros.
    inversion H; subst; clear H.
    destruct H1; subst. {
      assert (nt = n) by eauto using n_step_fun.
      simpl.
      assumption.
    }
    contradiction.
  Qed.
*)
(*
  Lemma access_step_next:
    forall x n a v,
    AStep (subst x (NNum n) a, NNum n) v ->
    forall m,
    exists v',
    AStep (subst x (NNum m) a, NNum m) v'.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    unfold subst in *.
    apply n_step_subst_next with (m1:=m) in H2.
    destruct H2 as (m1, Hn).
    exists [{| av_owner := m; av_index := m1; av_mode := (ae_mode a)|} ].
    apply step_def_eq.
    simpl.
    { apply Hn. }
    { auto using n_step_num. }
    { constructor. }
  Qed.
*)
  Lemma a_safe_sym:
    forall a1 a2,
    Safe a1 a2 ->
    Safe a2 a1.
  Proof.
    unfold Safe.
    intros.
    unfold Conflict in *.
    unfold not.
    intuition.
  Qed.
  *)
  Lemma a_subst_subst_eq:
    forall x n1 n2 a,
    a_subst x (NNum n1) (a_subst x (NNum n2) a) = a_subst x (NNum n2) a.
  Proof.
    intros.
    unfold a_subst.
    simpl.
    repeat rewrite NExp.n_subst_subst_eq.
    reflexivity.
  Qed.
(*
  Lemma a_subst_subst_eq_2: 
    forall (x : Var.var) n v e ,
    ~ NFree x v ->
    a_subst x e (a_subst x v n) = a_subst x v n.
  Proof.
    intros.
    unfold a_subst.
    simpl.
    rewrite NExp.n_subst_subst_eq_2; auto.
  Qed.
  *)

  Lemma a_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    a_subst x (NNum n1) (a_subst y (NNum n2) a) =
    a_subst y (NNum n2) (a_subst x (NNum n1) a).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    f_equal.
    all: rewrite NExp.n_subst_subst_neq; auto.
  Qed.

  Lemma a_subst_subst_neq_2:
    forall x y z n a,
    x <> z ->
    y <> z ->
    a_subst x (NVar y) (a_subst z (NNum n) a)
    =
    a_subst z (NNum n) (a_subst x (NVar y) a).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_neq_2; auto.
    rewrite NExp.n_subst_subst_neq_2; auto.
  Qed.

  Lemma a_subst_subst_neq_3 : 
    forall e (x y : Var.var) v1 v2,
       x <> y ->
       ~ NFree y v1 ->
       ~ NFree x v2 ->
       a_subst x v1 (a_subst y v2 e) =
       a_subst y v2 (a_subst x v1 e).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    f_equal.
    all: rewrite NExp.n_subst_subst_neq_3; auto.
  Qed.

  Lemma a_subst_subst_neq_5 : 
    forall e3 (x y : Var.var) (e1 e2 : nexp),
       NClosed e1 ->
       x <> y ->
       a_subst y e1 (a_subst x e2 e3) =
       a_subst x (n_subst y e1 e2) (a_subst y e1 e3).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    f_equal.
    all: rewrite NExp.n_subst_subst_neq_5; auto.
  Qed.
(*
  Lemma a_subst_subst_eq_1 : 
      forall (e1 e2 : nexp) (x : Var.VAR.t) a,
       a_subst x e1 (a_subst x e2 a) = a_subst x (n_subst x e1 e2) a.
  Proof.
    unfold a_subst.
    intros.
    simpl.
    f_equal.
    all: rewrite NExp.n_subst_subst_eq_1; auto.
    reflexivity.
  Qed.
*)
  Lemma a_subst_subst_trans:
    forall e (x : Var.var) v (y : Var.VAR.t),
    ~ AFree x e ->
    a_subst x v (a_subst y (NVar x) e) = a_subst y v e.
  Proof.
    unfold AFree, In, a_subst.
    intros.
    simpl in *.
    f_equal.
    all: rewrite NExp.n_subst_subst_trans; auto.
  Qed.

  Lemma a_subst_not_free
     : forall (x : Var.var) v n,
     ~ AFree x n ->
     a_subst x v n = n.
  Proof.
    unfold a_subst, AFree.
    intros x v (o, i, m) Ha.
    simpl in *.
    f_equal.
    all: rewrite NExp.n_subst_not_free; auto.
  Qed.

  (*
  Lemma a_subst_not_in: 
    forall x (e:access_exp) v,
    ~ NFree x (ae_index e) ->
    a_subst x v e = e.
  Proof.
    unfold a_subst.
    intros.
    destruct e.
    simpl in *.
    f_equal.
    eauto using n_subst_not_free.
  Qed.
*)
  Lemma a_free_inv_subst:
    forall e x y v,
    AFree x (a_subst y v e) ->
    ~ NFree x v ->
    AFree x e.
  Proof.
    unfold AFree, a_subst.
    simpl.
    intros.
    intuition.
    all: apply n_free_inv_subst in H1.
    all: intuition.
  Qed.

  Lemma a_step_proper:
    forall e' e v,
    access_eq e e' ->
    AStep e v ->
    AStep e' v.
  Proof.
    intros.
    invc H0.
    invc H.
    destruct e'.
    simpl in *.
    subst.
    intuition.
    constructor.
    - rewrite <- H.
      assumption.
    - rewrite <- H0.
      assumption.
  Qed.

  Lemma ae_owner_subst:
    forall x v e,
    ae_owner (a_subst x v e)
    = n_subst x v (ae_owner e).
  Proof.
    intros.
    unfold ae_owner.
    destruct e; simpl.
    reflexivity.
  Qed.

  Lemma ae_index_subst:
    forall x v e,
    ae_index (a_subst x v e)
    = n_subst x v (ae_index e).
  Proof.
    intros.
    unfold ae_index.
    destruct e; simpl.
    reflexivity.
  Qed.

  Lemma a_free_subst_neq : 
    forall e (x y : Var.var) (v:nexp),
    AFree x (a_subst y v e) ->
    ~ NFree x v ->
    AFree x e.
  Proof.
    unfold AFree.
    intros.
    rewrite ae_index_subst in *.
    rewrite ae_owner_subst in *.
    intuition.
    all: eauto using n_free_subst_neq.
  Qed.

(*
  Lemma eq_subst_proper:
    forall (x : Var.var) (v v' : nexp) e,
    NEq v v' -> access_eq (a_subst x v e) (a_subst x v' e).
  Proof.
    intros.
    split; intros.
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
  Qed.

  Lemma a_eq_refl:
    forall x, access_eq x x.
  Proof.
    intros.
    unfold access_eq.
    split.
    all: reflexivity.
  Qed.

  Lemma a_eq_sym:
    forall x y,
    access_eq x y -> 
    access_eq y x.
  Proof.
    unfold access_eq in *.
    intros.
    intuition.
  Qed.

  Lemma eq_trans: 
    forall x y z,
    access_eq x y -> 
    access_eq y z -> 
    access_eq x z.
  Proof.
    intros.
    unfold access_eq in *.
    intuition.
    - transitivity (ae_mode y); auto.
    - transitivity (ae_index y); auto.
  Qed.

  Lemma free_inv_subst_eq : 
    forall (x : Var.var) (e : nexp) a,
    NFree x (ae_index (a_subst x e a)) ->
    NFree x e.
  Proof.
    intros.
    unfold a_subst in *. 
    simpl in *.
    apply n_free_inv_subst_eq in H.
    auto.
  Qed.

  Lemma a_in_inv_neq:
    forall x y z a,
    x <> y ->
    x <> z ->
    NFree x (ae_index (a_subst z (NVar y) a)) ->
    NFree x (ae_index a).
  Proof.
    intros.
    apply a_in_subst_neq in H1; auto.
  Qed.
*)
End Defs.
