Require Import NExp.
Require Import BExp.
Require Import Coq.Lists.List.
Require Import AccExp.
Require Import Loc.
Require Import Tid.

Import ListNotations.

Module OneDim.

  (** One dimension *)
  Record access := {
    tid : nat;
    index: nat;
  }.

  Definition A := access.

  (** [ n ] *)

  Definition E := nexp.

  Definition Free := NFree.

  Definition subst := n_subst.

  Inductive Step:  (E * nexp) -> list A -> Prop :=
  | step_def:
    forall idx ni nt t,
    NStep idx ni ->
    NStep t nt ->
    Step (idx, t) [{| index := ni; tid := nt |}].

  Definition AStep := Step.

  Definition a_step (e:nexp*nexp) :=
    let (idx, t) := e in
    match n_step idx, n_step t with
    | Some ni, Some nt => Some [{| index := ni; tid:=nt|}]
    | _, _ => None
    end.

  Lemma a_step_to_prop:
    forall e l,
    a_step e = Some l ->
    AStep e l.
   Proof.
    intros.
    destruct e as (idx, t).
    simpl in *.
    destruct (n_step idx) eqn:Hi; try (inversion H; fail);
    destruct (n_step t) eqn:Ht; try (inversion H; fail);
    inversion H; subst; clear H;
    apply n_step_to_prop in Hi;
    apply n_step_to_prop in Ht.
    constructor; auto.
  Qed.

  Lemma prop_to_a_step:
    forall e l,
    AStep e l ->
    a_step e = Some l.
  Proof.
    intros.
    inversion H; subst; clear H; simpl;
    apply prop_to_n_step in H0;
    apply prop_to_n_step in H1;
    rewrite H0; rewrite H1; reflexivity.
  Qed.

  Definition Safe (a1 a2:A) :=
    tid a1 = tid a2 \/ (tid a1 <> tid a2 /\ index a1 = index a2).

  Lemma a_step_fun:
    forall e v1 v2,
    AStep e v1 ->
    AStep e v2 ->
    v1 = v2.
  Proof.
    unfold AStep; intros.
    inversion H; subst; clear H;
      inversion H0; subst; clear H0.
    assert (ni0 = ni) by eauto using n_step_fun.
    assert (nt0 = nt) by eauto using n_step_fun.
    subst.
    reflexivity.
  Qed.

  Lemma safe_eq_tid:
    forall v1 v2,
    tid v1 = tid v2 -> 
    Safe v1 v2.
  Proof.
    intros.
    destruct v1 as (n1, n2);
    destruct v2 as (n3, n4).
    simpl in *; subst.
    unfold Safe.
    intuition.
  Qed.

  Lemma access_step_inv_tid:
    forall e en n (l:list A),
    AStep (e, en) l ->
    NStep en n -> 
    Forall (fun a=> tid a = n) l.
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

  Lemma access_step_next:
    forall x n a v,
    AStep (subst x (NNum n) a, NNum n) v ->
    forall m,
    exists v',
    AStep (subst x (NNum m) a, NNum m) v'.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H4; subst; clear H4.
    unfold subst in *.
    apply n_step_subst_next with (m1:=m) in H2.
    destruct H2 as (m1, Hn).
    exists [{| tid := m; index := m1|} ].
    constructor; auto using n_step_num.
  Qed.

  Lemma safe_sym:
    forall a1 a2,
    Safe a1 a2 ->
    Safe a2 a1.
  Proof.
    unfold Safe.
    intros.
    destruct H as [H|[H1 H2]]. {
      left.
      rewrite H.
      reflexivity.
    }
    repeat split; auto.
  Qed.

  Lemma subst_subst_eq:
    forall x n1 n2 a,
    subst x (NNum n1) (subst x (NNum n2) a) = subst x (NNum n2) a.
  Proof.
    intros.
    unfold subst.
    apply NExp.n_subst_subst_eq.
  Qed.

  Lemma subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    subst x (NNum n1) (subst y (NNum n2) a) =
    subst y (NNum n2) (subst x (NNum n1) a).
  Proof.
    unfold subst.
    intros.
    auto using NExp.n_subst_subst_neq.
  Qed.

  Lemma subst_subst_neq_2:
    forall x y z n a,
    x <> z ->
    y <> z ->
    subst x (NVar y) (subst z (NNum n) a)
    =
    subst z (NNum n) (subst x (NVar y) a).
  Proof.
    unfold subst.
    intros.
    auto using NExp.n_subst_subst_neq_2.
  Qed.
(*
  Lemma subst_subst_trans:
    forall e x v y,
    ~ In x e ->
    subst x v (subst y (NVar x) e) = subst y v e.
  Proof.
    unfold In, subst.
    intros.
    auto using n_subst_subst_trans.
  Qed.

  Lemma subst_not_in:
    forall x e v,
    ~ In x e ->
    subst x v e = e.
  Proof.
    unfold In, subst.
    intros.
    apply n_subst_not_in; auto.
  Qed.

  Lemma in_subst_neq:
    forall e x y v,
    In x (subst y v e) ->
    ~ NIn x v ->
    In x e.
  Proof.
    unfold In, n_subst.
    intros.
    eapply in_n_subst_neq; eauto.
  Qed.
*)
  Lemma step_proper:
    forall (e' e n n' : nexp) (h : list OneDim.A),
  NEq e e' -> NEq n n' -> Step (e, n) h -> Step (e', n') h.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    rewrite H in *.
    rewrite H0 in *.
    apply step_def; auto.
  Qed.

  Lemma eq_subst_proper:
    forall (x : Var.var) (v v' e : nexp),
   NEq v v' -> NEq (n_subst x v e) (n_subst x v' e).
  Proof.
    intros.
    split; intros.
    - rewrite <- H.
      assumption.
    - rewrite H.
      assumption.
  Qed.

End OneDim.

Instance ONE_DIM : Access := {|
  access_subst := n_subst;
  access_step := OneDim.Step;
  access_safe := OneDim.Safe;
  access_eq := NEq;
  AFree := NFree;
  access_step_fun := OneDim.a_step_fun;
  access_eval1 := OneDim.a_step;
  access_eval1_to_step := OneDim.a_step_to_prop;
  access_step_to_eval1 := OneDim.prop_to_a_step;
  access_tid := OneDim.tid;
  access_safe_eq_tid := OneDim.safe_eq_tid;
  access_step_inv_tid := OneDim.access_step_inv_tid;
  access_step_next := OneDim.access_step_next;
  access_safe_sym := OneDim.safe_sym;
  access_subst_subst_eq := OneDim.subst_subst_eq;
  access_subst_subst_eq_2 := n_subst_subst_eq_2;
  access_subst_subst_neq := OneDim.subst_subst_neq;
  access_subst_subst_neq_2 := OneDim.subst_subst_neq_2;
  access_subst_subst_trans := n_subst_subst_trans;
  access_subst_not_free := n_subst_not_free;
  access_in_subst_neq := n_free_subst_neq;
  access_eq_refl := n_eq_refl;
  access_eq_sym := n_eq_sym;
  access_eq_trans := n_eq_trans;
  access_subst_proper := OneDim.eq_subst_proper;
  access_step_proper := OneDim.step_proper;
  access_subst_subst_neq_3 := n_subst_subst_neq_3;
  access_subst_subst_neq_5 := n_subst_subst_neq_5;
  access_subst_subst_eq_1 := n_subst_subst_eq_1;
  access_free_inv_subst_eq := n_free_inv_subst_eq;
|}.


Module Acc.
  Record access_exp := {
    access_exp_loc: loc;
    access_exp_index: list nexp;
    access_exp_mode : mode;
  }.

  Record access := {
    access_loc: loc;
    access_index: list nat;
    access_mode : mode; 
    access_tid : tid;
  }. 

  Inductive ModeConflict: mode -> mode -> Prop :=
  | mode_conflict_l:
    forall o,
    ModeConflict W o
  | mode_conflict_r:
    forall o,
    ModeConflict o W.

  Inductive Racy: access -> access -> Prop :=
  | racy_def:
    forall t1 t2 i m1 m2 l,
    t1 <> t2 ->
    ModeConflict m1 m2 ->
    Racy {| access_loc := l; access_index := i; access_mode := m1; access_tid := t1 |}
         {| access_loc := l; access_index := i; access_mode := m2; access_tid := t2 |}.

  Inductive SafeAcc: access -> access -> Prop :=
  | safe_acc_neq_loc:
    forall l1 l2 t1 t2 m1 m2 i1 i2,
    l1 <> l2 ->
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := m2; access_index := i2 |}
  | safe_acc_eq_task:
    forall t m1 m2 i1 i2 l1 l2,
    SafeAcc {| access_loc := l1; access_tid := t; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t; access_mode := m2; access_index := i2 |}
  | safe_acc_read:
    forall t1 t2 i1 i2 l1 l2,
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := R; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := R; access_index := i2 |}
  | safe_acc_neq_index:
    forall t1 t2 i1 i2 m1 m2 l1 l2,
    i1 <> i2 ->
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := m2; access_index := i2 |}.

  Section Add.

    Fixpoint eval_acc l i m (tids:list tid) : list access :=
    match tids with
    | [] => []
    | t :: tids =>
      {| access_loc := l; access_tid := t; access_mode := m; access_index := i |}
      :: eval_acc l i m tids
    end.

    Variable tids: list tid.

    Inductive AStep: access_exp -> list access -> Prop :=
    | a_step_def:
      forall i l m n,
      IStep i n -> 
      AStep {| access_exp_loc := l; access_exp_index := i; access_exp_mode := m; |}
            (eval_acc l n m tids).

  End Add.
End Acc.