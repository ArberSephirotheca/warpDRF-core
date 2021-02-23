Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationPairs.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import RExp.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.
Require Import PairInUtil.
Require Import VHist.
Require Import Conc.
Require Import Tictac.

Require Import Lia.

Import ListNotations.
Require Conc.

Section Defs.

  Notation history := (list access_val).

  Notation mhistory := (list history).

  Notation histpair := (mhistory * history) % type.

  Context `{T:Tasks}.
  Context {A:Access}.

  Open Scope vhist_scope.

(* -------------------- RUN --------------------------- *)


  Inductive w_inst :=
    (* code ; sync *)
  | WSync: Conc.inst -> w_inst 
    (* P ;  Q *)
  | WSeq: w_inst -> w_inst -> w_inst
    (* c; for { P; c } *)
  | WFor : Conc.inst -> var -> range -> w_inst -> Conc.inst -> w_inst.

  Fixpoint w_subst x v P :=
    match P with
    | WSync c => WSync (Conc.i_subst x v c)
    | WSeq P Q => WSeq (w_subst x v P) (w_subst x v Q)
    | WFor c1 y r P c2 =>
      let (P', c2') := if VAR.eq_dec x y
        then (P, c2)
        else (w_subst x v P, Conc.i_subst x v c2)
      in
      WFor (Conc.i_subst x v c1) y (r_subst x v r) P' c2'
    end.


  Lemma w_subst_subst_neq_3:
    forall P x y v1 v2,
    x <> y ->
    ~ NFree v1 y ->
    ~ NFree v2 x ->
    w_subst x v1 (w_subst y v2 P)
    =
    w_subst y v2 (w_subst x v1 P).
  Proof.
    induction P; intros; simpl.
    - rewrite i_subst_subst_neq_3; auto.
    - rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        destruct (Set_VAR.MF.eq_dec x v). {
          simpl.
          destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        rewrite i_subst_subst_neq_3; auto.
        rewrite r_subst_subst_neq_3; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        simpl.
        subst.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
        rewrite i_subst_subst_neq_3; auto.
        rewrite r_subst_subst_neq_3; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
      destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
      rewrite i_subst_subst_neq_3; auto.
      rewrite i_subst_subst_neq_3 with (c:=i0); auto.
      rewrite r_subst_subst_neq_3; auto.
      rewrite IHP; auto.
  Qed.

  Inductive WRun: w_inst -> vhist -> Prop :=
  | wrun_sync:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    WRun (WSync c) {{ h | [] }}
  | wrun_seq: forall i j mh_i mh_j mh,
    WRun i mh_i ->
    WRun j mh_j ->
    mh_i @ mh_j = mh ->
    WRun (WSeq i j) mh
  | wrun_for_cons:
    forall r r' n h1 h2 m1 m2 m3 c1 x c2 P,
    RStep r n r' ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c2) h2 ->
    WRun (WFor Conc.Skip x r' P c2) m2 ->
    {{ h1 }} @ m1 @ {{ h2 }} @ m2 = m3 ->
    WRun (WFor c1 x r P c2) m3

  | wrun_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall c1 h1 h2 r m m1 n x P c2,
    ROne r n ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c2) h2 ->
    {{ h1 }} @ m1 @ {{ h2 }} = m ->
    WRun (WFor c1 x r P c2) m.


  Inductive CanRun: w_inst -> Prop :=
  | can_run_sync:
    forall c,
    CanRun (WSync c)
  | can_run_seq:
    forall i j,
    CanRun i -> 
    CanRun j ->
    CanRun (WSeq i j)
  | can_run_for:
    forall x r P c1 c2,
    RHasNext r ->
    (forall n, RPick r n -> CanRun (w_subst x (NNum n) P)) -> 
    CanRun (WFor c1 x r P c2).

  Section X_CanRun.
    Variable x:var.
    Variable v:nexp.

  Inductive X_CanRun: w_inst -> Prop :=
  | x_can_run_sync:
    forall c,
    X_CanRun (WSync c)
  | x_can_run_seq:
    forall i j,
    X_CanRun i -> 
    X_CanRun j ->
    X_CanRun (WSeq i j)
  | x_can_run_for:
    forall y r P c1 c2,
    RHasNext (r_subst x v r) ->
    (forall n, RPick (r_subst x v r) n -> X_CanRun (w_subst y (NNum n) P)) -> 
    X_CanRun (WFor c1 y r P c2).
  End X_CanRun.

  Lemma x_can_run_subst:
    forall x v1 P,
    X_CanRun x v1 P ->
    forall v2 n,
    NStep v1 n ->
    NStep v2 n ->
    X_CanRun x v2 P.
  Proof.
    intros x v1 p H.
    induction H; intros v2 n Hn1 Hn2.
    - apply x_can_run_sync.
    - apply x_can_run_seq; eauto.
    - constructor.
      + eauto using r_has_next_subst.
      + eauto using r_pick_subst.
  Qed.

  Lemma w_subst_subst_eq_1:
    forall e1 e2 x P,
    w_subst x e1 (w_subst x e2 P) = w_subst x (n_subst x e1 e2) P.
  Proof.
    induction P; intros; simpl.
    - rewrite i_subst_subst_eq_1.
      auto.
    - rewrite IHP1.
      rewrite IHP2.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        remove_eq v v.
        rewrite i_subst_subst_eq_1.
        rewrite r_subst_subst_eq_1.
        reflexivity.
      }
      simpl.
      remove_eq x v.
      repeat rewrite i_subst_subst_eq_1.
      rewrite r_subst_subst_eq_1.
      rewrite IHP.
      reflexivity.
  Qed.

  Lemma x_can_run_spec:
    forall x v P,
    NClosed v ->
    X_CanRun x v P <-> CanRun (w_subst x v P).
  Proof.
    split; intros. {
      generalize dependent H.
      induction H0; intros; simpl.
      - constructor.
      - constructor; auto.
      - destruct (Set_VAR.MF.eq_dec x y). {
          subst.
          constructor; auto.
          intros.
          rename_hyp (forall n, _ -> _ -> CanRun _) as Hx.
          rename_hyp (RPick _ _) as Hp.
          apply Hx in Hp; auto.
          rewrite w_subst_subst_eq_1 in Hp.
          simpl in *.
          assumption.
        }
        constructor; auto.
        intros.
        rename_hyp (forall n, _ -> _ -> CanRun _) as Hx.
        rename_hyp (RPick _ _) as Hp.
        apply Hx in Hp; auto.
        rewrite w_subst_subst_neq_3; auto.
    }
    remember (w_subst _ _ _) as Q.
    generalize dependent x.
    generalize dependent v.
    generalize dependent P.
    induction H0;
      intros P_in v Hv y Heq;
      destruct P_in;
      simpl in Heq;
      try (invc Heq; fail);
      try (rename v0 into x).
    - invc Heq.
      constructor.
    - destruct (Set_VAR.MF.eq_dec y x); invc Heq.
    - invc Heq.
      constructor; eauto.
    - destruct (Set_VAR.MF.eq_dec y x); invc Heq.
    - rename v0 into x'.
      destruct (Set_VAR.MF.eq_dec y x'); invc Heq. {
        constructor; auto.
        intros.
        rename_hyp (forall n, RPick _ _ -> forall P v, _ -> _) as Hx.
        rename_hyp (RPick _ _) as Hp.
        eapply Hx in Hp; eauto.
        rewrite w_subst_subst_eq_1.
        simpl.
        auto.
      }
      constructor; auto.
      intros.
      rename_hyp (forall n, RPick _ _ -> forall P v, _ -> _) as Hx.
      rename_hyp (RPick _ _) as Hp.
      eapply Hx in Hp; eauto.
      rewrite w_subst_subst_neq_3; eauto.
  Qed.

  Lemma can_run_subst:
    forall x v1 P,
    CanRun (w_subst x v1 P) ->
    forall v2 n,
    NStep v1 n ->
    NStep v2 n ->
    CanRun (w_subst x v2 P).
  Proof.
    intros.
    apply x_can_run_spec; eauto using n_step_to_closed.
    apply x_can_run_spec in H; eauto using n_step_to_closed.
    eauto using x_can_run_subst.
  Qed.

  Lemma run_to_can_run:
    forall w h,
    WRun w h ->
    CanRun w.
  Proof.
    intros.
    intros.
    induction H; constructor; auto; subst.
    - apply r_step_to_has_next in H.
      assumption.
    - intros n' H'.
      destruct r as (e1, e2).
      apply r_pick_inv_first in H'.
      destruct H' as [H'|H'].
      + assert (n' = n).
        * apply r_step_to_first in H.
          eauto using r_first_fun.
        * subst.
          assumption.
      + assert (RPick r' n').
        eauto using r_step_inv_r.
        invc IHWRun2.
        auto.
    - apply r_one_to_has_next in H.
      assumption.
    - intros n' H'.
      destruct r as (e1, e2).
      assert (n' = n).
      + invc H.
        invc H'.
        assert (n1 = n) by eauto using n_step_fun; subst.
        assert (n2 = S n) by eauto using n_step_fun; subst.
        lia.
      + subst.
        assumption.
  Qed.

  Definition WEq P Q :=
    forall h,
    WRun P h <-> WRun Q h.

  Fixpoint WVar x i :=
    match i with
    | WSync c => Conc.Var x c
    | WSeq i j => WVar x i \/ WVar x j
    | WFor c1 y _ P c2 =>
      x = y \/
      Conc.Var x c1 \/
      WVar x P \/ Conc.Var x c2
    end.

  Fixpoint Distinct P :=
    match P with
    | WSync _ => True
    | WSeq P Q => Distinct P /\ Distinct Q
    | WFor c1 x _ P c2 =>
      Conc.Distinct c1
      /\ ~ WVar x P
      /\ ~ Var x c2
      /\ Distinct P
      /\ Conc.Distinct c2
    end.

  Lemma wvar_inv_subst:
    forall y x v i,
    WVar y (w_subst x v i) ->
    WVar y i.
  Proof.
    induction i; simpl; intros; auto.
    - eauto using Conc.var_inv_subst.
    - intuition.
    - destruct (Set_VAR.MF.eq_dec x v0); simpl in *. {
        intuition.
        eauto using Conc.var_inv_subst.
      }
      intuition.
      + eauto using Conc.var_inv_subst.
      + eauto using Conc.var_inv_subst.
  Qed.

  Lemma wrun_one:
    forall i h,
    ~ WRun i {{h}}.
  Proof.
    intros i h.
    intros N.
    remember (v_one _) as v.
    generalize dependent h.
    induction N; intros.
    - inversion Heqv.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h1, (h2, (?, ?))).
      subst.
      eauto using IHN1.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h3, (h4, (Heq1, Heq2))).
      inversion Heq1; subst; clear Heq1.
      apply v_seq_inv_one in Heq2.
      destruct Heq2 as (h1, (h5, (?, Heqv))).
      subst.
      eauto.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h3, (h4, (Heq1, Heqv))).
      inversion Heq1; subst; clear Heq1.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h5, (h6, (?, Heqv))).
      subst.
      eauto.
  Qed.

  Lemma wrun_has_many:
    forall i v,
    WRun i v ->
    HasMany v.
  Proof.
    intros.
    destruct v; simpl; auto.
    apply wrun_one in H.
    assumption.
  Qed.

  Lemma w_run_inv_for_skip:
    forall r P c m x,
    WRun (WFor Conc.Skip x r P c) m ->
    exists m1 h2 n,
    WRun (w_subst x (NNum n) P) m1 /\
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c) h2 /\
    (
    (
      exists m2 r',
      RStep r n r' /\
      WRun (WFor Conc.Skip x r' P c) m2 /\
      m = m1 @ {{ h2 }} @ m2
    )
    \/
    (ROne r n /\ m = m1 @ {{ h2 }})).
  Proof.
    intros.
    inversion H; subst; clear H;
      exists m1;
      exists h2;
      exists n;
      match goal with
        H: Conc.RunAll _ Conc.Skip _ |- _ =>
        apply Conc.run_all_inv_skip in H; subst; simpl; rewrite v_prefix_nil
      end;
      split; auto;
      split; auto
      .
    left.
    eauto.
  Qed.

  Lemma w_run_inv_for_skip_1:
    forall r P c m x,
    WRun (WFor Conc.Skip x r P c) m ->
    exists n,
    RFirst r n /\
    exists m1,
    WRun (w_subst x (NNum n) P) m1 /\
    exists h2,
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c) h2 /\
    exists m2,
    m = m1 @ {{ h2 }} @ m2.
  Proof.
    intros.
    apply w_run_inv_for_skip in H.
    destruct H as (m1, (h2, (n, (Hr, (Hr2, Hx))))).
    exists n.
    destruct Hx as [(m2, (r', (Hrs, (?, Hx))))|(Hx,?)]. {
      subst.
      apply r_step_to_first in Hrs.
      split; auto.
      exists m1.
      split; auto.
      exists h2.
      split; auto.
      exists m2.
      auto.
    }
    subst.
    split; auto using r_one_to_first.
    exists m1.
    split; auto.
    exists h2.
    split; auto.
    exists {{ [] }}.
    rewrite v_seq_one_nil_r.
    auto.
  Qed.

  Lemma wrun_for_inv_has_next:
    forall r P c v x,
    WRun (WFor Conc.Skip x r P c) v ->
    RHasNext r.
  Proof.
    intros.
    inversion H; subst; clear H. {
      eauto using r_step_to_has_next.
    }
    eauto using r_one_to_has_next.
  Qed.

  Lemma w_run_subst:
    forall x e1 e2 P v n,
    WRun (w_subst x e1 P) v ->
    NStep e1 n ->
    NStep e2 n ->
    WRun (w_subst x e2 P) v.
  Proof.
    intros.
    (* TODO: HARD *)
  Admitted.

  (* ------------------ IFIRST --------------------------------------- *)

  Inductive IFirst (a: access_val) : w_inst -> Prop :=
  | i_first_sync:
    forall c,
    CIn a c ->
    IFirst a (WSync c)
  | i_first_seq:
    forall i j,
    IFirst a i ->
    IFirst a (WSeq i j)
  | i_first_for_1:
    forall r c1 P c2 x,
    CIn a c1 ->
    IFirst a (WFor c1 x r P c2)
  | i_first_for_2:
    forall r n c1 x P c2,
    RFirst r n ->
    IFirst a (w_subst x (NNum n) P) ->
    IFirst a (WFor c1 x r P c2).



  Lemma i_first_1:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    List.In a (first v) ->
    IFirst a i.
  Proof.
    intros i v H.
    induction H; intros Hv a Hi; simpl in *.
    - apply i_first_sync.
      eapply c_in_1; eauto.
    - subst.
      apply first_inv_in_seq in Hi.
      intuition.
      + auto using i_first_seq.
      + destruct H1 as (h,(?,Hi)).
        subst.
        simpl in *.
        apply wrun_one in H.
        contradiction.
    - subst.
      apply first_inv_in_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CIn a c1). {
          eapply c_in_1; eauto.
        }
        auto using i_first_for_1.
      }
      apply first_inv_in_seq in Hi.
      destruct Hi as [Hi|(h', (?, Hi))]. {
        apply IHWRun1 in Hi; auto.
        2: { intros N. intuition. apply wvar_inv_subst in N. intuition.  }
        eapply i_first_for_2; eauto using r_step_to_first.
      }
      subst.
      apply wrun_one in H1.
      contradiction.
    - subst.
      apply first_inv_in_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CIn a c1). {
          eapply c_in_1; eauto.
        }
        auto using i_first_for_1.
      }
      apply first_inv_in_seq in Hi.
      destruct Hi as [Hi|(h', (?, Hi))]. {
        eapply i_first_for_2; eauto using r_one_to_first.
        apply IHWRun; auto.
        intros N.
        apply wvar_inv_subst in N.
        intuition.
      }
      subst.
      simpl in *.
      apply wrun_one in H1.
      contradiction.
  Qed.

  Lemma i_first_2:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    IFirst a i ->
    List.In a (first v).
  Proof.
    intros i v H.
    induction H; intros.
    - simpl.
      inversion H1; subst; clear H1.
      inversion H3; subst.
      eapply Conc.run_all_i_in_to_in; eauto.
    - subst.
      inversion H3; subst; clear H3.
      apply IHWRun1 in H4; auto using first_in_seq_l.
      simpl in *.
      auto.
    - subst.
      simpl.
      inversion H6; subst; clear H6. {
        simpl in *.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      simpl in *.
      apply r_step_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply first_in_prefix_r.
      apply IHWRun1 in H12.
      2: { intros N. apply wvar_inv_subst in N. intuition. }
      auto using first_in_seq_l.
    - simpl in *.
      inversion H5; subst; clear H5. {
        simpl.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      apply r_one_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply IHWRun in H12.
      2: { intros N. apply wvar_inv_subst in N. intuition. }
      auto using first_in_seq_l, first_in_prefix_r, first_in_seq_l.
  Qed.

  (* ------------------ ILAST --------------------------------------- *)

  Inductive ILast (a: access_val) : w_inst -> Prop :=
  | i_last_seq:
    forall i j,
    ILast a j ->
    ILast a (WSeq i j)
  | i_last_for_1:
    forall r n c1 P c2 x,
    RLast r n ->
    (forall e, NStep e n -> ILast a (w_subst x e P)) ->
    ILast a (WFor c1 x r P c2)
  | i_last_for_2:
    forall r n c1 P c2 x,
    RLast r n ->
    (forall e, NStep e n -> CIn a (Conc.i_subst x e c2)) ->
    ILast a (WFor c1 x r P c2)
  .

  Ltac handle_not_var :=
    match goal with
    | [  |- ~ WVar TID (w_subst _ _ _) ]  =>
      let N := fresh in
      intros N; apply wvar_inv_subst in N; intuition
    | [  |- ~ Conc.Var TID (Conc.i_subst _ _ _) ] =>
      let N := fresh in
      intros N; apply Conc.var_inv_subst in N; intuition
    | [ |- ~ WVar TID _ ] => simpl in *; intuition
   end.

  Lemma i_last_w_subst:
    forall a P x e1 n,
    NStep e1 n ->
    ILast a (w_subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    x <> TID ->
    ILast a (w_subst x e2 P).
  Proof.
    intros a P x e1 n Hn Hl.
    remember (w_subst _ _ _) as Q.
    generalize dependent e1.
    generalize dependent n.
    generalize dependent P.
    generalize dependent x.
    induction Hl; intros.
    - destruct P; inversion HeqQ; subst; clear HeqQ; simpl.
      + constructor.
        eauto.
      + destruct (Set_VAR.MF.eq_dec x v); inversion H2.
    - assert (r1: NEq e1 e2) by eauto using n_eq_def.
      destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
      destruct (Set_VAR.MF.eq_dec x0 v). {
        subst.
        inversion H5; subst; clear H5.
        eapply i_last_for_1; eauto.
        rewrite r1 in *.
        assumption.
      }
      inversion H5; subst; clear H5.
      rename x0 into y.
      rename P0 into Q.
      destruct r0 as (e1', e2').
      simpl in *.
      rewrite r1 in H.
      eapply i_last_for_1 with (n:=n); eauto.
      intros.
      assert (H0 := H0 _ H4).
      assert (H1 := H1 _ H4 y (w_subst v e Q) n0 e1 Hn).
      assert (ILast a (w_subst y e2 (w_subst v e Q))). {
        apply H1; auto.
        rewrite w_subst_subst_neq_3; eauto using n_step_to_not_free.
      }
      rewrite w_subst_subst_neq_3; eauto using n_step_to_not_free.
  - destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
    rename x0 into y.
    rename v into z.
    assert (r1: NEq e2 e1) by eauto using n_eq_def.
    destruct (Set_VAR.MF.eq_dec y z);
      inversion H4; subst; clear H4. {
      subst.
      eapply i_last_for_2; eauto.
      rewrite r1.
      auto.
    }
    eapply i_last_for_2 with (n:=n); eauto.
    + rewrite r1.
      auto.
    + intros e He.
      assert (~ NFree e2 z) by eauto using n_step_to_not_free.
      assert (~ NFree e y) by eauto using n_step_to_not_free.
      assert (~ NFree e1 z) by eauto using n_step_to_not_free.
      rewrite Conc.i_subst_subst_neq_3; auto.
      assert (Hi : CIn a (Conc.i_subst z e (Conc.i_subst y e1 i0))) by eauto.
      rewrite Conc.i_subst_subst_neq_3 in Hi; auto.
      eapply c_in_subst with (n2:=n0) (v:=e1); eauto.
  Qed.

  Lemma i_last_1:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    List.In a (last v) ->
    ILast a i.
  Proof.
    intros i v H.
    induction H; intros; simpl in *.
    - contradiction.
    - constructor.
      subst.
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
      apply last_inv_in_seq in Hi.
      destruct Hi as [Hi| (h', (?, Hi))]. {
        auto.
      }
      subst.
      apply wrun_one in H0.
      contradiction.
    - subst.
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
      apply last_inv_in_prefix in Hi.
      destruct Hi as [(h', (Heq, Hi))|Hi]. {
        symmetry in Heq.
        apply v_seq_inv_one in Heq.
        destruct Heq as (h1', (h3, (?, Heq))).
        subst.
        apply v_prefix_inv_one in Heq.
        destruct Heq as (h4, ?).
        subst.
        apply wrun_one in H3.
        contradiction.
      }
      apply last_inv_in_seq in Hi.
      destruct Hi as [Hi|(h, (Heq, Hi))]. {
        apply last_inv_in_prefix in Hi.
        destruct Hi as [(h', (?, Hi))| Hi]. {
          subst.
          apply wrun_one in H3.
          contradiction.
        }
        apply IHWRun2 in Hi.
        2: { intros N. intuition. }
        inversion Hi; subst; clear Hi.
        - apply i_last_for_1 with (n:=n0); eauto using r_step_last.
        - eapply i_last_for_2; eauto using r_step_last.
      }
      symmetry in Heq.
      apply v_prefix_inv_one in Heq.
      destruct Heq as (h'', ?).
      subst.
      apply wrun_one in H3.
      contradiction.
    - subst.
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
      apply last_inv_in_prefix in Hi.
      destruct Hi as [(h', (Heq, Hi))|Hi]. {
        symmetry in Heq.
        apply v_seq_inv_one in Heq.
        destruct Heq as (h1', (h3, (?, Heq))).
        inversion Heq; subst; clear Heq.
        apply wrun_one in H1.
        contradiction.
      }
      apply last_inv_in_seq in Hi.
      simpl in *.
      destruct Hi as [Hi|(h', (Heq, Hi))]. {
        eapply i_last_for_2; eauto using r_one_to_last, n_step_num.
        assert (CIn a (Conc.i_subst x (NNum n) c2)). {
          eapply c_in_1; eauto.
          handle_not_var.
        }
        intros e He.
        apply c_in_subst with (v:=NNum n) (n0:=n); auto using n_step_num.
      }
      inversion Heq; subst; clear Heq.
      eapply i_last_for_1; eauto using r_one_to_last, n_step_num.
      {
        assert ( ILast a (w_subst x (NNum n) P)). {
          apply IHWRun; auto.
          handle_not_var.
        }
        intros.
        auto.
        apply i_last_w_subst with (e1:=NNum n) (n:=n); eauto using n_step_num.
      }
  Qed.

  Lemma i_last_2:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    ILast a i ->
    List.In a (last v).
  Proof.
    (* TODO: MEDIUM *)
  Admitted.

  Notation any_inst := (Conc.inst + w_inst) % type.

  Definition OneOf (p:access_val*access_val) (P: any_inst) (Q:any_inst) : Prop :=
    let get_P : access_val -> Prop :=
      match P with
      | inl c => fun a => CIn a c
      | inr P => fun a => ILast a P
      end
    in  
    let get_Q : access_val -> Prop :=
      match Q with
      | inl c => fun a => CIn a c
      | inr Q => fun a => IFirst a Q
      end
    in
    let (a1, a2) := p in
      get_P a1 /\ get_Q a2
      \/
      get_P a2 /\ get_Q a1.

  Inductive IPairIn : (access_val * access_val) -> w_inst -> Prop :=
  | i_pair_in_sync:
    forall p c,
    CPairIn p c ->
    IPairIn p (WSync c)
  | i_pair_in_seq_l:
    forall p i j,
    IPairIn p i ->
    IPairIn p (WSeq i j)
  | i_pair_in_seq_r:
    forall p i j,
    IPairIn p j ->
    IPairIn p (WSeq i j)
  | i_pair_in_seq_both:
    forall p P Q,
    OneOf p (inr P) (inr Q) ->
    IPairIn p (WSeq P Q)
  (* Any iteration *)
  | i_pair_in_for_1:
    forall r e n c1 P c2 p x,
    RPick r n ->
    NStep e n ->
    IPairIn p (w_subst x e P) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_2:
    forall r e n c1 p P x c2,
    RPick r n ->
    NStep e n ->
    CPairIn p (Conc.i_subst x e c2) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_3:
    forall r e n c1 x p P c2,
    RPick r n ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inl (Conc.i_subst x e c2)) ->
    IPairIn p (WFor c1 x r P c2)
  (* ---- FIRST ITERATION ONLY ---- *)
  | i_pair_in_for_first_1:
    forall r c1 p P c2 x,
    CPairIn p c1 ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_first_2:
    forall r e n c1 p P x c2,
    RFirst r n ->
    NStep e n ->
    OneOf p (inl c1) (inr (w_subst x e P)) ->
    IPairIn p (WFor c1 x r P c2)
  (* -------- ALL BUT FIRST ---- *)
  | i_pair_in_for_mid_1:
    forall r n c1 p x P c2 e e',
    RPick2 r n ->
    NStep e n ->
    NStep e' (S n) ->
    OneOf p (inl (Conc.i_subst x e c2)) (inr (w_subst x e' P)) ->
    IPairIn p (WFor c1 x r P c2)

  | i_pair_in_for_mid_2:
    forall r n e e' P x c2 c1 p,
    RPick2 r n ->
    NStep e n ->
    NStep e' (S n) ->
    OneOf p (inr (w_subst x e P)) (inr (w_subst x e' P)) ->
    IPairIn p (WFor c1 x r P c2)
  .

  Lemma i_pair_in_for_run_0_1:
    forall r c1 p h x P c2,
    Conc.RunAll TID_COUNT c1 h ->
    PairIn p h ->
    ~ Conc.Var TID c1 ->
    IPairIn p (WFor c1 r x P c2).
  Proof.
    intros.
    eapply i_pair_in_for_first_1; eauto.
    eapply c_pair_in_1; eauto.
  Qed.

  Lemma i_pair_in_for_run_0_2:
    forall r n c1 P c2 h2 x p,
    RFirst r n ->
    Conc.RunAll TID_COUNT (Conc.i_subst x  (NNum n) c2) h2 ->
    PairIn p h2 ->
    ~ Conc.Var TID (Conc.i_subst x (NNum n) c2) ->
    IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    assert (CPairIn p (Conc.i_subst x (NNum n) c2)). {
      eapply c_pair_in_1; eauto.
    }
    eapply i_pair_in_for_2; eauto using n_step_num.
    auto using r_first_to_pick.
  Qed.

  Lemma i_one_of_1:
    forall i j vi vj,
    WRun i vi ->
    WRun j vj ->
    ~ WVar TID i ->
    ~ WVar TID j ->
    forall p,
    MOneOf p (last vi) (first vj) ->
    OneOf p (inr i) (inr j).
  Proof.
    intros.
    destruct p as (a1, a2).
    unfold MOneOf in *.
    destruct H3 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto; simpl; intuition.
  Qed.

  Lemma i_one_of_2:
    forall c1 P c2 h v r n p x,
    Conc.RunAll TID_COUNT c1 h ->
    RFirst r n ->
    WRun (WFor Conc.Skip x r P c2) v ->
    MOneOf p h (first v) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID (w_subst x (NNum n) P) ->
    OneOf p (inl c1) (inr (w_subst x (NNum n) P)).
  Proof.
    intros.
    apply w_run_inv_for_skip_1 in H1.
    destruct H1 as (n', (Hfst, (m1, (Hr1, (h2, (Hr2, (m2, Heq))))))).
    assert (n' = n) by eauto using r_first_fun.
    subst.
    simpl in *.
    destruct m1 as [h'|h' m1]. {
      simpl in *.
      apply wrun_one in Hr1.
      contradiction.
    }
    destruct p as (a1, a2).
    destruct H2 as [(Ha,Hb)|(Ha,Hb)]; eapply c_in_1 in Ha; eauto. {
      apply first_inv_in_seq in Hb.
      destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
        eapply i_first_1 in Hb; eauto.
        simpl.
        auto.
      }
      inversion Hb1.
    }
    apply first_inv_in_seq in Hb.
    destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
      eapply i_first_1 in Hb; eauto.
      simpl.
      auto.
    }
    inversion Hb1.
  Qed.

  Lemma i_one_of_3:
    forall i v c h p,
    WRun i v ->
    Conc.RunAll TID_COUNT c h ->
    MOneOf p (last v) h ->
    ~ WVar TID i ->
    ~ Conc.Var TID c ->
    OneOf p (inr i) (inl c).
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto; simpl;
      eapply c_in_1 in H0; eauto; exists ci; intuition
      .
  Qed.

  Lemma i_one_of_4:
    forall c1 h1 i m1 p,
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun i m1 ->
    MOneOf p h1 (first m1) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID i ->
    OneOf p (inl c1) (inr i).
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi,Hj)|(Hi,Hj)];
      simpl;
      eapply c_in_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto.
  Qed.

  Lemma i_one_of_skip_l:
    forall p P,
    ~ OneOf p (inl Conc.Skip) P.
  Proof.
    intros (a1, a2) [c|P]; simpl; intros N;
      destruct N as [(N,_)|(N,_)]; apply c_in_skip in N; auto.
  Qed.

  Lemma i_pair_in_for_cons:
    forall r n r' c1 p P c x,
    RStep r n r' ->
    IPairIn p (WFor Conc.Skip x r' P c) ->
    IPairIn p (WFor c1 x r P c).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - eauto using i_pair_in_for_1, r_step_pick_rev.
    - eauto using i_pair_in_for_2, r_step_pick_rev.
    - eauto using i_pair_in_for_3, r_step_pick_rev.
    - apply c_pair_in_skip in H3.
      contradiction.
    - rename_hyp (OneOf _ _ _) as Hi.
      apply i_one_of_skip_l in Hi.
      contradiction.
    - eauto using i_pair_in_for_mid_1, r_step_pick2_rev.
    - eauto using i_pair_in_for_mid_2, r_step_pick2_rev.
  Qed.

  (** Proving the correctness of IPairIn *)

  Lemma i_pair_in_1:
    forall i h,
    WRun i h ->
    ~ WVar TID i -> 
    forall p,
    VHist.MPairIn p h ->
    IPairIn p i.
  Proof.
    intros i h H.
    induction H; intros Hv p Hi; simpl in *.
    - destruct Hi as [Hi|Hi]. 2: {
        apply par_not_in_nil in Hi.
        contradiction.
      }
      eauto using i_pair_in_sync, c_pair_in_1.
    - subst.
      apply VHist.m_pair_in_inv_seq in Hi.
      intuition.
      + auto using i_pair_in_seq_l.
      + auto using i_pair_in_seq_r.
      + eapply i_one_of_1 in H2; eauto.
        eapply i_pair_in_seq_both; eauto.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CPairIn p c1). {
          eapply c_pair_in_1; eauto.
        }
        auto using i_pair_in_for_first_1.
      }
      destruct Hi as [Hi|Hi]. {
        apply VHist.m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|Hi]. {
          assert (IPairIn p (w_subst x (NNum n) P)). {
            apply IHWRun1; auto.
            handle_not_var.
          }
          eapply i_pair_in_for_1; eauto using r_step_to_pick, n_step_num.
        }
        destruct Hi as [Hi|Hi]. {
          apply VHist.m_pair_in_inv_prefix in Hi.
          destruct Hi as [Hi|Hi]. {
            assert (Hc := H2).
            eapply c_pair_in_1 in Hc; eauto.
            2: { handle_not_var. }
            simpl in *.
            eapply i_pair_in_for_run_0_2; eauto using r_step_to_first.
            handle_not_var.
          }
          destruct Hi as [Hi|Hi]. {
            apply IHWRun2 in Hi.
            2: { intuition. }
            eapply i_pair_in_for_cons; eauto.
          }
          (* are we mid or are we last? *)
          assert (Hx := H).
          apply r_step_unfold in H.
          destruct H as [Hr|Hr]. {
            (* last *)
            apply wrun_for_inv_has_next in H3.
            apply r_empty_to_has_next in Hr.
            contradiction.
          }
          (* mid *)
          destruct Hr as (n', Hr).
          assert (n' = S n) by eauto using r_step_inv_next_eq.
          subst.
          eapply i_one_of_2 in Hi; eauto; try handle_not_var.
          apply r_first_to_has_next in Hr.
          eapply i_pair_in_for_mid_1 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        }
        apply m_one_of_inv_first_prefix_l in Hi.
        destruct Hi as [Hi|Hi]. {
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_step_to_pick, n_step_num.
        }
        assert (OneOf p (inr (w_subst x (NNum n) P)) (inr (w_subst x (NNum (S n)) P))). {
          apply w_run_inv_for_skip_1 in H3.
          destruct H3 as (n_b, (Hf, (m_b, (Hr, (h2', (Hrr, (m3', Hx))))))).
          assert (n_b = S n) by eauto using r_step_inv_next_eq.
          subst.
          apply m_one_of_inv_first_seq_l in Hi.
          eapply i_one_of_1 in Hi; eauto; try handle_not_var.
          eauto using wrun_has_many.
        }
        eapply i_pair_in_for_mid_2 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        eapply r_step_to_pick2; eauto using wrun_for_inv_has_next.
      }
      apply m_one_of_inv_first_seq_l in Hi. 2: { eauto using wrun_has_many. }
      eapply i_one_of_4 in Hi; eauto; try handle_not_var.
      eapply i_pair_in_for_first_2; eauto using r_step_to_first, n_step_num.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|[Hi|Hi]].
      + (* c1 *)
        eapply c_pair_in_1 in Hi; eauto.
        eauto using i_pair_in_for_first_1.
      + apply m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|[Hi|Hi]].
        * (* w_subst x (NNum n) i *)
          apply IHWRun in Hi; try handle_not_var.
          eapply i_pair_in_for_1; eauto using r_one_to_pick, n_step_num.
        * simpl in *.
          (* c2 *)
          eapply i_pair_in_for_2; eauto using r_one_to_pick, n_step_num.
          eapply c_pair_in_1; eauto; try handle_not_var.
        * simpl in *.
          (* c2 / w_subst x (NNum n) i *)
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_one_to_pick, n_step_num.
      + (* c1 / w_subst x (NNum n) i *)
        apply m_one_of_inv_first_seq_l in Hi.
        2: { eauto using wrun_has_many. }
        eapply i_one_of_4 in Hi; eauto; try handle_not_var.
        eapply i_pair_in_for_first_2; eauto using r_one_to_first, n_step_num.
  Qed.

  Fixpoint w_seq (c:Conc.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (c_seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 x r P c2 => WFor (c_seq c c1) x r P c2
   end.

  Lemma i_pair_in_subst:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    forall p x P,
    IPairIn p (w_subst x e1 P) ->
    IPairIn p (w_subst x e2 P).
  Proof.
    (* TODO: HARD *)
  Admitted.

  Fixpoint WFree P (x:var) :=
    match P with
    | WSync c => CFree c x
    | WSeq P Q => WFree P x \/ WFree Q x
    | WFor c1 y r P c2 => CFree c1 x \/
      RFree r x \/ (x <> y /\ (WFree P x \/ CFree c2 x))
    end.

  Lemma w_free_inv_subst_eq:
    forall x e P,
    ~ WVar x P ->
    WFree (w_subst x e P) x ->
    NFree e x.
  Proof.
    induction P; simpl; intros.
    - eapply c_free_inv_subst_eq; eauto.
    - intuition.
    - rename_hyp (WFree _ _) as Hw.
      destruct (Set_VAR.MF.eq_dec x v); simpl in *. {
        subst.
        intuition.
      }
      intuition.
      + eauto using c_free_inv_subst_eq.
      + eauto using r_free_inv_subst_eq.
      + eauto using c_free_inv_subst_eq.
  Qed.

  Lemma w_subst_not_free:
    forall x P,
    ~ WFree P x ->
    forall v,
    w_subst x v P = P.
  Proof.
    induction P; simpl; intros.
    - rewrite c_subst_not_free; auto.
    - assert (~ WFree P1 x) by intuition.
      assert (~ WFree P2 x) by intuition.
      rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assert (~ CFree i v) by intuition.
        rewrite c_subst_not_free; auto.
        rewrite r_subst_not_free; auto.
      }
      rewrite c_subst_not_free; auto.
      rewrite r_subst_not_free; auto.
      assert (~  (WFree P x \/ CFree i0 x) ) by intuition.
      rewrite c_subst_not_free; auto.
      rewrite IHP; auto.
  Qed.

  Definition WClosed P :=
    forall x,
    ~ WFree P x.

  Lemma w_closed_inv_seq:
    forall P1 P2,
    WClosed (WSeq P1 P2) ->
    WClosed P1 /\ WClosed P2.
  Proof.
    unfold WClosed.
    intros.
    split;
      simpl in *;
      intros;
      assert (H:= H x);
      intuition.
  Qed.

  Lemma w_closed_inv_for:
    forall c1 x r P c2,
    WClosed (WFor c1 x r P c2) ->
    CClosed c1
    /\ RClosed r
    /\ (forall y, x <> y ->  ~ WFree P y)
    /\ (forall y, x <> y -> ~ CFree c2 y).
  Proof.
    intros.
    unfold WClosed in H.
    simpl in *.
    repeat split; intros y n; assert (H := H y); intuition.
  Qed.

  Inductive GetFirst : w_inst -> inst -> Prop :=
  | get_first_sync:
    forall c,
    GetFirst (WSync c) c
  | get_first_seq:
    forall P c Q,
    GetFirst P c ->
    GetFirst (WSeq P Q) c
  | get_first_for:
    forall c1 x r P n c2 c,
    RFirst r n ->
    GetFirst (w_subst x (NNum n) P) c ->
    GetFirst (WFor c1 x r P c2) (Conc.c_seq c1 c).

  Lemma get_first_fun:
    forall P c,
    GetFirst P c ->
    forall c',
    GetFirst P c' ->
    c' = c.
  Proof.
    intros P c H.
    induction H; intros c' Hg; invc Hg; auto.
    assert (n0 = n) by eauto using r_first_fun.
    subst.
    assert (c4 = c) by eauto.
    subst.
    reflexivity.
  Qed.

  Lemma get_first_subst:
    forall P c,
    GetFirst P c ->
    forall x v,
    NClosed v ->
    ~ WVar x P ->
    GetFirst (w_subst x v P) (i_subst x v c).
  Proof.
    intros P c H.
    induction H; intros y v Hc Hv.
    - simpl.
      constructor.
    - simpl in *.
      apply get_first_seq.
      eauto.
    - simpl.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        simpl in *.
        intuition.
      }
      assert (Hn : NClosed (NNum n)) by auto using n_closed_num.
      simpl in *.
      assert (Hw: ~ WVar y (w_subst x (NNum n) P) ). {
        intros N.
        apply wvar_inv_subst in N.
        intuition.
      }
      assert (IHGetFirst := IHGetFirst y v Hc Hw).
      rewrite Conc.c_subst_c_seq.
      apply get_first_for with (n:=n).
      + auto using r_first_subst_1.
      + rewrite w_subst_subst_neq_3; auto.
  Qed.

  Lemma get_first_exists:
    forall P,
    CanRun P ->
    exists c, GetFirst P c.
  Proof.
    intros P H.
    induction H.
    - eexists.
      constructor.
    - destruct IHCanRun1 as (c, Hg).
      eexists.
      constructor.
      eauto.
    - destruct H as (n, Hp).
      assert (RPick r n) by eauto using r_first_to_pick.
      assert (Hg : exists c, GetFirst (w_subst x (NNum n) P) c). {
        eauto.
      }
      destruct Hg as (c, Hg).
      eexists.
      apply get_first_for with (n:=n); eauto.
  Qed.

  Lemma get_first_1:
    forall P c,
    GetFirst P c ->
    forall a,
    CIn a c ->
    IFirst a P.
  Proof.
    intros P c H.
    induction H; intros a Hi.
    - constructor; auto.
    - constructor.
      auto.
    - apply c_in_inv_c_seq in Hi.
      destruct Hi as [Hi|Hi].
      + auto using i_first_for_1.
      + eauto using i_first_for_2.
  Qed.

  Lemma get_first_2:
    forall P a,
    IFirst a P ->
    forall c,
    GetFirst P c ->
    CIn a c.
  Proof.
    intros P a H.
    induction H; intros c_out Hg; invc Hg; auto.
    - eauto using c_in_c_seq_l.
    - assert (n0 = n) by eauto using r_first_fun.
      subst.
      eauto using c_in_c_seq_r.
  Qed.

  Corollary get_first_spec:
    forall P c,
    GetFirst P c ->
    forall a,
    IFirst a P <-> CIn a c.
  Proof.
    split; intros.
    - eauto using get_first_2.
    - eauto using get_first_1.
  Qed.

  Lemma distinct_subst:
    forall P,
    Distinct P ->
    forall x v,
    Distinct (w_subst x v P).
  Proof.
    induction P; simpl; intros; auto. {
      destruct H; eauto.
    }
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      simpl.
      intuition.
      eauto using distinct_subst.
    }
    simpl.
    intuition.
    - eauto using distinct_subst.
    - rename_hyp (WVar v _) as Hv.
      apply wvar_inv_subst in Hv.
      contradiction.
    - rename_hyp (Var v _) as Hv.
      apply var_inv_subst in Hv.
      contradiction.
    - auto using Conc.distinct_subst.
  Qed.

  Inductive GetLast : w_inst -> inst -> Prop :=
  | get_last_sync:
    forall c,
    GetLast (WSync c) Skip
  | get_last_seq:
    forall P c Q,
    GetLast Q c ->
    GetLast (WSeq P Q) c
  | get_last_for:
    forall c1 x r P n c2 c,
    RLast r n ->
    GetLast (w_subst x (NNum n) P) c ->
    GetLast (WFor c1 x r P c2) (Conc.c_seq c (i_subst x (NNum n) c2)).

  Lemma get_last_1:
    forall P c,
    GetLast P c ->
    forall a,
    ~ WVar TID P ->
    CIn a c ->
    ILast a P.
  Proof.
    intros P c H.
    induction H; intros a Hv Hc.
    - apply c_in_skip in Hc.
      contradiction.
    - constructor.
      simpl in *.
      auto.
    - simpl in *.
      apply c_in_inv_c_seq in Hc.
      destruct Hc. {
        eapply i_last_for_1; eauto.
        intros.
        apply i_last_w_subst with (e1:=NNum n) (n:=n); auto using n_step_num.
        apply IHGetLast; auto.
        intros N.
        apply wvar_inv_subst in N.
        intuition.
      }
      eapply i_last_for_2; eauto.
      intros.
      apply c_in_subst with (v:=NNum n) (n0:=n); auto using n_step_num.
  Qed.

  Lemma get_last_2:
    forall P a,
    ILast a P ->
    forall c,
    GetLast P c ->
    CIn a c.
  Proof.
    intros P a H.
    induction H; intros c Hg; invc Hg.
    - auto.
    - assert (n0 = n) by eauto using r_last_fun.
      subst.
      eauto using c_in_c_seq_l, n_step_num.
    - assert (n0 = n) by eauto using r_last_fun.
      subst.
      eauto using c_in_c_seq_r, n_step_num.
  Qed.

  Corollary get_last_spec:
    forall P c,
    GetLast P c ->
    ~ WVar TID P ->
    forall a,
    ILast a P <-> CIn a c.
  Proof.
    split; intros.
    - eauto using get_last_2.
    - eauto using get_last_1.
  Qed.

  Lemma get_last_exists:
    forall P,
    CanRun P ->
    exists c, GetLast P c.
  Proof.
    intros P H.
    induction H.
    - eexists.
      constructor.
    - destruct IHCanRun2 as (c, Hg).
      eexists.
      constructor.
      eauto.
    - edestruct r_has_next_to_last as (n, Hl); eauto.
      assert (RPick r n) by eauto using r_last_to_pick.
      assert (Hg : exists c, GetLast (w_subst x (NNum n) P) c). {
        eauto.
      }
      destruct Hg as (c, Hg).
      eexists.
      apply get_last_for with (n:=n); eauto.
  Qed.

  Lemma i_pair_in_2_for_1:
    forall x n c2 h2 r P e' e p (* r'*) h0 m0 h1 m1 m2,
    RunAll TID_COUNT (i_subst x (NNum n) c2) h2 ->
    ~ Var TID c2 ->
    ~ WVar TID P ->
    x <> TID ->
    NStep e' (S n) ->
    NStep e n ->
    OneOf p (inl (i_subst x e c2)) (inr (w_subst x e' P)) ->
    RFirst r (S n) ->
    RunAll TID_COUNT Skip h0 ->
    WRun (w_subst x (NNum (S n)) P) m0 ->
    MPairIn p
      (v_prefix h1
         (v_seq m1
            (v_prefix h2 (v_seq (v_one h0) (v_seq m0 m2))))).
  Proof.
    intros.
    rename_hyp (RunAll _ Skip _) as hr.
    apply run_all_inv_skip in hr.
    subst.
    simpl.
    rewrite v_prefix_nil.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e' P) m0). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (~ WVar TID (w_subst x e' P)). {
      intros N.
      apply wvar_inv_subst in N.
      auto.
    }
    assert (~ Var TID (i_subst x e c2)). {
      intros N.
      apply var_inv_subst in N.
      auto.
    }
    assert (RunAll TID_COUNT (i_subst x e c2) h2). {
      apply c_run_subst with (e0:=NNum n) (n0:=n);
      auto using n_step_num.
      eauto using n_step_to_not_free.
    }
    destruct ho as [(hc2,hf)|(hc2,hf)];
    eapply i_first_2 with (v:=m0) in hf; auto;
    apply c_in_2 with (h:=h2) in hc2; auto;
    apply m_pair_in_prefix_r;
    apply m_pair_in_seq_r.
    - auto using m_pair_in_prefix_1, first_in_seq_l.
    - auto using m_pair_in_prefix_2, first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_2:
    forall x n c2 h2 P e' e p (* r'*) h0 m0 h1 m1 m2,
    ~ Var TID c2 ->
    ~ WVar TID P ->
    x <> TID ->
    WRun (w_subst x (NNum n) P) m1 ->
    NStep e' (S n) ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inr (w_subst x e' P)) ->
    RunAll TID_COUNT Skip h0 ->
    WRun (w_subst x (NNum (S n)) P) m0 ->
    MPairIn p
      (v_prefix h1
         (v_seq m1 (v_prefix h2 (v_seq (v_one h0) (v_seq m0 m2))))).
  Proof.
    intros.
    rename_hyp (RunAll _ Skip _) as hr.
    apply run_all_inv_skip in hr.
    subst.
    simpl.
    rewrite v_prefix_nil.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (WRun (w_subst x e' P) m0). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (~ WVar TID (w_subst x e' P)). {
      intros N.
      apply wvar_inv_subst in N.
      auto.
    }
    assert (~ WVar TID (w_subst x e P)). {
      intros N.
      apply wvar_inv_subst in N.
      auto.
    }
    apply m_pair_in_prefix_r.
    destruct ho as [(hl,hf)|(hl,hf)];
      apply i_first_2 with (v:=m0) in hf; auto;
      apply i_last_2 with (v:=m1) in hl; auto.
    * auto using m_pair_in_seq_both_1,first_in_prefix_r, first_in_seq_l.
    * auto using m_pair_in_seq_both_2,first_in_prefix_r, first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_3:
    forall x n P e p c1 h1 m1 m2,
    ~ Var TID c1 ->
    ~ WVar TID P ->
    RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    NStep e n ->
    OneOf p (inl c1) (inr (w_subst x e P)) ->
    MPairIn p (v_prefix h1 (v_seq m1 m2)).
  Proof.
    intros.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (~ WVar TID (w_subst x e P)). {
      intros N.
      apply wvar_inv_subst in N.
      intuition.
    }
    destruct ho as [(hc,hf)|(hc,hf)];
    apply c_in_2 with (h:=h1) in hc; auto;
    apply i_first_2 with (v:=m1) in hf; auto.
    * apply m_pair_in_prefix_1; auto using first_in_seq_l.
    * apply m_pair_in_prefix_2; auto using first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_4:
    forall x n P e p h1 m1 m2 c2 h2,
    ~ Var TID c2 ->
    ~ WVar TID P ->
    x <> TID ->
    WRun (w_subst x (NNum n) P) m1 ->
    RunAll TID_COUNT (i_subst x (NNum n) c2) h2 ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inl (i_subst x e c2)) ->
    MPairIn p (v_prefix h1 (v_seq m1 (v_prefix h2 m2))).
  Proof.
    intros.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (~ WVar TID (w_subst x e P)). {
      intros N.
      apply wvar_inv_subst in N.
      auto.
    }
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (~ Var TID (i_subst x e c2)). {
      intros N.
      apply var_inv_subst in N.
      auto.
    }
    assert (RunAll TID_COUNT (i_subst x e c2) h2). {
      assert (~ NFree e TID). {
        apply n_closed_to_not_free.
        eauto using n_step_to_closed.
      }
      eapply c_run_subst with (e0:=NNum n); eauto using n_step_num.
    }
    destruct ho as [(hl, hc)|(hl,hc)];
    apply i_last_2 with (v:=m1) in hl; auto;
    apply c_in_2 with (h:=h2) in hc; auto;
    apply m_pair_in_prefix_r.
    - apply m_pair_in_seq_both_1; auto using first_in_prefix_l.
    - apply m_pair_in_seq_both_2; auto using first_in_prefix_l.
  Qed.


  Lemma i_pair_in_2:
    forall i h,
    WRun i h ->
    ~ WVar TID i -> 
    forall p,
    IPairIn p i ->
    VHist.MPairIn p h.
  Proof.
    intros i h H.
    induction H; intros Hv p Hp.
    - invc Hp.
      left.
      eauto using c_pair_in_to_pair_in.
    - subst.
      simpl in Hv.
      invc Hp.
      + apply m_pair_in_seq_l.
        apply IHWRun1; auto.
      + apply m_pair_in_seq_r.
        apply IHWRun2; auto.
      + destruct p as (a1, a2).
        simpl in *.
        intuition;
        rename_hyp (ILast _ _) as hl;
        rename_hyp (IFirst _ _) as hf;
        eapply i_first_2 in hf; eauto;
        eapply i_last_2 in hl; eauto.
        * auto using m_pair_in_seq_both_1.
        * auto using m_pair_in_seq_both_2.
    - subst.
      simpl.
      invc Hp.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          assert (MPairIn p m1). {
            apply IHWRun1. {
              simpl in Hv.
              intros N.
              apply wvar_inv_subst in N.
              auto.
            }
            eapply i_pair_in_subst; eauto using n_step_num.
          }
          auto using m_pair_in_prefix_r, m_pair_in_seq_l.
        }
        assert (MPairIn p m2). {
          apply IHWRun2. {
            simpl in *.
            intros N.
            intuition.
          }
          eapply i_pair_in_for_1; eauto.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          apply m_pair_in_prefix_r.
          apply m_pair_in_seq_r.
          apply m_pair_in_prefix_l.
          eapply c_pair_in_to_pair_in; eauto. {
            intros N.
            apply var_inv_subst in N.
            simpl in Hv.
            intuition.
          }
          eapply c_pair_in_subst; eauto using n_step_num.
          simpl in Hv.
          intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2. {
            simpl in *.
            intros N.
            intuition.
          }
          eapply i_pair_in_for_2; eauto using r_step_inv_r.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          simpl in Hv.
          apply i_pair_in_2_for_4 with (x:=x) (n:=n) (P:=P) (c2:=c2) (e:=e);
            auto; intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2. {
            simpl in *.
            intros N.
            intuition.
          }
          eapply i_pair_in_for_3; eauto using r_step_inv_r.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + apply m_pair_in_prefix_l.
        eapply c_pair_in_to_pair_in; eauto.
        simpl in Hv.
        auto.
      + assert (n0 = n). {
          assert (RFirst r n) by eauto using r_step_to_first.
          eauto using r_first_fun.
        }
        subst.
        simpl in Hv.
        apply i_pair_in_2_for_3 with (x:=x) (n:=n) (P:=P) (e:=e) (c1:=c1);
          eauto using n_step_num; intuition.
      + rename_hyp (RPick2 _ _) as hp.
        eapply r_step_pick2_advance in hp; eauto.
        destruct hp as [(?,hp)|hp]. {
          subst.
          rename_hyp (WRun (WFor _ _ _ _ _) _ ) as hr.
          invc hr. 2: {
            rename_hyp (ROne _ _) as ro.
            assert (n0 = S n). {
              assert (RFirst r' n0) by eauto using r_one_to_first.
              eauto using r_first_fun.
            }
            subst.
            simpl in Hv.
            eapply i_pair_in_2_for_1; eauto; intuition.
          }
          assert (n0 = S n). {
            assert (RFirst r' n0) by eauto using r_step_to_first.
            eauto using r_first_fun.
          }
          subst.
          simpl in Hv.
          eapply i_pair_in_2_for_1; eauto; intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2. {
            simpl in *.
            intuition.
          }
          eapply i_pair_in_for_mid_1; eauto.
        }
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        apply m_pair_in_prefix_r.
        auto.
      + rename_hyp (RPick2 _ _) as hp.
        eapply r_step_pick2_advance in hp; eauto.
        destruct hp as [(?,hp)|hp]. {
          subst.
          rename_hyp (WRun (WFor _ _ _ _ _) _ ) as hr.
          invc hr. 2: {
            assert (n0 = S n). {
              assert (RFirst r' n0) by eauto using r_one_to_first.
              eauto using r_first_fun.
            }
            subst.
            simpl in Hv.
            eapply i_pair_in_2_for_2; eauto.
            intuition.
          }
          assert (n0 = S n). {
            assert (RFirst r' n0) by eauto using r_step_to_first.
            eauto using r_first_fun.
          }
          subst.
          simpl in Hv.
          eapply i_pair_in_2_for_2; eauto.
          intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2. {
            simpl in *.
            intuition.
          }
          eapply i_pair_in_for_mid_2; eauto.
        }
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        apply m_pair_in_prefix_r.
        auto.
    - subst.
      simpl.
      invc Hp.
      + assert (MPairIn p m1). {
          apply IHWRun. {
            simpl in Hv.
            intros N.
            apply wvar_inv_subst in N.
            intuition.
          }
          eauto using i_pair_in_subst, n_step_num.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_l.
      + assert (n0 = n) by eauto using r_one_pick_fun.
        subst.
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        simpl.
        eapply c_pair_in_to_pair_in; eauto. {
          intros N.
          apply var_inv_subst in N.
          simpl in Hv.
          auto.
        }
        eapply c_pair_in_subst; eauto using n_step_num.
        simpl in Hv.
        intuition.
      + assert (n0 = n) by eauto using r_one_pick_fun.
        subst.
        assert (rx: v_one h2 = v_prefix h2 (v_one [])). {
          simpl.
          rewrite app_nil_r.
          reflexivity.
        }
        rewrite rx.
        simpl in Hv.
        apply i_pair_in_2_for_4 with (x:=x) (n:=n) (P:=P) (c2:=c2) (e:=e);
          auto; intuition.
      + apply m_pair_in_prefix_l.
        eapply c_pair_in_to_pair_in; eauto.
        simpl in Hv.
        auto.
      + assert (n0 = n) by eauto using r_one_to_first, r_first_fun.
        subst.
        simpl in Hv.
        apply i_pair_in_2_for_3 with (x:=x) (n:=n) (P:=P) (e:=e) (c1:=c1);
          auto using n_step_num; intuition.
      + rename_hyp (RPick2 _ _) as hp.
        contradict hp.
        eauto using r_one_to_not_pick2.
      + rename_hyp (RPick2 _ _) as hp.
        contradict hp.
        eauto using r_one_to_not_pick2.
  Qed.

  Definition DRF P :=
    forall p,
    IPairIn p P ->
    access_safe (fst p) (snd p).

End Defs.

Module ALangNotations.
  Import Conc.CLangNotations.
  Infix ";" := WSeq (at level 50, only printing)
    : lang_scope.
  Notation "c [ x := v ]" := (i_subst x v c) (at level 30, only printing)
    : lang_scope. 
  Infix ";;" := w_seq (at level 50, only printing)
    : lang_scope.
  Notation "c1 ';' 'for' x 'in' r '{' P ',' c2 '}' " := (WFor c1 x r P c2) (at level 50, only printing)
    : lang_scope.
  Infix "∈" := IPairIn (at level 30, only printing)
    : lang_scope.
End ALangNotations.