Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Coq.omega.Omega.

Require Import Var.
Require Import Loc.
Require Import Exp.
Require Import AccExp.
Require Import Util.
Require Import InUtil.
Require Import Tasks.
Require Import SymExec2.
Require Conc2.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).
  Definition t := (history * Conc.inst) % type.

  Definition LStep n e v :=
    access_step (e, NNum n) v.

  Lemma l_step_fun n: forall (e : access_exp) (l1 l2 : history),
    LStep n e l1 ->
    LStep n e l2 ->
    l1 = l2.
  Proof.
    intros e l1 l2.
    unfold LStep.
    intros.
    eauto using access_step_fun.
  Qed.


  Instance LoopAcc n : AccessInst := {
    access_inst_type := access_exp;
    access_inst_subst := access_subst;
    access_inst_step := LStep n;
    access_inst_in := access_in;
    access_inst_step_fun := l_step_fun n;
    access_inst_subst_subst_eq := access_subst_subst_eq;
    access_inst_subst_subst_neq := access_subst_subst_neq;
    access_inst_subst_subst_neq_2 := access_subst_subst_neq_2;
    access_inst_subst_not_in := access_subst_not_in;
    access_inst_subst_subst_trans := access_subst_subst_trans;
    access_inst_in_subst_neq := access_in_subst_neq;
  }.

(*
  Lemma run_inv_branch_all_incl_all:
    forall x l i1 i2 hs2,
    Run (Branch x l i1 i2) hs2 ->
    forall hs1,
    Run i2 hs1 ->
    AllInclAll hs1 hs2.
  Proof.
    intros x l i1 i2 hs2 H.
    remember (Branch _ _ _ _).
    generalize dependent i1.
    generalize dependent i2.
    generalize dependent l.
    induction H; intros; inversion Heqi; subst; clear Heqi. {
      assert (IHRun2 := IHRun2 _ _ _ eq_refl _ H1).
      apply all_incl_all_app_r; auto.
    }
    assert (hs = hs1) by eauto using run_fun; subst.
    apply all_incl_all_refl.
  Qed.
*) 
  Variable CurTask : nat.
  Fixpoint translate (i:Conc2.inst) : SymExec2.inst (I:=LoopAcc CurTask) :=
    match i with
    | Conc2.Skip => SymExec2.Skip
    | Conc2.Seq i j => SymExec2.Seq (translate i) (translate j)
    | Conc2.If b i j => SymExec2.If b (translate i) (translate j)
    | Conc2.MemAcc e => SymExec2.MemAcc (I:=LoopAcc CurTask) e
    | Conc2.For x r i => SymExec2.Decl x r (translate i)
    | Conc2.Loop x l i => SymExec2.Branch x l (translate i)
    end.

  Lemma i_subst_translate_rw:
    forall i x n,
    i_subst x n (translate i) =
    translate (Conc2.i_subst x n i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - reflexivity.
    - rewrite IHi.
      destruct (Set_VAR.MF.eq_dec x v); auto.
    - rewrite IHi.
      destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma run_to_all_incl:
    forall i h,
    Conc2.Run CurTask i h ->
    forall hs,
    Run (translate i) hs ->
    AllIncl hs h.
  Proof.
    intros i h H; induction H; intros.
    - inversion H; subst; clear H.
      auto using all_incl_nil_nil.
    - inversion H0; subst; clear H0.
      simpl in *.
      unfold LStep in *.
      assert (v0 = v) by eauto using access_step_fun; subst.
      apply all_incl_cons; auto using incl_refl, all_incl_nil.
    - inversion H1; subst; clear H1.
      apply IHRun1 in H4.
      apply IHRun2 in H6.
      auto using all_incl_prod, all_incl_appl, all_incl_appr.
    - inversion H1; subst; clear H1; auto.
      assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - inversion H1; subst; clear H1; auto.
      assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - inversion H1; subst; clear H1.
      simpl in IHRun.
      assert (l0 = l) by eauto using r_step_fun; subst.
      apply IHRun in H7.
      assumption.
    - simpl in *.
      inversion H1; subst; clear H1.
      rewrite i_subst_translate_rw in *.
      auto using all_incl_app, all_incl_appl, all_incl_appr.
    - simpl in *.
      inversion H; subst; clear H.
      apply all_incl_nil_nil.
  Qed.

  Theorem completeness:
    forall i h,
    Conc2.Run CurTask i h ->
    forall hs,
    Run (translate i) hs ->
    Hist.Safe h ->
    Hist.MSafe hs.
  Proof.
    intros.
    assert (AllIncl hs h) by eauto using run_to_all_incl.
    eauto using Hist.safe_to_msafe.
  Qed.

  Lemma incl_all_eq:
    forall A v,
    @InclAll A v [v].
  Proof.
    unfold InclAll, Ensembles.Included, Ensembles.In; intros.
    auto using m_in_eq.
  Qed.

  Lemma run_to_incl_all:
    forall i h,
    Conc2.Run CurTask i h ->
    forall hs,
    Run (translate i) hs ->
    InclAll h hs.
  Proof.
    intros i h H; induction H; intros; simpl in *.
    - apply incl_all_nil.
    - inversion H0; subst; clear H0.
      simpl in *.
      unfold LStep in *.
      assert (v0 = v) by eauto using access_step_fun.
      subst.
      apply incl_all_eq.
    - inversion H1; subst; clear H1.
      apply incl_all_app.
      + apply incl_all_prod_l; eauto using SymExec2.run_not_nil.
      + apply incl_all_prod_r; eauto using SymExec2.run_not_nil.
    - inversion H1; subst; clear H1; eauto using SymExec2.run_not_nil.
      assert (N: false = true) by eauto using b_step_fun.
      inversion N.
    - inversion H1; subst; clear H1; eauto using SymExec2.run_not_nil.
      assert (N: false = true) by eauto using b_step_fun.
      inversion N.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun; subst.
      auto.
    - inversion H1; subst; clear H1.
      rewrite i_subst_translate_rw in *.
      apply IHRun1 in H7; auto; clear IHRun1.
      apply IHRun2 in H8; auto; clear IHRun2.
      apply incl_all_app.
      + apply incl_all_app_l; eauto using SymExec2.run_not_nil.
      + apply incl_all_app_r; eauto using SymExec2.run_not_nil.
    - apply incl_all_nil.
  Qed.

  Theorem soundness:
    forall i h,
    Conc2.Run CurTask i h ->
    forall hs,
    Run (translate i) hs ->
    Hist.MSafe hs ->
    Hist.Safe h.
  Proof.
    intros.
    assert (InclAll h hs) by eauto using run_to_incl_all.
    eauto using Hist.m_safe_to_safe.
  Qed.

  Corollary correctness:
    forall i h hs,
    Conc2.Run CurTask i h ->
    Run (translate i) hs ->
    Hist.MSafe hs <-> Hist.Safe h.
  Proof.
    intros.
    split; eauto using completeness, soundness.
  Qed.
(*
  Lemma run_inv_branch_1:
    forall x l i j m,
    Run (Branch x l i j) m ->
    exists m', Run j m'.
  Proof.
    induction l; intros.
    - inversion H; subst; clear H.
      eauto.
    - inversion H; subst; clear H.
      eauto.
  Qed.

  Lemma run_conc_to_loopfree:
    forall i h,
    Conc.Run i h ->
    exists m, Run (translate i) m.
  Proof.
    intros.
    induction H; intros.
    - exists [[]].
      apply run_skip.
    - destruct IHRun as (m, Hr).
      eexists.
      simpl.
      apply run_access; eauto.
      simpl.
      unfold LStep.
      eauto.
    - destruct IHRun as (m, Hl).
      simpl.
      eauto using run_decl.
    - destruct IHRun1 as (m, Hr1).
      destruct IHRun2 as (m2, Hr2).
      assert (Hx: exists m', Run (translate i2) m') by eauto using run_inv_branch_1.
      destruct Hx as (m_i2, Hr_i2).
      assert (Run (seq (i_subst x n (translate i1)) (translate i2)) (prod m m_i2)). {
        apply run_seq; auto.
        rewrite i_subst_translate_rw.
        assumption.
      }
      eauto using run_branch_cons.
    - destruct IHRun as (m, Hr).
      eauto using run_branch_nil.
  Qed.

  Corollary correctness_ext:
    forall i h,
    Conc.Run i h ->
    exists m, Run (translate i) m /\
    (Hist.MSafe m <-> Hist.Safe h).
  Proof.
    intros.
    destruct (run_conc_to_loopfree i h) as (m, Hr); auto.
    exists m.
    split; auto.
    eauto using correctness.
  Qed.
*)

End Defs.


