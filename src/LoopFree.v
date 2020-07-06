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
Require Import Access.
Require Import Util.
Require Import InUtil.
Require Import Tasks.
Require Import SymExec.
Require Conc.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).
  Definition t := (history * Conc.inst) % type.

  Definition LStep e v :=
    exists vs, Hist.GenAccess TID e TID_COUNT vs /\ List.concat vs = v.

  Lemma l_step_fun: forall (e : access_exp) (l1 l2 : history),
    LStep e l1 ->
    LStep e l2 ->
    l1 = l2.
  Proof.
    intros e l1 l2.
    intros (vs1, (Hg1, ?)).
    intros (vs2, (Hg2, ?)).
    assert (vs1 = vs2) by eauto using Hist.gen_access_fun.
    subst.
    reflexivity.
  Qed.


  Instance LoopAcc : AccessInst := {
    access_inst_type := access_exp ;
    access_inst_subst := access_subst;
    access_inst_step := LStep;
    access_inst_in := access_in;
    access_inst_step_fun := l_step_fun;
    access_inst_subst_subst_eq := access_subst_subst_eq;
    access_inst_subst_subst_neq := access_subst_subst_neq;
    access_inst_subst_subst_neq_2 := access_subst_subst_neq_2;
    access_inst_subst_not_in := access_subst_not_in;
    access_inst_subst_subst_trans := access_subst_subst_trans;
    access_inst_in_subst_neq := access_in_subst_neq;
  }.
 
  Coercion NNum: nat >-> nexp.  
  Infix "⇓" := Run (at level 80).
  Notation "⊢" := Hist.Safe.
  Notation "⊨" := Hist.MSafe.
  Infix "*⊆" := AllIncl (at level 80).
  Infix "⊆*" := InclAll (at level 80).
  Infix "*⊆*" := AllInclAll (at level 70).
  Infix "×" := prod (at level 50).
  Infix "↓" := SymExec.Run (at level 80).
  Notation "i '[' x ':=' n ']'" := (Conc.i_subst x n i) (at level 40).

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

  Fixpoint translate (i:Conc.inst) : SymExec.inst :=
    match i with
    | Conc.Skip => SymExec.Skip
    | Conc.Acc e i => SymExec.MemAcc e (translate i)
    | Conc.For x r i j => SymExec.Decl x r (translate i) (translate j)
    | Conc.Loop x l i j => SymExec.Branch x l (translate i) (translate j)
    end.

  Lemma i_subst_translate_rw:
    forall i x n,
    i_subst x n (translate i) =
    translate (Conc.i_subst x n i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi.
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      destruct (Set_VAR.MF.eq_dec x v); auto.
    - rewrite IHi1; rewrite IHi2.
      destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma run_to_all_incl:
    forall i h,
    Conc.Run i h ->
    forall hs,
    Run (translate i) hs ->
    AllIncl hs h.
  Proof.
    intros i h H; induction H; intros.
    - inversion H; subst; clear H.
      auto using all_incl_nil_nil.
    - inversion H1; subst; clear H1.
      simpl in *.
      destruct H4 as (vs, (Hg, ?)).
      subst.
      assert (v = vs) by eauto using Hist.gen_access_fun.
      subst.
      assert (AllIncl hs0 h) by auto.
      auto using all_incl_prepend.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun; subst.
      auto.
    - inversion H1; subst; clear H1.
      apply run_inv_seq in H8.
      destruct H8 as (hs3, (hs4, (?, (Hr1, Hr2)))); subst.
      simpl in *.
      rewrite i_subst_translate_rw in *.
      assert (IHRun1 := IHRun1 _ Hr1).
      assert (IHRun2 := IHRun2 _ H9).
      apply Conc.run_inv_loop in H0.
      destruct H0 as (ha, (hb, (Ha, (Hb, ?)))).
      subst.
      eapply run_inv_branch_all_incl_all in Hr2; eauto.
      apply all_incl_app.
      + apply all_incl_prod.
        * auto using all_incl_appl.
        * apply all_incl_appr.
          apply all_incl_all_incl_all with (ls2:=hs2); auto.
      + auto using all_incl_appr.
    - inversion H0; subst; clear H0.
      auto.
  Qed.

  Theorem completeness:
    forall i h,
    Conc.Run i h ->
    forall hs,
    Run (translate i) hs ->
    Hist.Safe h ->
    Hist.MSafe hs.
  Proof.
    intros.
    assert (AllIncl hs h) by eauto using run_to_all_incl.
    eauto using Hist.safe_to_msafe.
  Qed.

  Lemma run_to_incl_all:
    forall i h,
    Conc.Run i h ->
    forall hs,
    Run (translate i) hs ->
    InclAll h hs.
  Proof.
    intros i h H; induction H; intros.
    - apply incl_all_nil.
    - inversion H1; subst; clear H1; simpl in *.
      match goal with
      | H: LStep _ _ |- _ => destruct H as (vs, (Hvs,?))
      end.
      subst.
      assert (vs = v) by eauto using Hist.gen_access_fun; subst; clear Hvs.
      assert (hs0 <> []) by eauto using run_not_nil.
      apply IHRun in H6; clear IHRun.
      apply incl_all_app.
      + auto using incl_all_prepend_l.
      + auto using incl_all_prepend_r.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun; subst.
      auto.
    - inversion H1; subst; clear H1.
      apply run_inv_seq in H8.
      destruct H8 as (hs3, (hs4, (?, (Hr1, Hr2)))); subst.
      assert (hs4 <> nil) by eauto using run_not_nil.
      simpl in *.
      rewrite i_subst_translate_rw in *.
      assert (IHRun1 := IHRun1 _ Hr1).
      assert (IHRun2 := IHRun2 _ H9).
      eapply run_inv_branch_all_incl_all in Hr2; eauto.
      apply incl_all_app.
      + apply incl_all_app_l.
        auto using incl_all_prod_l.
      + apply incl_all_app_r.
        auto.
    - inversion H0; subst; clear H0.
      auto.
  Qed.

  Theorem soundness:
    forall i h,
    Conc.Run i h ->
    forall hs,
    Run (translate i) hs ->
    Hist.MSafe hs ->
    Hist.Safe h.
  Proof.
    intros.
    assert (InclAll h hs) by eauto using run_to_incl_all.
    eauto using Hist.msafe_to_safe.
  Qed.

  Corollary correctness:
    forall i h hs,
    Conc.Run i h ->
    Run (translate i) hs ->
    Hist.MSafe hs <-> Hist.Safe h.
  Proof.
    intros.
    split; eauto using completeness, soundness.
  Qed.

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

End Defs.


