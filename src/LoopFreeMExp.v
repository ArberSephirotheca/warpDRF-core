Require Import Coq.Lists.List.

Require Import Access.
Require Import Tasks.
Require Import MExp.
Require Import MultiHist.
Require Import Conc.
Require Import LoopFree.
Require Import Exp.
Require Import Util.

Import ListNotations.
Import MHistNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).

  Inductive ERun: Conc.inst -> mexp -> Prop :=
  | e_run_skip:
    ERun Conc.Skip (One [])
  | e_run_access:
    forall i e v m,
    Hist.GenAccess TID e TID_COUNT v ->
    ERun i m ->
    ERun (Conc.Acc e i) (Prod (One (List.concat v)) m)
  | e_run_for:
    forall r l i1 i2 x m,
    RStep r l ->
    ERun (Conc.Loop x l i1 i2) m ->
    ERun (Conc.For x r i1 i2) m
  | e_run_loop_cons:
    forall x n l i1 i2 m1 m2,
    ERun (Conc.seq (Conc.i_subst x (NNum n) i1) i2) m1 ->
    ERun (Conc.Loop x l i1 i2) m2 ->
    ERun (Conc.Loop x (n::l) i1 i2) (Plus m1 m2)
  | e_run_loop_nil:
    forall x i1 i2 m,
    ERun i2 m ->
    ERun (Conc.Loop x [] i1 i2) m.

  Lemma e_run_1:
    forall i e,
    ERun i e ->
    Run i (to_mem e).
  Proof.
    intros i e H.
    induction H; simpl.
    - auto using run_skip.
    - rewrite app_nil_r.
      auto using run_access.
    - eauto using run_for.
    - eauto using run_loop_cons.
    - eauto using run_loop_nil.
  Qed.

  Lemma run_inv_nil:
    forall i,
    ~ Run i [].
  Proof.
    intros i H.
    remember ([]).
    generalize dependent Heql.
    induction H; intros.
    - inversion Heql.
    - apply prepend_inv_nil in Heql.
      auto.
    - apply IHRun in Heql.
      assumption.
    - apply IHRun2.
      destruct hs2. {
        reflexivity.
      }
      destruct hs1;
        inversion Heql.
    - auto.
  Qed.

  Lemma run_not_nil:
    forall i m,
    Run i m ->
    m <> [].
  Proof.
    intros.
    intros N.
    subst.
    apply run_inv_nil in H.
    assumption.
  Qed.

  Lemma e_run_2:
    forall i h,
    Run i h ->
    exists e, ERun i e /\ MemEquiv h (to_mem e).
  Proof.
    intros i h H.
    induction H.
    - exists (One []).
      split.
      + apply e_run_skip.
      + simpl.
        reflexivity.
    - destruct IHRun as (e1, (Hr, R)).
      exists (Prod (One (List.concat v)) e1).
      split; auto using e_run_access.
      simpl.
      rewrite app_nil_r.
      repeat rewrite prepend_rw.
      apply mem_equiv_prod_r; eauto using run_not_nil, to_mem_not_nil.
      intros N.
      inversion N.
    - destruct IHRun as (e1, (Hr, R)).
      eauto using e_run_for.
    - destruct IHRun1 as (e1, (Hr1, R1)).
      destruct IHRun2 as (e2, (Hr2, R2)).
      eexists.
      split.
      + apply e_run_loop_cons; eauto.
      + rewrite R1.
        rewrite R2.
        reflexivity.
    - destruct IHRun as (e1, (Hr1, R1)).
      eauto using e_run_loop_nil.
  Qed.

  Lemma e_run_inv_seq:
    forall i1 i2 m,
    ERun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ ERun i1 m1 /\ ERun i2 m2.
  Proof.
    intros.
    apply e_run_1 in H.
    apply run_inv_seq in H.
    destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
    assert (m1 <> []) by eauto using run_not_nil.
    assert (m2 <> []) by eauto using run_not_nil.
    apply e_run_2 in Hr1.
    apply e_run_2 in Hr2.
    destruct Hr1 as (m3, (Hr3, R3)).
    destruct Hr2 as (m4, (Hr4, R4)).
    exists m3.
    exists m4.
    split; auto.
    apply e_eq_iff_m_equiv.
    rewrite R1.
    simpl.
    apply mem_equiv_prod; auto using to_mem_not_nil.
  Qed.

  (* --------------------- FRun ------------------------------ *) 

  Definition FRun i m :=
    exists m', EEq m m' /\ ERun i m'.

  Lemma f_run_def:
    forall i m m',
    EEq m m' ->
    ERun i m' ->
    FRun i m.
  Proof.
    unfold FRun.
    eauto.
  Qed.

  Lemma f_run_eq:
    forall i m,
    ERun i m ->
    FRun i m.
  Proof.
    intros.
    assert (m == m) by reflexivity.
    unfold FRun; eauto.
  Qed.

  Lemma f_run_inv_seq:
    forall i1 i2 m,
    FRun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ FRun i1 m1 /\ FRun i2 m2.
  Proof.
    intros.
    destruct H as (m', (R1, Hr1)).
    apply e_run_inv_seq in Hr1.
    destruct Hr1 as (m1, (m2, (R2, (Hr1, Hr2)))).
    apply f_run_eq in Hr1.
    apply f_run_eq in Hr2.
    rewrite <- R1 in R2.
    eauto.
  Qed.

  Lemma f_run_1:
    forall i e,
    FRun i e ->
    exists e', e == e' /\ Run i (to_mem e').
  Proof.
    intros.
    destruct H as (m, (R, Hr)).
    apply e_run_1 in Hr.
    eauto.
  Qed.

  Lemma f_run_2: forall (i : inst) (h : list history),
    Run i h ->
    exists e, MemEquiv h (to_mem e) /\ FRun i e.
  Proof.
    intros.
    apply e_run_2 in H.
    destruct H as (e, (Hr, Hm)).
    eauto using f_run_eq.
  Qed.

  Lemma e_run_seq:
    forall i1 m1,
    ERun i1 m1 ->
    forall i2 m2,
    ERun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    apply e_run_1 in H.
    apply e_run_1 in H0.
    assert (Hr: Run (seq i1 i2) (prod (to_mem m1) (to_mem m2))) by eauto using run_seq.
    apply e_run_2 in Hr.
    destruct Hr as (e, (Hr1, Hm2)).
    apply f_run_def with (m':=e); auto.
    apply e_eq_iff_m_equiv.
    simpl.
    assumption.
  Qed.

  Import Morphisms.

  Global Instance f_run_proper_1: Proper (eq ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite H0 in R1.
      eauto using f_run_def.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite <- H0 in R1.
      eauto using f_run_def.
  Qed.

  Lemma f_run_seq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2 m3,
    FRun i2 m2 ->
    m3 == (Prod m1 m2) ->
    FRun (seq i1 i2) m3.
  Proof.
    intros.
    rewrite H1.
    destruct H as (m1', (R1, Hr1)).
    destruct H0 as (m2', (R2, Hr2)).
    rewrite R1.
    rewrite R2.
    eauto using e_run_seq.
  Qed.

  Lemma f_run_seq_eq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2,
    FRun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    eapply f_run_seq; eauto.
    reflexivity.
  Qed.

  Lemma e_run_fun:
    forall i e1,
    ERun i e1 ->
    forall e2,
    ERun i e2 ->
    e1 = e2.
  Proof.
    intros i e1 H.
    induction H; intros.
    - inversion H; subst; auto.
    - inversion H1; subst; clear H1.
      assert (v0 = v) by eauto using Hist.gen_access_fun.
      subst.
      apply IHERun in H6.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun.
      subst.
      eauto.
    - inversion H1; subst; clear H1.
      apply IHERun1 in H8.
      apply IHERun2 in H9.
      subst.
      reflexivity.
    - inversion H0; subst; clear H0.
      eauto.
  Qed.

  Lemma f_run_fun:
    forall i e1,
    FRun i e1 ->
    forall e2,
    FRun i e2 ->
    e1 == e2.
  Proof.
    intros.
    destruct H as (m1, (R1, Hr1)).
    destruct H0 as (m2, (R2, Hr2)).
    transitivity m1; auto.
    assert (m2 = m1) by eauto using e_run_fun.
    subst.
    symmetry.
    assumption.
  Qed.

End Defs.