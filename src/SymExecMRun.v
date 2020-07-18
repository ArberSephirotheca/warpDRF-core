Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import AccExp.
Require Import Exp.
Require Import MExp.
Require Import MultiHist.
Require Import SymExec2.

Import ListNotations.
Import MHistNotations.

(*

  Alternative semantics with algebraic memory operations.
  The FRun semantics differs from the ERun semantics in that it
  allows for rewriting according to MemEquiv.
  
 *)

Section Defs.
  Context {A:Access}.
  Context {I:AccessInst}.
  Notation history := (list access_val).

  Inductive ERun: inst -> mexp -> Prop :=
  | e_run_skip:
    ERun Skip (One [])
  | e_run_seq:
    forall i j m1 m2,
    ERun i m1 ->
    ERun j m2 ->
    ERun (Seq i j) (Prod m1 m2)
  | e_run_if_true:
    forall i j m b,
    BStep b true ->
    ERun i m ->
    ERun (If b i j) m
  | e_run_if_false:
    forall i j m b,
    BStep b false ->
    ERun j m ->
    ERun (If b i j) m
  | e_run_access:
    forall e v,
    access_inst_step e v ->
    ERun (MemAcc e) (One v)
  | e_run_decl:
    forall r l i x m,
    RStep r l ->
    ERun (Branch x l i) m ->
    ERun (Decl x r i) m
  | e_run_branch_cons:
    forall x n l i m1 m2,
    ERun (i_subst x (NNum n) i) m1 ->
    ERun (Branch x l i) m2 ->
    ERun (Branch x (n::l) i) (Plus m1 m2)
  | e_run_branch_nil:
    forall x i,
    ERun (Branch x [] i) (One [])
  | e_run_fork:
    forall i j m1 m2,
    ERun i m1 ->
    ERun j m2 ->
    ERun (Fork i j) (Plus m1 m2)
  .

  Lemma e_run_1:
    forall i e,
    ERun i e ->
    Run i (to_mem e).
  Proof.
    intros i e H.
    induction H; simpl;
      eauto using
        run_skip,
        run_seq,
        run_if_true,
        run_if_false,
        run_access,
        run_decl,
        run_branch_cons,
        run_branch_nil,
        run_fork.
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
    - destruct IHRun1 as (m1, (Hr1, R1)).
      destruct IHRun2 as (m2, (Hr2, R2)).
      eexists.
      split; eauto using e_run_seq.
      simpl.
      apply mem_equiv_prod; eauto using run_not_nil, to_mem_not_nil.
    - destruct IHRun as (m, (Hr, R)).
      eauto using e_run_if_true.
    - destruct IHRun as (m, (Hr, R)).
      eauto using e_run_if_false.
    - exists (One v).
      split; auto using e_run_access.
      reflexivity.
    - destruct IHRun as (e1, (Hr, R)).
      eauto using e_run_decl.
    - destruct IHRun1 as (e1, (Hr1, R1)).
      destruct IHRun2 as (e2, (Hr2, R2)).
      eexists.
      split.
      + apply e_run_branch_cons; eauto.
      + rewrite R1.
        rewrite R2.
        reflexivity.
    - eexists.
      split; eauto using e_run_branch_nil.
      reflexivity.
    - destruct IHRun1 as (m1, (Hr1, R1)).
      destruct IHRun2 as (m2, (Hr2, R2)).
      eexists.
      split.
      + eauto using e_run_fork.
      + simpl.
        rewrite R1.
        rewrite R2.
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
      erewrite IHERun1; eauto.
      erewrite IHERun2; eauto.
    - erewrite IHERun; eauto.
      inversion H1; subst; clear H1; auto.
      assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - erewrite IHERun; eauto.
      inversion H1; subst; clear H1; auto.
      assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - inversion H0; subst; clear H0.
      assert (v0 = v) by eauto using access_inst_step_fun.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun.
      subst.
      erewrite IHERun; eauto.
    - inversion H1; subst; clear H1.
      erewrite IHERun1; eauto.
      erewrite IHERun2; eauto.
    - inversion H; subst; clear H.
      reflexivity.
    - inversion H1; subst; clear H1.
      erewrite IHERun1; eauto.
      erewrite IHERun2; eauto.
  Qed.

  (* ------------------------------ FRun  ---------------------------- *)


  Inductive FRun: inst -> mexp -> Prop :=
  | f_run_skip:
    forall m,
    m == One [] ->
    FRun Skip m
  | f_run_seq:
    forall i j m1 m2 m3,
    FRun i m1 ->
    FRun j m2 ->
    m3 == Prod m1 m2 ->
    FRun (Seq i j) m3
  | f_run_if_true:
    forall i j m b,
    BStep b true ->
    FRun i m ->
    FRun (If b i j) m
  | f_run_if_false:
    forall i j m b,
    BStep b false ->
    FRun j m ->
    FRun (If b i j) m
  | f_run_access:
    forall e v m,
    access_inst_step e v ->
    m == One v ->
    FRun (MemAcc e) m
  | f_run_decl:
    forall r l i x m,
    RStep r l ->
    FRun (Branch x l i) m ->
    FRun (Decl x r i) m
  | f_run_branch_cons:
    forall x n l i m1 m2 m3,
    FRun (i_subst x (NNum n) i) m1 ->
    FRun (Branch x l i) m2 ->
    m3 == Plus m1 m2 ->
    FRun (Branch x (n::l) i) m3
  | f_run_branch_nil:
    forall x i m,
    m == One [] ->
    FRun (Branch x [] i) m
  | f_run_fork:
    forall i j m1 m2 m3,
    FRun i m1 ->
    FRun j m2 ->
    m3 == Plus m1 m2 ->
    FRun (Fork i j) m3
  .

  Lemma f_run_to_e_run:
    forall i m,
    FRun i m ->
    exists m', EEq m m' /\ ERun i m'.
  Proof.
    intros i m H; induction H.
    - eauto using e_run_skip.
    - destruct IHFRun1 as (m1', (R1, Hr1)).
      destruct IHFRun2 as (m2', (R2, Hr2)).
      exists (m1' * m2').
      rewrite H1; rewrite R1; rewrite R2.
      split. { reflexivity. }
      eauto using e_run_seq.
    - destruct IHFRun as (m', (R, Hr)).
      exists m'.
      split; eauto using e_run_if_true.
    - destruct IHFRun as (m', (R, Hr)).
      exists m'.
      split; eauto using e_run_if_false.
    - eauto using e_run_access.
    - destruct IHFRun as (m', (R, Hr)).
      eauto using e_run_decl.
    - destruct IHFRun1 as (m1', (R1, Hr1)).
      destruct IHFRun2 as (m2', (R2, Hr2)).
      eexists.
      split. 2: { eauto using e_run_branch_cons. }
      rewrite H1.
      rewrite R1.
      rewrite R2.
      reflexivity.
    - eauto using e_run_branch_nil.
    - destruct IHFRun1 as (m1', (R1, Hr1)).
      destruct IHFRun2 as (m2', (R2, Hr2)).
      eexists.
      rewrite H1. rewrite R1. rewrite R2.
      split. { reflexivity. }
      eauto using e_run_fork.
  Qed.

  Infix "//" := FRun (at level 50).

  Lemma f_run_def:
    forall i m',
    ERun i m' ->
    forall m,
    EEq m m' ->
    FRun i m.
  Proof.
    intros i m' H.
    induction H; intros;
    eauto using
      f_run_skip,
      f_run_if_true,
      f_run_if_false,
      f_run_decl,
      f_run_branch_nil,
      f_run_access.
    - eapply f_run_seq; eauto.
      + apply IHERun1; reflexivity.
      + apply IHERun2; reflexivity.
    - eapply f_run_branch_cons; eauto.
      + apply IHERun1; auto.
        reflexivity.
      + apply IHERun2; auto.
        reflexivity.
    - eapply f_run_fork; eauto.
      + apply IHERun1; auto.
        reflexivity.
      + apply IHERun2; auto.
        reflexivity.
  Qed.

  Lemma f_run_eq:
    forall i m,
    ERun i m ->
    FRun i m.
  Proof.
    intros.
    assert (m == m) by reflexivity.
    eapply f_run_def; eauto.
  Qed.

  Lemma f_run_1:
    forall i e,
    FRun i e ->
    exists e', e == e' /\ Run i (to_mem e').
  Proof.
    intros.
    apply f_run_to_e_run in H.
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

  Import Morphisms.

  Global Instance f_run_proper_1: Proper (eq ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - apply f_run_to_e_run in H1.
      destruct H1 as (m1, (R1, Hr1)).
      rewrite H0 in R1.
      eauto using f_run_def.
    - apply f_run_to_e_run in H1.
      destruct H1 as (m1, (R1, Hr1)).
      rewrite <- H0 in R1.
      eauto using f_run_def.
  Qed.

  Lemma f_run_fun:
    forall i e1,
    FRun i e1 ->
    forall e2,
    FRun i e2 ->
    e1 == e2.
  Proof.
    intros.
    apply f_run_to_e_run in H.
    destruct H as (m1, (R1, Hr1)).
    apply f_run_to_e_run in H0.
    destruct H0 as (m2, (R2, Hr2)).
    transitivity m1; auto.
    assert (m2 = m1) by eauto using e_run_fun.
    subst.
    symmetry.
    assumption.
  Qed.

  Lemma f_run_branch_cons_eq:
    forall x n l i m1 m2,
    FRun (i_subst x (NNum n) i) m1 ->
    FRun (Branch x l i) m2 ->
    FRun (Branch x (n :: l) i) (m1 + m2).
  Proof.
    intros.
    apply f_run_branch_cons with (m1:=m1) (m2:=m2); auto.
    reflexivity.
  Qed.

  Lemma f_run_branch_nil_eq:
    forall x i,
    FRun (Branch x [] i) (One []).
  Proof.
    intros.
    apply f_run_branch_nil.
    reflexivity.
  Qed.

  Lemma f_run_seq_eq:
    forall i j m1 m2,
    FRun i  m1 ->
    FRun j m2 ->
    FRun (Seq i j) (m1 * m2).
  Proof.
    intros.
    eapply f_run_seq; eauto.
    reflexivity.
  Qed.

  Lemma f_run_fork_eq:
    forall i j m1 m2,
    FRun i  m1 ->
    FRun j m2 ->
    FRun (Fork i j) (m1 + m2).
  Proof.
    intros.
    eapply f_run_fork; eauto.
    reflexivity.
  Qed.

  Lemma f_run_skip_eq:
    FRun Skip (One []).
  Proof.
    apply f_run_skip.
    reflexivity.
  Qed.

End Defs.