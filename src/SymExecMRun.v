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
  | e_run_fork:
    forall i j m1 m2,
    ERun i m1 ->
    ERun j m2 ->
    ERun (Fork i j) (Plus m1 m2)
  | e_run_decl_cons:
    forall e1 e2 n1 n2 i x m1 m2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    ERun (i_subst x (NNum n1) i) m1 ->
    ERun (Decl x (NNum (S n1), NNum n2) i) m2 ->
    ERun (Decl x (e1, e2) i) (Plus m1 m2)
  | e_run_decl_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    ERun (Decl x (e1, e2) i) (One [])
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
        run_decl_cons,
        run_decl_nil,
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
    - destruct IHRun1 as (m1, (Hr1, R1)).
      destruct IHRun2 as (m2, (Hr2, R2)).
      eexists.
      split.
      + eauto using e_run_fork.
      + simpl.
        rewrite R1.
        rewrite R2.
        reflexivity.
    - destruct IHRun1 as (e1', (Hr1, R1)).
      destruct IHRun2 as (e2', (Hr2, R2)).
      eexists.
      split.
      + eapply e_run_decl_cons; eauto.
      + rewrite R1.
        rewrite R2.
        reflexivity.
    - eexists.
      split; eauto using e_run_decl_nil.
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
      erewrite IHERun1; eauto.
      erewrite IHERun2; eauto.
    - inversion H4; subst; clear H4.
      + assert (n0 = n1) by eauto using n_step_fun; subst.
        assert (n3 = n2) by eauto using n_step_fun; subst.
        rewrite IHERun1 with (e2:=m0); auto.
        rewrite IHERun2 with (e2:=m3); auto.
      + assert (n0 = n1) by eauto using n_step_fun; subst.
        assert (n3 = n2) by eauto using n_step_fun; subst.
        Import Omega.
        omega.
    - inversion H2; subst; clear H2;
      assert (n0 = n1) by eauto using n_step_fun; subst;
      assert (n3 = n2) by eauto using n_step_fun; subst
      . {
        Import Omega.
        omega.
      }
      reflexivity.
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
  | f_run_fork:
    forall i j m1 m2 m3,
    FRun i m1 ->
    FRun j m2 ->
    m3 == Plus m1 m2 ->
    FRun (Fork i j) m3
  | f_run_decl_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    FRun (i_subst x (NNum n1) i) m1 ->
    FRun (Decl x (NNum (S n1), NNum n2) i) m2 ->
    m3 == Plus m1 m2 ->
    FRun (Decl x (e1, e2) i) m3
  | f_run_decl_nil:
    forall x i e1 e2 n1 n2 m,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    m == One [] ->
    FRun (Decl x (e1, e2) i) m

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
    - destruct IHFRun1 as (m1', (R1, Hr1)).
      destruct IHFRun2 as (m2', (R2, Hr2)).
      eexists.
      rewrite H1. rewrite R1. rewrite R2.
      split. { reflexivity. }
      eauto using e_run_fork.
    - destruct IHFRun1 as (m1', (R1, Hr1)).
      destruct IHFRun2 as (m2', (R2, Hr2)).
      eexists.
      split. 2: { eauto using e_run_decl_cons. }
      repeat match goal with
        H: _ == _ |- _ => rewrite H; clear H
      end.
      reflexivity.
    - exists (One []).
      eauto using e_run_decl_nil.
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
      f_run_decl_nil,
      f_run_access.
    - eapply f_run_seq; eauto.
      + apply IHERun1; reflexivity.
      + apply IHERun2; reflexivity.
    - eapply f_run_fork; eauto.
      + apply IHERun1; auto.
        reflexivity.
      + apply IHERun2; auto.
        reflexivity.
    - eapply f_run_decl_cons; eauto.
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

  Lemma f_run_decl_cons_eq:
    forall x e1 e2 n1 n2 i m1 m2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    FRun (i_subst x (NNum n1) i) m1 ->
    FRun (Decl x (NNum (S n1), NNum n2) i) m2 ->
    FRun (Decl x (e1, e2) i) (m1 + m2).
  Proof.
    intros.
    eapply f_run_decl_cons with (m1:=m1) (m2:=m2); eauto.
    reflexivity.
  Qed.

  Lemma f_run_decl_nil_eq:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    FRun (Decl x (e1, e2) i) (One []).
  Proof.
    intros.
    eapply f_run_decl_nil; eauto.
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

  Lemma f_run_inv_decl_r_step:
    forall x r i m,
    FRun (Decl x r i) m ->
    exists l, RStep r l.
  Proof.
    intros.
    inversion H; subst; clear H;
      eauto using r_step_def, range_list_to_prop.
  Qed.

  Lemma f_run_decl_1:
    forall x e1 e2 n1 n2 i m,
    FRun (Decl x (e1, e2) i) m ->
    NStep e1 n1 ->
    NStep e2 n2 ->
    FRun (Decl x (NNum n1, NNum n2) i) m.
  Proof.
    intros.
    inversion H; subst; clear H;
    assert (n0 = n1) by eauto using n_step_fun;
    assert (n3 = n2) by eauto using n_step_fun;
    subst.
    + eapply f_run_decl_cons; eauto using n_step_num.
    + eapply f_run_decl_nil; eauto using n_step_num.
  Qed.

  Lemma f_run_inv_decl_nil:
    forall x r i m,
    RPred ge r ->
    FRun (Decl x r i) m ->
    EEq m (One []).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0;
    assert (n1 = n0) by eauto using n_step_fun; subst;
    assert (n3 = n2) by eauto using n_step_fun; subst.
    + Import Omega.
      omega.
    + assumption.
  Qed.

  Lemma f_run_decl_r_pred_ge:
    forall r m i x,
    RPred ge r ->
    m == One [] ->
    FRun (Decl x r i) m.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using f_run_decl_nil.
  Qed.

  Lemma f_run_inv_decl_cons:
    forall x n1 n2 i m,
    n1 < n2 ->
    FRun (Decl x (NNum n1, NNum n2) i) m ->
    exists m1 m2,
    m == m1 + m2 /\
    FRun (i_subst x (NNum n1) i) m1 /\
    FRun (Decl x (NNum (S n1), NNum n2) i) m2.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    assert (n1 = n0) by eauto using n_step_fun, n_step_num; subst;
    assert (n3 = n2) by eauto using n_step_fun, n_step_num; subst.
    + eauto.
    + Import Omega.
      omega.
  Qed.
End Defs.