Require Import RExp.
Require Import NExp.
Require Import Tictac.
From Stdlib Require Import Lia.
Require R.Closed.
Require R.HasNext.
Require R.Start.
Require R.End.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> Prop :=
  | def:
    forall e1 e2 n1 n2,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    n1 >= n2 ->
    t (e1, e2).

  Lemma def_eq_num:
    forall n,
    t (NNum n, NNum n).
  Proof.
    intros.
    eapply def; eauto using n_step_num.
  Qed.

  Lemma to_closed:
    forall r,
    t r ->
    Closed.t r.
  Proof.
    intros.
    invc H.
    apply Closed.def; eauto using n_step_to_closed.
  Qed.

  Lemma to_has_next:
    forall r,
    t r ->
    ~ HasNext.t tid r.
  Proof.
    intros.
    invc H.
    intros N.
    invc N.
    assert (n0 = n1) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    lia.
  Qed.

  Lemma from_has_next:
    forall r,
    HasNext.t tid r ->
    ~ t r.
  Proof.
    intros r H N.
    invc H.
    invc N.
    assert (n0 = n1) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    lia.
  Qed.

  Lemma inv:
    forall r,
    t r ->
    forall lo,
    Start.t tid r lo ->
    forall hi,
    End.t tid r hi ->
    lo >= hi.
  Proof.
    intros.
    invc H0.
    invc H1.
    assert (n1 = lo) by eauto using n_step_fun.
    assert (n2 = hi) by eauto using n_step_fun.
    subst.
    invc H.
    assert (n1 = lo) by eauto using n_step_fun.
    assert (n2 = hi) by eauto using n_step_fun.
    subst.
    assumption.
  Qed.

  Lemma from_start_end:
    forall r,
    forall lo,
    Start.t tid r lo ->
    forall hi,
    End.t tid r hi ->
    lo >= hi ->
    t r.
  Proof.
    intros.
    destruct r as (e1, e2).
    invc H.
    invc H0.
    assert (n1 = lo) by eauto using n_step_fun.
    assert (n2 = hi) by eauto using n_step_fun.
    subst.
    eapply def; eauto.
  Qed.
End Defs.