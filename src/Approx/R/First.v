From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lia.
Require R.Closed.
Require R.HasNext.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> nat -> Prop :=
  | def:
    forall e1 e2 n1 n2,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    n1 < n2 ->
    t (e1, e2) n1.

  Lemma refl_l:
    forall e n,
    ~ t (e, e) n.
  Proof.
    intros.
    intros N.
    invc N.
    assert (n2 = n) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma func:
    forall r n1 n2,
    t r n1 ->
    t r n2 ->
    n1 = n2.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n1 = n2) by eauto using n_step_fun.
    assert (n3 = n4) by eauto using n_step_fun.
    subst.
    reflexivity.
  Qed.

  Lemma to_step:
    forall e1 e2 n,
    t (e1, e2) n ->
    NStep tid e1 n.
  Proof.
    intros.
    invc H.
    assumption.
  Qed.

  Lemma inv_eq:
    forall n e n',
    t (NNum n, e) n' ->
    n = n'.
  Proof.
    intros.
    invc H.
    eauto using n_step_fun, n_step_num.
  Qed.

  Lemma to_closed:
    forall r n,
    t r n ->
    Closed.t r.
  Proof.
    intros.
    destruct r as (e1, e2).
    invc H.
    intros x N.
    destruct N as [N|N];
      contradict N;
      eauto using n_step_to_not_free.
  Qed.

  Lemma subst:
    forall r n,
    t r n ->
    forall x v,
    t (r_subst x v r) n.
  Proof.
    intros.
    assert (Hx := H).
    apply to_closed in H.
    rewrite Closed.subst; auto.
  Qed.

  Lemma to_has_next:
    forall r n,
    t r n ->
    HasNext.t tid r.
  Proof.
    intros.
    invc H.
    econstructor.
    all: eauto.
  Qed.

  Lemma from_has_next:
    forall r,
    HasNext.t tid r ->
    exists m, t r m.
  Proof.
    intros.
    invc H.
    eexists.
    econstructor.
    all: eauto.
  Qed.

End Defs.