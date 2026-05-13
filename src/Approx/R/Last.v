From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lia.
Require R.HasNext.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> nat -> Prop :=
  | def:
    forall e1 e2 n1 n2,
    NStep tid e1 n1 ->
    NStep tid e2 (S n2) ->
    n1 < S n2 ->
    t (e1, e2) n2.

  Lemma func:
    forall r n,
    t r n ->
    forall n',
    t r n' ->
    n' = n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (x: S n = S n') by eauto using n_step_fun.
    invc x.
    reflexivity.
  Qed.

  Lemma to_n_step:
    forall e1 e2 n,
    t (e1, e2) n ->
    NStep tid (NBin NMinus e2 (NNum 1)) n.
  Proof.
    intros.
    invc H.
    assert (R1: n = eval_nbin NMinus (S n) 1). {
      simpl.
      lia.
    }
    rewrite R1.
    apply n_step_bin; auto.
    auto using n_step_num.
  Qed.

  Lemma from_has_next:
    forall r,
    HasNext.t tid r ->
    exists n, t r n.
  Proof.
    intros.
    invc H.
    destruct n2. { lia. }
    exists n2.
    econstructor.
    all: eauto.
  Qed.

  Lemma to_has_next:
    forall r n,
    t r n ->
    HasNext.t tid r.
  Proof.
    intros.
    invc H.
    eapply HasNext.def; eauto.
  Qed.

End Defs.