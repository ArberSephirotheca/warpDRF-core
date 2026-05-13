Require Import NExp.
Require Import RExp.
Require R.Closed.
Require Import Tictac.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> Prop :=
    def:
      forall e1 n1 e2 n2,
      NStep tid e1 n1 ->
      NStep tid e2 n2 ->
      n1 < n2 ->
      t (e1, e2).

  Lemma to_closed:
    forall r,
    t r ->
    Closed.t r.
  Proof.
    intros.
    invc H.
    apply Closed.def.
    all: eauto using n_step_to_closed.
  Qed.
(*

  Lemma from_one:
    forall r n,
    One.t r n ->
    RHasNext r.
  Proof.
    intros.
    apply r_one_to_first in H.
    eauto using r_first_to_has_next.
  Qed.

  Lemma from_step:
    forall r n r',
    RStep r n r' ->
    RHasNext r.
  Proof.
    intros.
    apply r_step_to_first in H.
    eauto using r_first_to_has_next.
  Qed.
*)


End Defs.