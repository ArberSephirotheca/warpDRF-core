From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lia.
Require R.Free.

Section Defs.
  Definition t (r:range) :=
    forall x,
    ~ R.Free.t x r.

  Lemma def:
    forall e1 e2,
    NClosed e1 ->
    NClosed e2 ->
    t (e1, e2).
  Proof.
    intros.
    intros x N.
    simpl in N.
    destruct N as [N|N]. {
      contradict N.
      apply H.
    }
    contradict N.
    apply H0.
  Qed.

  Lemma inv:
    forall e1 e2,
    t (e1, e2) ->
    NClosed e1 /\ NClosed e2.
  Proof.
    intros.
    unfold t in *.
    split.
    - intros x N.
      specialize H with x.
      contradict H.
      simpl.
      intuition.
    - intros x N.
      specialize H with x.
      contradict H.
      simpl.
      intuition.
  Qed.

  Lemma subst:
    forall r x v,
    t r ->
    r_subst x v r = r.
  Proof.
    unfold t.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    specialize (H x).
    intuition.
    rewrite n_subst_not_free; eauto using n_step_to_not_free.
    rewrite n_subst_not_free; eauto using n_step_to_not_free.
  Qed.
End Defs.