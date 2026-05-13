Require Import NExp.
Require Import RExp.
Require Import Tictac.
Require R.Start.
Require R.HasNext.
Require R.Last.
Require R.Pick.
Require R.Empty.
Require R.Step.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Wf.

Definition f (lo:nat) (hi:nat) := List.seq lo (hi - lo).

Module Range.

  Inductive t : nat -> nat -> list nat -> Prop :=
  | base:
    forall lo hi,
    lo >= hi ->
    t lo hi []
  | step:
    forall lo hi l,
    lo < hi ->
    t (S lo) hi l ->
    t lo hi (lo::l).


  Lemma succ:
    forall lo hi l,
    t lo hi l ->
    t (S lo) (S hi) (List.map S l).
  Proof.
    intros lo hi l H.
    induction H.
    all: simpl.
    - constructor.
      lia.
    - constructor.
      all: auto.
      lia.
  Qed.

  Lemma zero:
    forall n,
    t 0 n (seq 0 n).
  Proof.
    induction n.
    all: simpl.
    - constructor.
      lia.
    - rewrite cons_seq.
      simpl.
      constructor.
      + lia.
      + apply succ in IHn.
        rewrite seq_shift in IHn.
        assumption.
  Qed.

  Lemma make:
    forall lo hi,
    t lo hi (f lo hi).
  Proof.
    unfold f.
    intros lo hi.
    generalize dependent lo.
    induction hi.
    all: intros lo.
    all: simpl.
    - constructor.
      lia.
    - destruct lo.
      + apply zero.
      + specialize (IHhi lo).
        apply succ in IHhi.
        rewrite seq_shift in IHhi.
        assumption.
  Qed.
End Range.

From Stdlib Require Import Lia.
Section Defs.
  Variable tid: nat.
  Inductive t : range ->  list range -> nat -> nat -> list nat -> Prop :=
  | base:
    forall r lo hi,
    R.Start.t tid r lo ->
    R.End.t tid r hi ->
    lo >= hi ->
    t r [r] lo hi  []
  | step:
    forall r r' l1 l2 lo hi,
    R.Start.t tid r lo ->
    R.End.t tid r hi ->
    lo < hi ->
    R.Step.t tid r lo r' ->
    t r' l1 (S lo) hi l2 ->
    t r (r::l1) lo hi (lo::l2).

  Lemma to_range:
    forall lo hi r l1 l2,
    t r l1 lo hi l2 ->
    Range.t lo hi l2.
  Proof.
    intros lo hi r l1 l2 H.
    induction H.
    - constructor.
      assumption.
    - constructor.
      all: assumption.
  Qed.

  Lemma from_range:
    forall lo hi l2,
    Range.t lo hi l2 ->
    forall r,
    R.Start.t tid r lo ->
    R.End.t tid r hi ->
    exists l1,
    t r l1 lo hi l2.
  Proof.
    intros lo hi l2 H.
    induction H.
    all: intros r Hs He.
    - exists [r].
      constructor.
      all: auto.
    - assert (Hx: Step.t tid r lo (NNum (S lo), NNum hi)). {
        destruct r as (e1, e2).
        econstructor.
        - invc Hs.
          assumption.
        - invc He.
          apply H5.
        - constructor.
        - constructor.
        - assumption.
      }
      specialize (IHt (NNum (S lo), NNum hi)).
      assert (Ha: Start.t tid (NNum (S lo), NNum hi) (S lo)). {
        econstructor.
        all: eauto using n_step_num.
      }
      assert (Hb: End.t tid (NNum (S lo), NNum hi) hi ). {
        econstructor.
        all: eauto using n_step_num.
      }
      specialize (IHt Ha Hb).
      destruct IHt as (l', IHt).
      eexists.
      econstructor.
      all: eauto.
  Qed.

  Lemma from_closed:
    forall r,
    R.Closed.t r ->
    exists l lo hi,
    t r l lo hi (f lo hi).
  Proof.
    intros r H.
    assert (Hs: exists lo, Start.t tid r lo) by eauto using Start.from_closed.
    assert (He: exists lo, End.t tid r lo) by eauto using End.from_closed.
    destruct Hs as (lo, Hlo).
    destruct He as (hi, Hhi).
    assert (Hx := Range.make lo hi).
    eapply from_range in Hx; eauto.
    destruct Hx as (l1, Ht).
    eauto.
  Qed.
End Defs.