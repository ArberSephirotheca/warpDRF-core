Require Trace.
Require Import AExp.
Require D.LRun.
From Stdlib Require Import Logic.Classical.

Inductive t : D.Lang.t -> access_val * Trace.t -> Prop :=
  def:
    forall base tid M1 M2 h l a s,
    D.LRun.t tid base M1 s h M2 l ->
    av_owner a = tid ->
    t s (a, l).

Lemma dec:
  forall s r,
  t s r \/ ~ t s r.
Proof.
  intros.
  apply (classic (t s r)). 
Qed.