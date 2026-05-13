From Faial.Core Require Import Var.
Require Import Dependency.

Section Dom.
  Definition t (keys: list var) (m: Map_VAR.t Dependency.t) : Prop :=
    forall k, List.In k keys <-> Map_VAR.In k m.

  Lemma add:
    forall dom G,
    t dom G ->
    forall x s,
    t (x :: dom) (Map_VAR.add x s G).
  Proof.
    unfold t.
    intros.
    simpl.
    rewrite H.
    rewrite Map_VAR_Facts.add_in_iff.
    intuition.
  Qed.
End Dom.