
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.

Import ListNotations.

Section Def.
  Set Implicit Arguments.
  Variable action: Type.
  Variable config: Type.
  Variable Step: action -> config -> config -> Prop.
  Inductive t : list action -> config -> config -> Prop :=
  | refl:
    forall C,
    t [] C C
  | step:
    forall a l C1 C2 C3,
    Step a C1 C2 ->
    t l C2 C3 ->
    t (a::l) C1 C3.

  Definition rel C1 C2 := exists l, t l C1 C2.

  Lemma to_clos_refl_trans:
    forall l C1 C2,
    t l C1 C2 ->
    clos_refl_trans _ (fun A B => exists a, Step a A B) C1 C2.
  Proof.
    intros.
    induction H.
    - apply rt_refl.
    - apply rt_trans with (y:=C2).
      + apply rt_step.
        eauto.
      + assumption.
  Qed.

  Lemma from_step:
    forall a C1 C2,
    Step a C1 C2 ->
    t [a] C1 C2.
  Proof.
    intros.
    econstructor. {
      apply H.
    }
    constructor.
  Qed.

  Lemma app:
    forall l1 C1 C2,
    t l1 C1 C2 ->
    forall C3 l2,
    t l2 C2 C3 ->
    t (l1 ++ l2) C1 C3.
  Proof.
    intros l1 C1 C2 H.
    induction H.
    all: intros C4 l2 Hl2.
    - simpl.
      assumption.
    - simpl.
      eapply step.
      + apply H.
      + auto.
  Qed.

  Lemma from_clos_refl_trans:
    forall C1 C2,
    clos_refl_trans _ (fun A B => exists a, Step a A B) C1 C2 ->
    rel C1 C2.
  Proof.
    intros.
    induction H.
    - destruct H as (a, Hs).
      exists [a].
      apply from_step.
      assumption.
    - exists [].
      constructor.
    - destruct IHclos_refl_trans1 as (l1, Hs1).
      destruct IHclos_refl_trans2 as (l2, Hs2).
      exists (l1 ++ l2).
      eapply app; eauto.
  Qed.

  Lemma inv_app:
    forall C1 C3 l1 l2,
    t (l1 ++ l2) C1 C3 ->
    exists C2, t l1 C1 C2  /\ t l2 C2 C3.
  Proof.
  Admitted.

End Def.


