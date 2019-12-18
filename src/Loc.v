Require Coq.Arith.Compare_dec.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Omega.

Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Inductive loc := location : nat -> loc.

Definition loc_nat r := match r with | location n => n end.

Definition loc_first := location 0.

Definition loc_next m := location (S (loc_nat m)).

Module LOC <: UsualOrderedType.
  Definition t := loc.
  Definition eq := @eq loc.
  Definition lt x y := lt (loc_nat x) (loc_nat y).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z.
    simpl in *.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x <> y.
  Proof.
    unfold lt in *.
    intros.
    destruct x, y.
    simpl in *.
    unfold not; intros.
    inversion H0.
    subst.
    apply Lt.lt_irrefl in H.
    inversion H.
  Qed.

  Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt Logic.eq x y.
  Proof.
    intros.
    destruct x, y.
    destruct (Nat_as_OT.compare n n0);
    eauto using LT, GT.
    apply EQ.
    unfold Nat_as_OT.eq in *.
    subst.
    intuition.
  Defined.

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros.
    unfold eq.
    destruct x, y.
    destruct (eq_nat_dec n n0).
    - subst; eauto.
    - right.
      unfold not.
      intros.
      contradiction n1.
      inversion H; auto.
  Defined.
End LOC.


Module Map_LOC := FMapAVL.Make LOC.
Module Map_LOC_Facts := FMapFacts.Facts Map_LOC.
Module Map_LOC_Props := FMapFacts.Properties Map_LOC.
Module Map_LOC_Extra := MapUtil Map_LOC.
Module Set_LOC := FSetAVL.Make LOC.
Definition set_loc := Set_LOC.t.
Lemma loc_eq_rw:
  forall (k k':loc), LOC.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Section NotIn.
  Variable elt:Type.

  Let lt_irrefl:
    forall x : loc, ~ LOC.lt x x.
  Proof.
    unfold not; intros.
    apply LOC.lt_not_eq in H.
    contradiction H.
    apply LOC.eq_refl.
  Qed.

  Let lt_next:
    forall x, LOC.lt x (loc_next x).
  Proof.
    intros.
    destruct x.
    unfold loc_next, loc_nat, LOC.lt.
    simpl.
    auto.
  Qed.

  Let loc_impl_eq:
    forall k k' : loc, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @Map_LOC_Extra.supremum elt loc_first loc_next LOC.lt LOC.compare.

  Theorem find_not_in:
    forall (m: Map_LOC.t elt),
    ~ Map_LOC.In (supremum m) m.
  Proof.
    intros.
    eauto using Map_LOC_Extra.find_not_in, LOC.lt_trans.
  Qed.

End NotIn.