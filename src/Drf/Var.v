From Stdlib Require Arith.Compare_dec.

From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FSetAVL.
From Stdlib Require Import Arith.Peano_dec.
From Stdlib Require Import Strings.String.

Require Import Aniceto.Map.

From Faial.Core Require Import StringUtil.

From Stdlib Require FSets.FMapFacts.

From Stdlib Require String.

Inductive var := variable : string -> var.

Definition var_str r := match r with | variable n => n end.
(*
Definition var_first := variable 0.

Definition var_next m := variable (S (var_nat m)).
*)

Module VAR <: UsualOrderedType.
  Definition t := var.
  Definition eq := @eq var.
  Definition lt x y := String_OT.lt (var_str x) (var_str y).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z.
    simpl in *.
    eauto using String_OT.lt_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> x <> y.
  Proof.
    unfold lt in *.
    intros.
    unfold not; intros.
    destruct x, y.
    simpl in *.
    inversion H0; subst; clear H0.
    apply String_OT.lt_not_eq in H.
    contradiction H.
    unfold String_OT.eq.
    reflexivity.
  Qed.

  Lemma compare:
    forall x y, Compare lt Logic.eq x y.
  Proof.
    intros.
    destruct x, y.
    assert (Hx := String_OT.compare s s0).
    inversion Hx; subst; clear Hx.
    - apply LT.
      unfold lt; simpl.
      assumption.
    - apply EQ.
      unfold String_OT.eq in *.
      subst.
      reflexivity.
    - apply GT.
      unfold lt.
      auto.
  Defined.

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x, y.
    destruct (String_OT.eq_dec s s0).
    - subst; eauto.
    - right.
      unfold not.
      intros H.
      contradiction n.
      inversion H; auto.
  Defined.
End VAR.


Module Map_VAR := FMapAVL.Make VAR.
Module Map_VAR_Facts := FMapFacts.Facts Map_VAR.
Module Map_VAR_Props := FMapFacts.Properties Map_VAR.
Module Map_VAR_Extra := MapUtil Map_VAR.
Module Set_VAR := FSetAVL.Make VAR.
Definition set_var := Set_VAR.t.
Lemma var_eq_rw:
  forall (k k':var), VAR.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.
(*
Section NotIn.
  Variable elt:Type.

  Let lt_irrefl:
    forall x : var, ~ VAR.lt x x.
  Proof.
    unfold not; intros.
    apply VAR.lt_not_eq in H.
    contradiction H.
    apply VAR.eq_refl.
  Qed.

  Let lt_next:
    forall x, VAR.lt x (var_next x).
  Proof.
    intros.
    destruct x.
    unfold var_next, var_nat, VAR.lt.
    simpl.
    auto.
  Qed.

  Let var_impl_eq:
    forall k k' : var, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @Map_VAR_Extra.supremum elt var_first var_next VAR.lt VAR.compare.

  Theorem find_not_in:
    forall (m: Map_VAR.t elt),
    ~ Map_VAR.In (supremum m) m.
  Proof.
    intros.
    eauto using Map_VAR_Extra.find_not_in, VAR.lt_trans.
  Qed.
End NotIn.
*)