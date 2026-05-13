From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import Lists.List.
Set Implicit Arguments.

Section ListEq.
  Variable A:Type.
  Variable a_eq: A -> A -> Prop.
  Fixpoint list_eq (l1:list A) (l2:list A) :=
  match l1, l2 with
  | nil, nil => True
  | nil, _
  | _, nil => False
  | cons x l1, cons y l2 => a_eq x y /\ list_eq l1 l2
  end.
End ListEq.

Module ListOrderedType(OT:OrderedType) <: OrderedType.
  Module MO := OrderedTypeFacts(OT).
  Definition t := list OT.t.

  Definition eq := @list_eq OT.t OT.eq.

  Definition eq_dec: forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    induction x; intros. {
      destruct y. {
        left; simpl; auto.
      }
      right; simpl; intros N; inversion N.
    }
    destruct y. {
      right; simpl; intros N; inversion N.
    }
    destruct (IHx y). {
      destruct (OT.eq_dec a t0). {
        left.
        simpl; auto.
      }
      right.
      intros N.
      simpl in *.
      destruct N.
      contradiction.
    }
    right.
    intros N.
    simpl in *.
    destruct N.
    contradiction.
  Defined.

  Lemma eq_refl: forall x: t, eq x x.
  Proof.
    induction x; simpl; auto using OT.eq_refl.
  Qed.

  Lemma eq_sym: forall x y,
    eq x y -> eq y x.
  Proof.
    induction x; intros; simpl in *; destruct y; simpl; auto.
    destruct H.
    eauto using OT.eq_sym.
  Qed.

  Lemma eq_trans: forall x y z:t,
    eq x y -> eq y z -> eq x z.
  Proof.
    intros x y; generalize dependent x.
    induction y; intros. {
      destruct x. {
        auto.
      }
      simpl in *.
      inversion H.
    }
    simpl in *.
    destruct z. {
      inversion H0.
    }
    destruct H0.
    destruct x. {
      inversion H.
    }
    simpl in *.
    destruct H.
    eauto using OT.eq_trans.
  Qed.

  Fixpoint lt (l1 l2: list OT.t) : Prop :=
  match l1, l2 with
  | _, nil => False
  | nil, cons _ _ => True
  | cons x l1, cons y l2 => OT.lt x y \/ (OT.eq x y /\ lt l1 l2)
  end.

  Lemma lt_r_nil:
    forall s,
    ~ lt s nil.
  Proof.
    intros [] N; simpl in *; auto.
  Qed.

  Lemma lt_trans:
    forall l1 l2 l3,
    lt l1 l2 ->
    lt l2 l3 ->
    lt l1 l3.
  Proof.
    intros l1 l2.
    generalize dependent l1.
    induction l2; intros. {
      apply lt_r_nil in H.
      inversion H.
    }
    destruct l1, l2.
    - destruct l3.
      + inversion H0.
      + trivial.
    - destruct l3.
      + inversion H0.
      + trivial.
    - destruct l3.
      + inversion H0.
      + simpl in *.
        intuition.
        * eauto using OT.lt_trans.
        * subst.
          destruct l3; inversion H2.
          left.
          eauto using MO.lt_eq.
        * apply lt_r_nil in H2.
          inversion H2.
        * subst; destruct l3; inversion H3.
          apply lt_r_nil in H2; inversion H2.
    - destruct l3. {
        apply lt_r_nil in H0.
        inversion H0.
      }
      simpl in *.
      intuition.
      + eauto using OT.lt_trans.
      + subst.
        destruct l3.
        * inversion H2.
        * eauto using MO.lt_eq.
      + left.
        apply MO.eq_lt with (y:=a); auto.
      + subst; destruct l3; intuition.
        * right.
          split; eauto using OT.eq_trans.
        * right.
          split; eauto using OT.eq_trans.
  Qed.

  Lemma lt_not_eq:
    forall x y, lt x y -> ~ eq x y.
  Proof.
    induction x; intros. {
      destruct y. {
        apply lt_r_nil in H.
        inversion H.
      }
      intros N; inversion N.
    }
    destruct y. {
      apply lt_r_nil in H.
      inversion H.
    }
    simpl in H.
    intuition. {
      inversion H0; subst; clear H0.
      apply OT.lt_not_eq in H1.
      contradiction.
    }
    inversion H0; subst; clear H0.
    apply IHx in H2; auto.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    induction x; intros. {
      destruct y. {
        apply EQ; auto using eq_refl.
      }
      apply LT.
      simpl; trivial.
    }
    destruct y. {
      apply GT.
      simpl; auto.
    }
    destruct (OT.compare a t0).
    - apply LT.
      simpl; auto.
    - subst.
      assert (IHx := IHx y).
      inversion IHx; subst; clear IHx.
      + apply LT.
        simpl.
        auto.
      + apply EQ.
        simpl.
        auto.
      + apply GT.
        simpl.
        auto using OT.eq_sym.
    - apply GT; simpl; auto.
  Defined.
End ListOrderedType.

Section Bit.
  Inductive bit_lt: bool -> bool -> Prop :=
  | bit_lt_def: bit_lt false true.

  Lemma bit_lt_trans:
    forall x y z,
    bit_lt x y -> bit_lt y z -> bit_lt x z.
  Proof.
    intros.
    inversion H; subst; inversion H0.
  Qed.

  Lemma bit_lt_irrefl:
    forall x y,
    bit_lt x y -> x <> y.
  Proof.
    intros.
    intros N.
    subst.
    inversion H.
  Qed.

  Lemma bit_lt_compare:
    forall x y,
    Compare bit_lt eq x y.
  Proof.
    intros.
    destruct x. {
      destruct y. {
        apply EQ.
        trivial.
      }
      apply GT.
      apply bit_lt_def.
    }
    destruct y. {
      apply LT, bit_lt_def.
    }
    apply EQ; reflexivity.
  Qed.
End Bit.

Module Bit_OT <: UsualOrderedType.
  Definition t := bool.
  Definition eq := @eq t.
  Definition lt : t -> t -> Prop := bit_lt.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition lt_trans := bit_lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := bit_lt_irrefl.
  Definition compare : forall x y : t, Compare lt eq x y := bit_lt_compare.
  Definition eq_dec := Bool.bool_dec.
End Bit_OT.

Section Ascii.
  Definition as_bools (a: ascii): list bool :=
  match a with
  | Ascii x1 x2 x3 x4 x5 x6 x7 x8 => x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: nil
  end.
  Lemma as_bools_ext:
    forall x y,
    as_bools x = as_bools y ->
    x = y.
  Proof.
    intros.
    destruct x, y; simpl in *.
    inversion H; subst; clear H.
    trivial.
  Qed.
End Ascii.

Module Ascii_OT <: UsualOrderedType.
  Module LOT := ListOrderedType Bit_OT.

  Definition t := ascii.
  Definition eq := @eq t.
  Definition lt x y : Prop := LOT.lt (as_bools x) (as_bools y).
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Lemma lt_trans: forall x y z: t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    intros.
    eauto using LOT.lt_trans.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply LOT.lt_not_eq in H.
    intros N; inversion N; subst.
    contradict H.
    apply LOT.eq_refl.
  Qed.

  Lemma lot_eq_ext:
    forall x y,
    LOT.eq x y ->
    x = y.
  Proof.
    induction x; intros; destruct y; auto; inversion H; subst; clear H.
    apply IHx in H1.
    subst.
    trivial.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (LOT.compare (as_bools x) (as_bools y)); auto using LT, GT.
    apply EQ.
    apply lot_eq_ext, as_bools_ext in e.
    subst.
    apply eq_refl.
  Defined.

  Definition eq_dec: forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq; intros.
    destruct (LOT.eq_dec (as_bools x) (as_bools y)). {
      left; apply lot_eq_ext, as_bools_ext in e.
      auto.
    }
    right.
    intros N.
    subst.
    contradict n.
    auto using LOT.eq_refl.
  Defined.
End Ascii_OT.

Section String.
  Fixpoint string_to_list (s:string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s => cons c (string_to_list s)
  end.

  Lemma string_to_list_ext:
    forall x y,
    string_to_list x = string_to_list y ->
    x = y.
  Proof.
    induction x; intros. {
      destruct y. {
        trivial.
      }
      inversion H.
    }
    destruct y. {
      inversion H.
    }
    inversion H.
    subst.
    apply IHx in H2.
    subst.
    reflexivity.
  Qed.

End String.

Module String_OT <: UsualOrderedType.
  Module LOT := ListOrderedType Ascii_OT.

  Definition t := string.
  Definition eq := @eq t.

  Definition lt (x y : t): Prop := LOT.lt (string_to_list x) (string_to_list y).
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Lemma lot_eq_ext:
    forall x y,
    LOT.eq x y ->
    x = y.
  Proof.
    induction x; intros; destruct y; auto; inversion H; subst; clear H.
    apply IHx in H1.
    subst.
    trivial.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    eauto using LOT.lt_trans.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply LOT.lt_not_eq in H.
    intros N; subst.
    contradict H.
    auto using LOT.eq_refl.
  Qed.
  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    destruct (LOT.compare (string_to_list x) (string_to_list y)); auto using LT, GT.
    apply EQ.
    apply lot_eq_ext, string_to_list_ext in e.
    subst.
    apply eq_refl.
  Defined.
  Definition eq_dec := string_dec.
End String_OT.

