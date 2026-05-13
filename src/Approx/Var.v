From Stdlib Require Arith.Compare_dec.

From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FSetAVL.
From Stdlib Require Import Arith.Peano_dec.
From Stdlib Require Import Strings.String.

Require Import Aniceto.Map.

From Faial.Approx Require Import StringUtil.

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

Lemma find_add_1:
  forall {A:Type} x (v:A) m,
  Map_VAR.find x (Map_VAR.add x v m) = Some v.
Proof.
  intros.
  apply Map_VAR.find_1.
  auto using Map_VAR.add_1.
Qed.

Lemma not_in_to_find_none {elt:Type}:
  forall x m,
  ~ Map_VAR.In x m ->
  Map_VAR.find (elt:=elt) x m = None.
Proof.
  intros.
  destruct (Map_VAR.find x m) eqn:eq1. {
    apply Map_VAR.find_2 in eq1.
    contradict H.
    exists e.
    assumption.
  }
  reflexivity.
Qed.

Lemma find_none_to_not_in {elt:Type}:
  forall x m,
  Map_VAR.find (elt:=elt) x m = None ->
  ~ Map_VAR.In x m.
Proof.
  intros.
  intros N.
  apply Map_VAR_Extra.in_to_mapsto in N.
  destruct N as (e, M).
  apply Map_VAR.find_1 in M.
  rewrite H in *.
  inversion M.
Qed.

Lemma find_add_2:
  forall {A:Type} x y (v:A) m,
  x <> y ->
  Map_VAR.find x (Map_VAR.add y v m) = Map_VAR.find x m.
Proof.
  intros.
  destruct (Map_VAR.find x m) eqn:eq1. {
    apply Map_VAR.find_1.
    apply Map_VAR.add_2.
    all: eauto using Map_VAR.find_2.
  }
  apply not_in_to_find_none.
  intros N.
  apply Map_VAR_Extra.in_to_mapsto in N.
  destruct N as (e, N).
  apply Map_VAR.add_3 in N; auto.
  apply Map_VAR.find_1 in N.
  rewrite N in *.
  inversion eq1.
Qed.

Lemma rw_remove_add_eq {elt:Type}:
  forall k v m,
  Map_VAR.Equal (Map_VAR.remove (elt:=elt) k (Map_VAR.add k v m)) (Map_VAR.remove (elt:=elt) k m).
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros k1 v1.
  split.
  all: intros Hm.
  - rewrite Map_VAR_Facts.remove_mapsto_iff in *.
    intuition.
    eauto using Map_VAR.add_3.
  - rewrite Map_VAR_Facts.remove_mapsto_iff in *.
    intuition.
    auto using Map_VAR.add_2.
Qed.

Lemma rw_add_remove_eq {elt:Type}:
  forall k v m,
  Map_VAR.Equal (Map_VAR.add k v (Map_VAR.remove (elt:=elt) k m)) (Map_VAR.add k v m).
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros k1 v1.
  split.
  all: intros Hm.
  - destruct (VAR.eq_dec k1 k). {
      subst.
      assert (v1 = v). {
        eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1.
      }
      subst.
      auto using Map_VAR.add_1.
    }
    apply Map_VAR.add_3 in Hm; auto.
    apply Map_VAR.remove_3 in Hm.
    eauto using Map_VAR.add_2.
  - destruct (VAR.eq_dec k1 k). {
      subst.
      assert (v1 = v). {
        eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1.
      }
      subst.
      auto using Map_VAR.add_1.
    }
    apply Map_VAR.add_3 in Hm; auto.
    apply Map_VAR.add_2; auto.
    apply Map_VAR.remove_2; auto.
Qed.

Lemma rw_add_remove_neq {elt:Type}:
  forall x y v m,
  x <> y ->
  Map_VAR.Equal
    (Map_VAR.add x v (Map_VAR.remove (elt:=elt) y m))
    (Map_VAR.remove (elt:=elt) y (Map_VAR.add x v m)).
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros k1 v1.
  split.
  all: intros Ha.
  - destruct (Set_VAR.MF.eq_dec k1 x). {
      destruct (Set_VAR.MF.eq_dec k1 y). {
        subst.
        contradiction.
      }
      subst.
      assert (v1 = v). {
        eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1.
      }
      subst.
      apply Map_VAR.remove_2.
      all: auto using Map_VAR.add_1.
    }
    destruct (Set_VAR.MF.eq_dec k1 y). {
      subst.
      apply Map_VAR.add_3 in Ha; auto.
      apply Map_VAR_Extra.mapsto_to_in in Ha.
      apply Map_VAR.remove_1 in Ha.
      all: intuition.
    }
    apply Map_VAR.add_3 in Ha; auto.
    apply Map_VAR.remove_3 in Ha.
    apply Map_VAR.remove_2; auto.
    auto using Map_VAR.add_2.
  - destruct (Set_VAR.MF.eq_dec k1 x). {
      destruct (Set_VAR.MF.eq_dec k1 y). {
        subst.
        apply Map_VAR.remove_3 in Ha.
        assert (v1 = v). {
          eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1.
        }
        subst.
        auto using Map_VAR.add_1.
      }
      subst.
      assert (v1 = v). {
        eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1, Map_VAR.remove_2.
      }
      subst.
      auto using Map_VAR.add_1.
    }
    destruct (Set_VAR.MF.eq_dec k1 y). {
      subst.
      apply Map_VAR_Extra.mapsto_to_in in Ha.
      apply Map_VAR.remove_1 in Ha; intuition.
    }
    apply Map_VAR.remove_3 in Ha.
    apply Map_VAR.add_3 in Ha; auto.
    apply Map_VAR.add_2; auto.
    apply Map_VAR.remove_2; auto.
Qed.

Lemma rw_remove_empty {elt:Type}:
  forall x,
  Map_VAR.Equal (Map_VAR.remove (elt:=elt) x (Map_VAR.empty elt)) (Map_VAR.empty elt).
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros.
  split.
  all: intros ha.
  - apply Map_VAR.remove_3 in ha.
    assumption.
  - rewrite Map_VAR_Facts.empty_mapsto_iff in ha.
    contradiction.
Qed.

Lemma empty_to_not_in {elt:Type}:
  forall m,
  Map_VAR.Empty (elt:=elt) m ->
  forall x,
  ~ Map_VAR.In x m.
Proof.
  intros.
  intros N.
  apply Map_VAR_Extra.in_to_mapsto in N.
  destruct N as (e, mt).
  apply Map_VAR_Extra.empty_to_mapsto in mt; auto.
Qed.

Lemma not_in_to_empty {elt:Type}:
  forall m,
  (forall x, ~ Map_VAR.In x m) ->
  Map_VAR.Empty (elt:=elt) m.
Proof.
  intros.
  assert (is_a: Map_VAR.Equal m (Map_VAR.empty elt)). {
    rewrite Map_VAR_Facts.Equal_mapsto_iff.
    intros.
    split.
    all: intros ha.
    all: apply Map_VAR_Extra.mapsto_to_in in ha.
    - apply H in ha.
      contradiction.
    - apply Map_VAR_Facts.empty_in_iff in ha.
      contradiction.
  }
  assert (Ha := Map_VAR_Facts.Empty_m is_a).
  rewrite Ha.
  auto using Map_VAR.empty_1.
Qed.

Lemma rw_empty_not_in {elt:Type}:
  forall m,
  (forall x, ~ Map_VAR.In x m) <->
  Map_VAR.Empty (elt:=elt) m.
Proof.
  intros m.
  split; auto using not_in_to_empty, empty_to_not_in.
Qed.

Lemma equal_empty_empty {elt:Type}:
  forall m1,
  Map_VAR.Empty (elt:=elt) m1 ->
  forall m2,
  Map_VAR.Empty (elt:=elt) m2 ->
  Map_VAR.Equal m1 m2.
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros.
  split.
  all: intros ha.
  all: apply Map_VAR_Extra.empty_to_mapsto in ha; auto.
  all: contradiction.
Qed.

Lemma rw_remove_is_empty {elt:Type}:
  forall m,
  Map_VAR.Empty m ->
  forall x,
  Map_VAR.Equal (Map_VAR.remove (elt:=elt) x m) m.
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros.
  split.
  all: intros ha.
  - apply Map_VAR.remove_3 in ha.
    assumption.
  - apply Map_VAR_Extra.empty_to_mapsto in ha; auto.
    contradiction.
Qed.

Lemma empty_to_empty_remove {elt:Type}:
  forall x m,
  Map_VAR.Empty (elt:=elt) m -> Map_VAR.Empty (elt:=elt) (Map_VAR.remove (elt:=elt) x m).
Proof.
  intros.
  assert (rw1:= rw_remove_is_empty m H).
  rewrite rw1.
  assumption.
Qed.

Lemma rw_remove_remove_eq {elt:Type}:
  forall x m,
  Map_VAR.Equal (Map_VAR.remove x (Map_VAR.remove (elt:=elt) x m)) (Map_VAR.remove (elt:=elt) x m).
Proof.
  intros.
  rewrite Map_VAR_Facts.Equal_mapsto_iff.
  intros k e.
  split.
  all: intros ha.
  all: destruct (VAR.eq_dec k x).
  - subst.
    apply Map_VAR_Extra.mapsto_to_in in ha.
    apply Map_VAR.remove_1 in ha.
    all: intuition.
  - apply Map_VAR.remove_3 in ha; auto.
  - subst.
    apply Map_VAR_Extra.mapsto_to_in in ha.
    apply Map_VAR.remove_1 in ha.
    all: intuition.
  - apply Map_VAR.remove_2; auto.
Qed.

Lemma not_in_remove {elt:Type}:
  forall x m,
  ~ Map_VAR.In (elt:=elt) x (Map_VAR.remove (elt:=elt) x m).
Proof.
  intros.
  intros N.
  apply Map_VAR.remove_1 in N; auto.
Qed.

Lemma in_add_1:
  forall (elt : Type) (m : Map_VAR.t elt) (x : Map_VAR.key) (e : elt),
  Map_VAR.In x (Map_VAR.add x e m).
Proof.
  intros.
  apply Map_VAR_Extra.mapsto_to_in with (e:=e).
  auto using Map_VAR.add_1.
Qed.

Lemma in_add_2:
  forall (elt : Type) (m : Map_VAR.t elt) (x y : Map_VAR.key) (e : elt),
  Map_VAR.In y m ->
  Map_VAR.In y (Map_VAR.add x e m).
Proof.
  intros.
  apply Map_VAR_Extra.in_to_mapsto in H.
  destruct H as (e', Hm).
  destruct (VAR.eq_dec x y). {
    subst.
    auto using in_add_1.
  }
  apply Map_VAR_Extra.mapsto_to_in with (e:=e').
  auto using Map_VAR.add_2.
Qed.

Lemma in_add_3:
  forall (elt : Type) (m : Map_VAR.t elt) (x y : Map_VAR.key) (e : elt),
  x <> y ->
  Map_VAR.In y (Map_VAR.add x e m) ->
  Map_VAR.In y m.
Proof.
  intros.
  apply Map_VAR_Extra.in_to_mapsto in H0.
  destruct H0 as (e', Hm).
  apply Map_VAR_Extra.mapsto_to_in with (e:=e').
  eauto using Map_VAR.add_3.
Qed.

Lemma in_remove_2:
  forall (elt : Type) m x y,
  x <> y ->
  Map_VAR.In y m ->
  Map_VAR.In y (Map_VAR.remove (elt:=elt) x m).
Proof.
  intros.
  apply Map_VAR_Extra.in_to_mapsto in H0.
  destruct H0 as (e, H0).
  eapply Map_VAR_Extra.mapsto_to_in; eauto using Map_VAR.remove_2.
Qed.

Lemma in_remove_3:
  forall (elt : Type) (m : Map_VAR.t elt) (x y : Map_VAR.key),
  Map_VAR.In y (Map_VAR.remove (elt:=elt) x m) ->
  Map_VAR.In y m.
Proof.
  intros.
  apply Map_VAR_Extra.in_to_mapsto in H.
  destruct H as (e, H).
  eapply Map_VAR_Extra.mapsto_to_in; eauto using Map_VAR.remove_3.
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