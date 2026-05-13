Require Import Dependency.
Require Import BExp.
Require Import NExp.
Require Import N.TypeOf.
Require Import B.WellTyped.
Require Import Tictac.
Require Map.Dom.
Require Map.Ind.

Section BTypeOf.
  Import Dependency.Dependency.
  Inductive t (G:Env.t) : bexp -> Dependency.t -> Prop :=
  | b_type_of_bool:
    forall b,
    t G (BBool b) Independent
  | b_type_of_nrel:
    forall o n1 n2 d1 d2,
    N.TypeOf.t G n1 d1 ->
    N.TypeOf.t G n2 d2 ->
    t G (NRel o n1 n2) (merge d1 d2)
  | b_type_of_brel:
    forall o b1 b2 d1 d2,
    t G b1 d1 ->
    t G b2 d2 ->
    t G (BRel o b1 b2) (merge d1 d2)
  | b_type_of_not:
    forall b d,
    t G b d ->
    t G (BNot b) d
  .

  Lemma subst_num:
    forall G e d1,
    t G e d1 ->
    forall x k,
    exists d2,
    Le.t d2 d1 /\ t G (b_subst x (NNum k) e) d2.
  Proof.
    intros G e d1 H.
    induction H.
    all: intros vx k.
    all: simpl.
    - exists Independent.
      split; constructor.
    - assert (Hx := N.TypeOf.subst_num _ _ _ H vx k).
      destruct Hx as (d3, (Hle1, Ht1)).
      assert (Hy := N.TypeOf.subst_num _ _ _ H0 vx k).
      destruct Hy as (d4, (Hle2, Ht2)).
      exists (merge d3 d4).
      split. {
        auto using Le.merge.
      }
      constructor; auto.
    - specialize IHt1 with vx k.
      destruct IHt1 as (d3, (Hle1, Ht1)).
      specialize IHt2 with vx k.
      destruct IHt2 as (d4, (Hle2, Ht2)).
      exists (merge d3 d4).
      split. {
        auto using Le.merge.
      }
      constructor; auto.
    - specialize IHt with vx k.
      destruct IHt as (d3, (Hle1, Ht1)).
      exists d3.
      intuition.
      constructor.
      assumption.
  Qed.

  Lemma subst_num_independent:
    forall G e,
    t G e Independent ->
    forall x k,
    t G (b_subst x (NNum k) e) Independent.
  Proof.
    intros.
    assert (Hx := subst_num _ _ _ H x k).
    destruct Hx as (?, (Hle, ?)).
    apply Le.inv_independent_r in Hle.
    subst.
    assumption.
  Qed.

  Lemma from_ind:
    forall env e,
    B.WellTyped.t env e ->
    forall G,
    Ind.t env G ->
    t G e Independent.
  Proof.
    intros env e H.
    induction H.
    all: assert (r1: Independent = merge Independent Independent) by reflexivity.
    all: intros G Hdom.
    - constructor.
    - rewrite r1.
      constructor.
      all: eauto using N.TypeOf.from_ind.
    - specialize (IHt1 G Hdom).
      specialize (IHt2 G Hdom).
      rewrite r1.
      constructor.
      all: auto.
    - constructor.
      auto.
  Qed.

  Lemma from_dom:
    forall env e,
    B.WellTyped.t env e ->
    forall G,
    Dom.t env G ->
    exists d, t G e d.
  Proof.
    intros env e H.
    induction H.
    all: intros G Hdom.
    - eexists.
      constructor.
    - rename_hyp (N.WellTyped.t _ e1) as w1.
      rename_hyp (N.WellTyped.t _ e2) as w2.
      eapply N.TypeOf.from_dom in w1; eauto.
      eapply N.TypeOf.from_dom in w2; eauto.
      destruct w1 as (d1, w1).
      destruct w2 as (d2, w2).
      eexists.
      constructor.
      all: eauto.
    - specialize (IHt1 _ Hdom).
      specialize (IHt2 _ Hdom).
      destruct IHt1 as (d1, Ha).
      destruct IHt2 as (d2, Hb).
      eexists.
      constructor.
      all: eauto.
    - specialize (IHt G Hdom).
      destruct IHt as (d, Ht).
      eexists.
      constructor.
      eauto.
  Qed.
End BTypeOf.