Require Import Dependency.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Var.
Require N.WellTyped.
Require Map.Dom.
Require Map.Ind.

Section NTypeOf.
  Import Dependency.
  Inductive t (G:Env.t) : nexp -> Dependency.t -> Prop :=
  | var:
    forall x d,
    Map_VAR.MapsTo x d G ->
    t G (NVar x) d
  | tid:
    t G NTid Independent
  | num:
    forall n,
    t G (NNum n) Independent
  | bin:
    forall o e1 e2 d1 d2,
    t G e1 d1 ->
    t G e2 d2 ->
    t G (NBin o e1 e2) (Dependency.merge d1 d2)
  .

  Lemma subst_num:
    forall G e d1,
    t G e d1 ->
    forall x k,
    exists d2,
    Le.t d2 d1 /\ t G (n_subst x (NNum k) e) d2.
  Proof.
    intros G e d1 H.
    induction H.
    all: intros y k.
    all: simpl.
    - destruct (Set_VAR.MF.eq_dec y x). {
        exists Independent.
        subst.
        split; constructor.
      }
      exists d.
      split; constructor.
      assumption.
    - exists Independent.
      split; constructor.
    - exists Independent.
      split; constructor.
    - specialize IHt1 with (x:=y) (k:=k).
      specialize IHt2 with (x:=y) (k:=k).
      destruct IHt1 as (d3, (Hle3, Ht3)).
      destruct IHt2 as (d4, (Hle4, Ht4)).
      exists (merge d3 d4).
      split.
      + auto using Le.merge.
      + constructor; auto.
  Qed.

  Lemma subst_num_independent:
    forall G e,
    t G e Independent ->
    forall x k,
    t G (n_subst x (NNum k) e) Independent.
  Proof.
    intros.
    assert (Hx := subst_num _ _ _ H x k).
    destruct Hx as (?, (Hle, ?)).
    apply Le.inv_independent_r in Hle.
    subst.
    assumption.
  Qed.

  Lemma strengthen:
    forall n d G,
    t G n d ->
    forall G',
    Env.Le.t G' G ->
    exists d',
    Le.t d' d /\
    t G' n d'.
  Proof.
    intros n d G H.
    induction H.
    all: intros G' env_le.
    - apply (Env.Le.inv env_le) in H.
      destruct H as (d', (Hm, Hle)).
      exists d'.
      split; auto.
      constructor.
      assumption.
    - exists Independent.
      split; constructor.
    - exists Independent.
      split; constructor.
    - assert (IHt1 := IHt1 G' env_le).
      assert (IHt2 := IHt2 G' env_le).
      destruct IHt1 as (d1', (Hle1, Ht1)).
      destruct IHt2 as (d2', (Hle2, Ht2)).
      exists (merge d1' d2').
      split. {
        apply Le.merge; auto.
      }
      constructor; auto.
  Qed.

  Lemma add_strengthen:
    forall n x d1 d2 G,
    t (Map_VAR.add x d1 G) n d2 ->
    forall d1',
    Le.t d1' d1 ->
    exists d2',
    Le.t d2' d2 /\
    t (Map_VAR.add x d1' G) n d2'.
  Proof.
    intros.
    apply strengthen with (G:=Map_VAR.add x d1 G);
      auto using Env.Le.add_1.
  Qed.

  Lemma add_strengthen_independent:
    forall n x d G,
    t (Map_VAR.add x d G) n Independent ->
    forall d',
    Le.t d' d ->
    t (Map_VAR.add x d' G) n Independent.
  Proof.
    intros.
    apply add_strengthen with (d1':=d') in H; auto.
    destruct H as (d2, (Hle, Ht)).
    assert (d2 = Independent) by eauto using Le.inv_independent_r.
    subst.
    assumption.
  Qed.

  Lemma from_ind:
    forall env e,
    N.WellTyped.t env e ->
    forall G,
    Ind.t env G ->
    t G e Independent.
  Proof.
    intros env e H.
    induction H.
    all: intros G Hdom.
    - constructor.
    - constructor.
    - apply Hdom in H.
      constructor.
      assumption.
    - specialize (IHt1 G Hdom).
      specialize (IHt2 G Hdom).
      assert (r1: Independent = merge Independent Independent) by reflexivity.
      rewrite r1.
      constructor.
      all: auto.
  Qed.

  Lemma from_dom:
    forall env e,
    N.WellTyped.t env e ->
    forall G,
    Dom.t env G ->
    exists d, t G e d.
  Proof.
    intros env e H.
    induction H.
    all: intros G Hdom.
    - eexists.
      constructor.
    - eexists.
      constructor.
    - apply Hdom in H.
      apply Map_VAR_Extra.in_to_mapsto in H.
      destruct H as (d, H).
      exists d.
      constructor.
      assumption.
    - specialize (IHt1 G Hdom).
      specialize (IHt2 G Hdom).
      destruct IHt1 as (d1, Ht1).
      destruct IHt2 as (d2, Ht2).
      eexists.
      constructor.
      all: eauto.
  Qed.
End NTypeOf.

