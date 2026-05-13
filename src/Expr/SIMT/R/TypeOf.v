Require Import Dependency.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.N.TypeOf.
From Faial.Core Require Import Tictac.
From Faial.Expr Require SIMT.R.WellTyped.
From Faial.Expr Require SIMT.N.WellTyped.
From Faial.Expr Require SIMT.N.TypeOf.
Require Map.Dom.
Require Map.Ind.

Section RTypeOf.
  Import Dependency.
  Inductive t (G:Env.t) : range -> Dependency.t -> Prop :=
  | def:
    forall n1 n2 d1 d2,
    N.TypeOf.t G n1 d1 ->
    N.TypeOf.t G n2 d2 ->
    t G (n1, n2) (merge d1 d2).

  Lemma def_ind:
    forall G n1 n2,
    N.TypeOf.t G n1 Independent ->
    N.TypeOf.t G n2 Independent ->
    t G (n1, n2) Independent.
  Proof.
    intros.
    assert (r1: Independent = merge Independent Independent) by auto.
    rewrite r1.
    constructor; auto.
  Qed.

  Lemma subst_num:
    forall G e d1,
    t G e d1 ->
    forall x k,
    exists d2,
    Le.t d2 d1 /\ t G (r_subst x (NNum k) e) d2.
  Proof.
    intros.
    invc H.
    assert (Hx := N.TypeOf.subst_num _ _ _ H0 x k).
    destruct Hx as (dx, (Hle1, Ht1)).
    assert (Hy := N.TypeOf.subst_num _ _ _ H1 x k).
    destruct Hy as (dy, (Hle2, Ht2)).
    exists (merge dx dy).
    split. {
      eauto using Le.merge.
    }
    constructor; auto.
  Qed.

  Lemma subst_num_independent:
    forall G e,
    t G e Independent ->
    forall x k,
    t G (r_subst x (NNum k) e) Independent.
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
    R.WellTyped.t env e ->
    forall G,
    Ind.t env G ->
    t G e Independent.
  Proof.
    intros.
    invc H.
    assert (w1: N.TypeOf.t G e1 Independent) by eauto using N.TypeOf.from_ind.
    assert (w2: N.TypeOf.t G e2 Independent) by eauto using N.TypeOf.from_ind.
    auto using def_ind.
  Qed.

  Lemma from_dom:
    forall env e,
    R.WellTyped.t env e ->
    forall G,
    Dom.t env G ->
    exists d, t G e d.
  Proof.
    intros.
    invc H.
    assert (w1: exists d, N.TypeOf.t G e1 d) by eauto using N.TypeOf.from_dom.
    assert (w2: exists d, N.TypeOf.t G e2 d) by eauto using N.TypeOf.from_dom.
    destruct w1 as (d1, w1).
    destruct w2 as (d2, w2).
    eexists.
    constructor.
    all: eauto.
  Qed.
End RTypeOf.