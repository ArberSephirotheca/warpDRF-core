Require N.WellTyped.
From Faial.Approx Require Import BExp.
From Faial.Core Require Import Var.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import InUtil.
Require B.MultiSubst.
Require Import B.Equal.
Import ListNotations.

  Inductive t (env: list var) : bexp -> Prop :=
  | bool:
    forall b,
    t env (BBool b)
  | n_rel:
    forall e1 e2 o,
    N.WellTyped.t env e1 ->
    N.WellTyped.t env e2 ->
    t env (NRel o e1 e2)
  | b_rel:
    forall e1 e2 o,
    t env e1 ->
    t env e2 ->
    t env (BRel o e1 e2)
  | not:
    forall e,
    t env e ->
    t env (BNot e).

  Lemma subst:
    forall env e,
    t env e ->
    forall x n,
    t env (b_subst x (NNum n) e).
  Proof.
    induction e; intros.
    all: simpl.
    all: try invc H.
    all: constructor.
    all: auto using N.WellTyped.subst.
  Qed.

  Lemma to_not_free:
    forall x env,
    ~ In x env ->
    forall e,
    t env e ->
    ~ BFree x e.
  Proof.
    induction e.
    all: intros wt.
    all: simpl.
    all: try (intuition; fail).
    all: invc wt.
    - intuition.
      all: contradict H1.
      all: eauto using N.WellTyped.to_not_free.
    - intuition.
    - intuition.
  Qed.

  Lemma strengthen:
    forall x env e,
    ~ BFree x e ->
    t (x :: env) e ->
    t env e.
  Proof.
    induction e.
    all: intros nf wt.
    all: simpl in nf.
    all: invc wt.
    all: constructor.
    all: eauto using N.WellTyped.strengthen.
  Qed.

  Lemma reorder:
    forall e env1 env2,
    SetEq.t env1 env2 ->
    t env1 e ->
    t env2 e.
  Proof.
    induction e.
    all: intros x y env wt.
    all: invc wt.
    all: constructor.
    all: eauto using N.WellTyped.reorder.
  Qed.

  Lemma free_1:
    forall env e,
    t env e ->
    forall x,
    BFree x e ->
    List.In x env.
  Proof.
    intros env e H.
    induction H.
    all: intros y Hf.
    all: simpl in Hf.
    all: intuition.
    all: eauto using N.WellTyped.free_1.
  Qed.

  Lemma subst_strengthen:
    forall x env e,
    t (x :: env) e ->
    forall n,
    t env (b_subst x (NNum n) e).
  Proof.
    intros.
    apply strengthen with (x:=x).
    - apply BExp.not_free_after_subst.
      apply n_free_num.
    - apply subst.
      assumption.
  Qed.

  Lemma multi_subst_to_equal tid:
    forall e env,
    t env e ->
    forall m1 m2,
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    B.Equal.t tid (MultiSubst.f m1 e) (MultiSubst.f m2 e).
  Proof.
    intros e env H.
    induction H.
    all: intros m1 m2 S.
    all: simpl.
    - reflexivity.
    - assert (eq1: N.Equal.t tid (N.MultiSubst.f m1 e1) (N.MultiSubst.f m2 e1)). {
        eauto using N.WellTyped.multi_subst_to_equal.
      }
      assert (eq2: N.Equal.t tid (N.MultiSubst.f m1 e2) (N.MultiSubst.f m2 e2)). {
        eauto using N.WellTyped.multi_subst_to_equal.
      }
      rewrite eq1.
      rewrite eq2.
      reflexivity.
    - rewrite IHt1; auto.
      rewrite IHt2; auto.
      reflexivity.
    - rewrite IHt; eauto.
      reflexivity.
  Qed.

  Lemma progress:
    forall e,
    t [] e ->
    forall tid,
    exists b, BStep tid e b.
  Proof.
    induction e; intros.
    all: invc H.
    - exists b.
      constructor.
    - destruct (N.WellTyped.progress _ H2 tid) as (i1, Hn1).
      destruct (N.WellTyped.progress _ H4 tid) as (i2, Hn2).
      eexists.
      constructor; eauto.
    - destruct IHe1 with (tid:=tid) as (b1, Hb1). { assumption. }
      destruct IHe2 with (tid:=tid) as (b2, Hb2). { assumption. }
      eexists.
      constructor.
      all: eauto.
    - destruct IHe with (tid:=tid) as (b1, Hb1). { assumption. }
      eexists.
      constructor.
      eauto.
  Qed.

  Lemma multisubst:
    forall env n,
    t env n ->
    forall m,
    (forall x, In x env <-> Map_VAR.In x m) ->
    t [] (B.MultiSubst.f m n).
  Proof.
    intros env n H.
    induction H.
    all: intros m spec.
    all: simpl.
    all: constructor.
    all: eauto using N.WellTyped.multisubst.
  Qed.
(*
  Lemma multi_subst_fun tid:
    forall e env,
    t env e ->
    forall m1 v1,
    BStep tid (MultiSubst.f m1 e) v1 ->
    forall m2 v2,
    BStep tid (MultiSubst.f m2 e) v2 ->
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    v1 = v2.
  Proof.
    induction e.
    all: intros env wt m1 v1 r1 m2 v2 r2 S.
    all: simpl in *.
    all: invc r1.
    all: invc r2.
    all: invc wt.
    - reflexivity.
    - f_equal.
      + apply N.WellTyped.multi_subst_fun
          with (tid:=tid) (e:=n0) (env:=env) (m1:=m1) (m2:=m2); eauto.
      + apply N.WellTyped.multi_subst_fun
          with (tid:=tid) (e:=n1) (env:=env) (m1:=m1) (m2:=m2); eauto.
  - f_equal.
    all: eauto.
  - f_equal.
    eauto.
  Qed.*)