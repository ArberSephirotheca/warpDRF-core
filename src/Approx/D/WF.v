From Faial.Core Require Import Var.
From Faial.Expr Require SIMT.N.WellTyped.
From Faial.Expr Require SIMT.B.WellTyped.
From Faial.Expr Require SIMT.R.WellTyped.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Approx.D Require Import Lang.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import InUtil.
From Faial.Approx.D Require Free.
From Faial.Approx.D Require Bound.
From Faial.Approx.D Require LRun.
From Stdlib Require Import Lists.List.
From Faial.Approx.D Require MultiSubst.
Import ListNotations.

Inductive t : list var -> Lang.t -> Prop :=
| read:
  forall env x e s,
  N.WellTyped.t env e ->
  ~ List.In x env ->
  t (x :: env) s ->
  t env (Read x e s)
| decl:
  forall x s env,
  ~ List.In x env ->
  t (x :: env) s ->
  t env (Decl x s)
| loop:
  forall x r s env,
  R.WellTyped.t env r ->
  t (x :: env) s ->
  ~ List.In x env ->
  t env (Loop x r s)
| write:
  forall env idx e,
  N.WellTyped.t env idx ->
  N.WellTyped.t env e ->
  t env (Write idx e)
| skip:
  forall env,
  t env Skip
| seq:
  forall env s1 s2,
  t env s1 ->
  t env s2 ->
  t env (Seq s1 s2)
| cond:
  forall e s1 s2 env,
  B.WellTyped.t env e ->
  t env s1 ->
  t env s2 ->
  t env (Cond e s1 s2).

Section Defs.
  Lemma subst:
    forall env e,
    t env e ->
    forall x n,
    t env (Subst.f x (NNum n) e).
  Proof.
    intros.
    induction H.
    all: simpl.
    all: constructor.
    all: auto using
      N.WellTyped.subst,
      R.WellTyped.subst,
      B.WellTyped.subst.
    all: destruct (Set_VAR.MF.eq_dec x x0).
    all: subst.
    all: auto.
  Qed.

  Lemma reorder:
    forall e env1,
    t env1 e ->
    forall env2,
    SetEq.t env1 env2 ->
    t env2 e.
  Proof.
    intros e env1 H.
    induction H.
    all: intros env2 eq1.
    all: constructor.
    all: eauto using N.WellTyped.reorder, R.WellTyped.reorder, B.WellTyped.reorder.
    all: auto using SetEq.cons.
    all: intros N.
    all: rename_hyp (~ _) as M.
    all: contradict M.
    all: apply eq1.
    all: assumption.
  Qed.

  Lemma free_1:
    forall env s,
    t env s ->
    forall x,
    Free.t x s ->
    List.In x env.
  Proof.
    intros env s H.
    induction H.
    all: intros y Hf.
    all: simpl in Hf.
    - destruct Hf as [Hf | (?, Hf)]. {
        eauto using N.WellTyped.free_1.
      }
      apply IHt in Hf.
      simpl in *.
      intuition.
      subst.
      contradiction.
    - destruct Hf as (?, Hf).
      apply IHt in Hf.
      destruct Hf as [? | Hf]. { subst. contradiction. }
      assumption.
    - destruct Hf as [Hf|(?,Hf)]. { eauto using R.WellTyped.free_1. }
      apply IHt in Hf.
      destruct Hf as [Hf | Hf]. { subst. contradiction. }
      assumption.
    - destruct Hf as [Hf|Hf].
      all: eauto using N.WellTyped.free_1.
    - contradiction.
    - destruct Hf as [Hf|Hf].
      all: auto.
    - destruct Hf as [Hf|[Hf|Hf]].
      all: eauto using B.WellTyped.free_1.
  Qed.

  Lemma strengthen:
    forall e x env,
    ~ Free.t x e ->
    t (x :: env) e ->
    t env e.
  Proof.
    induction e.
    all: intros x env nin wf.
    all: invc wf.
    all: constructor.
    all: simpl in nin.
    all: intuition.
    all: eauto using
      N.WellTyped.strengthen,
      B.WellTyped.strengthen,
      R.WellTyped.strengthen.
    all: assert (x <> v) by (intros N; subst; intuition).
    all: assert (SetEq.t (v :: x :: env) (x :: v :: env)) by (unfold SetEq.t; simpl; intuition).
    all: apply IHe with (x:=x).
    all: eauto using reorder.
  Qed.

  Lemma subst_strengthen:
    forall s x env,
    t (x :: env) s ->
    forall n,
    t env (Subst.f x (NNum n) s).
  Proof.
    intros.
    apply strengthen with (x:=x).
    - apply Free.not_free_after_subst.
      apply n_free_num.
    - apply subst.
      assumption.
  Qed.

  Lemma bound_not_in_env:
    forall s x,
    Bound.t x s ->
    forall env,
    t env s ->
    ~ List.In x env.
  Proof.
    induction s.
    all: intros x hb env wf N.
    all: invc wf.
    all: simpl in hb.
    all: auto.
    all: intuition.
    all: subst.
    all: eauto using List.in_cons.
  Qed.

  Lemma loop_var_not_bound:
    forall env x r s,
    t env (Loop x r s) ->
    ~ Bound.t x s.
  Proof.
    intros.
    invc H.
    intros N.
    eapply bound_not_in_env in H5; eauto.
    simpl in *.
    intuition.
  Qed.

End Defs.

