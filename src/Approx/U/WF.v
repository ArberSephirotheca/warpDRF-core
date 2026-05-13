Require Import U.Lang.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import AExp.
From Faial.Core Require Import Var.
Require N.WellTyped.
Require B.WellTyped.
Require R.WellTyped.
Require U.Free.
Require U.Bound.
Require U.Subst.

From Faial.Core Require Import InUtil.
From Faial.Core Require Import Tictac.


Inductive t : list var -> U.Lang.t -> Prop :=
| acc:
  forall env a,
  N.WellTyped.t env (ae_index a) ->
  t env (MemAcc a)
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
  t env (For x r s)
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
  t env (If e s1 s2).
  
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
    { destruct a. simpl in *. auto using N.WellTyped.subst. }
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
    t env (For x r s) ->
    ~ Bound.t x s.
  Proof.
    intros.
    invc H.
    intros N.
    eapply bound_not_in_env in H5; eauto.
    simpl in *.
    intuition.
  Qed.

  Lemma in_env_not_bound:
    forall u env,
    t env u ->
    forall x,
    List.In x env ->
    ~ Bound.t x u.
  Proof.
    induction u.
    all: intros env wt x hi N.
    all: simpl in *.
    all: intuition.
    all: invc wt.
    all: eauto.
    - rename_hyp (Bound.t _ _) as hb.
      contradict hb.
      eauto using bound_not_in_env, List.in_cons.
    - rename_hyp (Bound.t _ _) as hb.
      contradict hb.
      eauto using bound_not_in_env, List.in_cons.
  Qed.

  Lemma free_to_in_env:
    forall u env,
    t env u ->
    forall x,
    Free.t x u ->
    List.In x env.
  Proof.
    intros u env H.
    induction H.
    all: intros x_orig hf.
    all: simpl in hf.
    all: eauto using N.WellTyped.free_1.
    all: intuition.
    - rename_hyp (Free.t _ _) as hf.
      apply IHt in hf.
      simpl in hf.
      intuition.
      subst.
      intuition.
    - eapply R.WellTyped.free_1 in H; eauto.
    - rename_hyp (Free.t _ _) as hf.
      apply IHt in hf.
      simpl in hf.
      intuition.
      subst.
      intuition.
    - eapply B.WellTyped.free_1 in H; eauto.
  Qed.

  Lemma not_in_env_not_free:
    forall u env,
    t env u ->
    forall x,
    ~ List.In x env ->
    ~ Free.t x u.
  Proof.
    intros.
    intros N.
    contradict H0.
    eauto using free_to_in_env.
  Qed.

End Defs.
