From Faial.Approx Require Import Var.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
Require N.WellTyped.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.
From Faial.Approx Require Import InUtil.
Require R.MultiSubst.
Require R.Equal.
Import ListNotations.
From Stdlib Require Import Lia.
Require R.Closed.
Require R.Free.
Require R.Empty.
Require R.Step.
Section Defs.
  Inductive t (env:list var) : range -> Prop :=
  | def:
    forall e1 e2,
    N.WellTyped.t env e1 ->
    N.WellTyped.t env e2 ->
    t env (e1, e2).

  Lemma subst:
    forall env e,
    t env e ->
    forall x n,
    t env (r_subst x (NNum n) e).
  Proof.
    intros.
    invc H.
    constructor; auto using N.WellTyped.subst.
  Qed.

  Lemma from_closed:
    forall e,
    R.Closed.t e ->
    forall env,
    t env e.
  Proof.
    intros (e1, e2) closed env.
    apply R.Closed.inv in closed.
    destruct closed as (closed1, closed2).
    constructor; eauto using N.WellTyped.from_closed.
  Qed.

  Lemma to_closed:
    forall e,
    t [] e ->
    R.Closed.t e.
  Proof.
    intros.
    invc H.
    apply N.WellTyped.to_closed in H0.
    apply N.WellTyped.to_closed in H1.
    auto using R.Closed.def.
  Qed.

  Lemma to_not_free:
    forall x env,
    ~ In x env ->
    forall e,
    t env e ->
    ~ R.Free.t x e.
  Proof.
    intros x env nin (e1, e2) ht N.
    simpl in N.
    invc ht.
    destruct N as [N|N].
    all: contradict N.
    all: eauto using N.WellTyped.to_not_free.
  Qed.

  Lemma rw_empty_subst tid:
    forall x e n,
    R.Empty.t tid (r_subst x (NNum n) e) ->
    forall env,
    t env e ->
    ~ List.In x env ->
    R.Empty.t tid e.
  Proof.
    intros.
    destruct e as (e1, e2).
    invc H.
    rename_hyp (t env _ ) as wt.
    invc wt.
    rename_hyp (NStep _ (n_subst _ _ e1) _) as r1. 
    rename_hyp (NStep _ (n_subst _ _ e2) _) as r2. 
    eapply N.WellTyped.rw_subst in r1; eauto.
    eapply N.WellTyped.rw_subst in r2; eauto.
    econstructor; eauto.
  Qed.

  Lemma rw_step_subst tid:
    forall x e e' n n',
    R.Step.t tid (r_subst x (NNum n) e) n' e' ->
    forall env,
    t env e ->
    ~ List.In x env ->
    R.Step.t tid e n' e'.
  Proof.
    intros.
    destruct e as (e1, e2).
    invc H.
    rename_hyp (t env _ ) as wt.
    invc wt.
    rename_hyp (NStep _ (n_subst _ _ e1) _) as r1. 
    rename_hyp (NStep _ (n_subst _ _ e2) _) as r2. 
    eapply N.WellTyped.rw_subst in r1; eauto.
    eapply N.WellTyped.rw_subst in r2; eauto.
    econstructor; eauto.
  Qed.

  Lemma strengthen:
    forall x env e,
    ~ R.Free.t x e ->
    t (x :: env) e ->
    t env e.
  Proof.
    intros x env (e1, e2) nf wt.
    invc wt.
    simpl in nf.
    constructor.
    all: eapply N.WellTyped.strengthen.
    all: eauto.
  Qed.

  Lemma reorder:
    forall e env1 env2,
    SetEq.t env1 env2 ->
    t env1 e ->
    t env2 e.
  Proof.
    intros (e1, e2) x y env wt.
    invc wt.
    constructor.
    all: eauto using N.WellTyped.reorder.
  Qed.

  Lemma free_1:
    forall env e,
    t env e ->
    forall x,
    R.Free.t x e ->
    List.In x env.
  Proof.
    intros env e H.
    invc H.
    intros x Hr.
    simpl in Hr.
    destruct Hr as [Hr|Hr].
    all: eauto using N.WellTyped.free_1.
  Qed.

  Lemma subst_strengthen:
    forall x env e,
    t (x :: env) e ->
    forall n,
    t env (r_subst x (NNum n) e).
  Proof.
    intros.
    apply strengthen with (x:=x).
    - apply R.Free.not_free_after_subst.
      apply n_free_num.
    - apply subst.
      assumption.
  Qed.

  Lemma multi_subst_to_equal tid:
    forall e env,
    t env e ->
    forall m1 m2,
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    R.Equal.t tid (MultiSubst.f m1 e) (MultiSubst.f m2 e).
  Proof.
    intros.
    destruct e as (e1, e2).
    simpl.
    invc H.
    apply Equal.def.
    all: eauto using N.WellTyped.multi_subst_to_equal.
  Qed.

  Lemma progress:
    forall e,
    t [] e ->
    forall tid,
    R.HasNext.t tid e \/ R.Empty.t tid e.
  Proof.
    intros.
    invc H.
    apply N.WellTyped.progress with (tid:=tid) in H0.
    apply N.WellTyped.progress with (tid:=tid) in H1.
    destruct H0 as (n1, Hn1).
    destruct H1 as (n2, Hn2).
    assert (Hx: n1 < n2 \/ n1 >= n2) by lia.
    destruct Hx. {
      left.
      econstructor.
      all: eauto.
    }
    right.
    econstructor.
    all: eauto.
  Qed.

  Lemma multisubst:
    forall env e,
    t env e ->
    forall m,
    (forall x, In x env <-> Map_VAR.In x m) ->
    t [] (R.MultiSubst.f m e).
  Proof.
    intros env (e1, e2) H m spec.
    invc H.
    constructor.
    all: eauto using N.WellTyped.multisubst.
  Qed.

End Defs.