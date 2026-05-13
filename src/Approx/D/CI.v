From Faial.Approx Require Import Tasks.
From Faial.Approx Require Import Var.
Require Import D.Lang.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import AExp.
From Stdlib Require Import List.
Require U.Lang.
Import ListNotations.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Sorting.SetoidList.
From Faial.Approx Require Import InUtil.
Require D.WF.
Require D.Bound.
Require D.Free.
Require N.WellTyped.
Require B.WellTyped.
Require R.WellTyped.
Require EqualModIndex.
Require D.Infer.
Require U.CI.

  Inductive t : list var -> D.Lang.t -> Prop :=
  | read:
    forall env idx x s,
    t env s ->
    t env (D.Lang.Read x idx s)
  | write:
    forall env idx val,
    t env (D.Lang.Write idx val)
  | seq:
    forall env s1 s2,
    t env s1 ->
    t env s2 ->
    t env (D.Lang.Seq s1 s2)
  | cond:
    forall env c s1 s2,
    B.WellTyped.t env c ->
    t env s1 ->
    t env s2 ->
    t env (D.Lang.Cond c s1 s2)
  | loop:
    forall env r s x,
    R.WellTyped.t env r ->
    t (x::env) s ->
    t env (D.Lang.Loop x r s)
  | skip:
    forall env,
    t env D.Lang.Skip
  | decl:
    forall env x s,
    t env s ->
    t env (D.Lang.Decl x s)
  .

Section Def.

  Lemma to_ci:
    forall env s,
    t env s ->
    U.CI.t env (Infer.f s).
  Proof.
    intros env s H.
    induction H.
    all: simpl.
    - constructor.
      + constructor.
      + constructor.
        assumption.
    - constructor.
    - constructor.
      all: auto.
    - constructor.
      all: auto.
    - constructor.
      all: assumption.
    - constructor.
    - constructor.
      assumption.
  Qed.

  Lemma func tid base:
    forall dom s,
    D.WF.t dom s ->
    forall env,
    List.incl env dom ->
    t env s ->
    forall M1 h1 M2 l1,
    D.LRun.t tid base M1 s h1 M2 l1 ->
    forall h2 l2,
    U.LRun.t tid (Infer.f s) h2 l2 ->
    l1 = l2.
  Proof.
    intros.
    apply Infer.to_run in H2.
    eapply U.CI.func; eauto using Infer.to_wf, to_ci.
  Qed.

End Def.
