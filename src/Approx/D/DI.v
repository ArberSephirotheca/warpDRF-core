Require D.Lang.

From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import InUtil.
From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
Require Import D.Lang.
From Faial.Expr Require SIMT.N.WellTyped.
From Faial.Expr Require SIMT.B.WellTyped.
From Faial.Expr Require SIMT.R.WellTyped.
From Faial.Expr Require SIMT.A.WellTyped.
Require D.Free.
Require D.Bound.
Require D.WF.
Require U.DI.
Require U.LRun.
Require D.LRun.
Import ListNotations.
Require D.Infer.

Section WellTyped.
  Inductive t : list var -> D.Lang.t -> Prop :=
  | read:
    forall env idx x s,
    N.WellTyped.t env idx ->
    t env s ->
    t env (Read x idx s)
  | decl:
    forall env x s,
    t env s ->
    t env (Decl x s)
  | write:
    forall env idx val,
    N.WellTyped.t env idx ->
    t env (Write idx val)
  | seq:
    forall env s1 s2,
    t env s1 ->
    t env s2 ->
    t env (Seq s1 s2)
  | cond:
    forall env c s1 s2,
    t env s1 ->
    t env s2 ->
    t env (Cond c s1 s2)
  | loop_dep:
    forall env r s x,
    t env s ->
    t env (Loop x r s)
  | loop_indep:
    forall env r s x,
    R.WellTyped.t env r ->
    t (x::env) s ->
    t env (Loop x r s)
  | skip:
    forall env,
    t env Skip
  .

End WellTyped.

Section Completeness.

  Lemma to_di:
    forall env s,
    t env s ->
    U.DI.t env (Infer.f s).
  Proof.
    intros env s H.
    induction H.
    all: simpl.
    - constructor.
      + constructor.
        unfold ae_index, ae_read.
        assumption.
      + constructor.
        assumption.
    - constructor.
      assumption.
    - constructor.
      unfold ae_index, ae_write.
      assumption.
    - constructor.
      all: auto.
    - constructor.
      all: assumption.
    - apply U.DI.loop_dep; auto.
    - apply U.DI.loop_indep; auto.
    - constructor.
  Qed.


  Lemma func tid base:
    forall M s P' M' l,
    D.LRun.t tid base M s P' M' l ->
    forall P,
    U.LRun.t tid (Infer.f s) P l ->
    forall env,
    t env s ->
    forall dom,
    incl env dom ->
    D.WF.t dom s ->
    P = P'.
  Proof.
    intros.
    assert (U.LRun.t tid (Infer.f s) P' l) by eauto using Infer.to_run.
    eapply U.DI.func; eauto.
    - apply to_di. assumption.
    - apply Infer.to_wf. assumption.
  Qed.

End Completeness.

