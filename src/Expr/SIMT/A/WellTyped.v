From Stdlib Require Import Lists.List.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Expr Require SIMT.N.WellTyped.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Var.
From Faial.Expr Require SIMT.A.MultiSubst.
From Faial.Expr Require Import SIMT.A.Equal.

Section Defs.

  Variable tid: nat.

  Lemma multi_subst_to_equal:
    forall e env,
    N.WellTyped.t env (ae_index e) ->
    forall m1 m2,
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    A.Equal.t tid (MultiSubst.f m1 e) (MultiSubst.f m2 e).
  Proof.
    intros.
    destruct e as (e1, e2).
    simpl.
    constructor. { reflexivity. }
    simpl in *.
    eauto using N.WellTyped.multi_subst_to_equal.
  Qed.
End Defs.
