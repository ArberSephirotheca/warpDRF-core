From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lia.
From Faial.Expr Require SIMT.R.Closed.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> nat -> Prop :=
  | def:
    forall e1 e2 n1 n2,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    t (e1, e2) n1.

  Lemma from_closed:
    forall r,
    R.Closed.t r ->
    exists n, t r n.
  Proof.
    intros.
    destruct r as (e1, e2).
    apply Closed.inv in H.
    destruct H as (Ha, Hb).
    apply n_closed_to_step with (tid:=tid) in Ha.
    apply n_closed_to_step with (tid:=tid) in Hb.
    destruct Ha as (a, Ha).
    destruct Hb as (b, Hb).
    eexists.
    econstructor.
    all: eauto.
  Qed.
End Defs.