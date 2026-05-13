From Stdlib Require Import Classes.RelationPairs.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Import ListNotations.

From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Util.
From Faial.Approx Require Import InUtil.

Section Defs.
  Definition range := (nexp * nexp) % type.

  Definition r_subst x v (r:range) :=
  let (n1, n2) := r in
  (n_subst x v n1, n_subst x v n2).

  Lemma r_subst_subst_neq_2:
    forall x y z n e,
    y <> z ->
    x <> z ->
    r_subst x (NVar y) (r_subst z (NNum n) e)
    =
    r_subst z (NNum n) (r_subst x (NVar y) e).
  Proof.
    intros.
    destruct e.
    simpl.
    repeat rewrite n_subst_subst_neq_2; auto.
  Qed.

  Lemma r_subst_subst_neq_3:
    forall e x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    r_subst x v1 (r_subst y v2 e)
    =
    r_subst y v2 (r_subst x v1 e).
  Proof.
    intros (e1, e2); intros.
    simpl.
    rewrite n_subst_subst_neq_3; auto.
    rewrite n_subst_subst_neq_3 with (e:=e2); auto.
  Qed.

  Lemma r_subst_subst_eq:
    forall x n1 n2 r,
    r_subst x (NNum n1) (r_subst x (NNum n2) r) = r_subst x (NNum n2) r.
  Proof.
    intros.
    destruct r; simpl.
    repeat rewrite n_subst_subst_eq.
    reflexivity.
  Qed.

  Lemma r_subst_subst_neq:
    forall x y n1 n2 r,
    x <> y ->
    r_subst x (NNum n1) (r_subst y (NNum n2) r) =
    r_subst y (NNum n2) (r_subst x (NNum n1) r).
  Proof.
    destruct r; simpl; intros.
    rewrite n_subst_subst_neq; auto.
    remember (n_subst y _ (n_subst x _ n0)) as a.
    symmetry in Heqa.
    rewrite n_subst_subst_neq in Heqa; auto.
    subst.
    reflexivity.
  Qed.

  Lemma r_subst_subst_eq_2:
    forall x r v e,
    ~ NFree x v ->
    r_subst x e (r_subst x v r) = r_subst x v r.
  Proof.
    intros.
    destruct r.
    simpl in *.
    rewrite n_subst_subst_eq_2; auto.
    rewrite n_subst_subst_eq_2; auto.
  Qed.

  Variable tid : nat.


  (* ------------------------------------- *)

  (* ------------------------- HAS NEXT ------------------- *)

 
  (* ------------------------------------ RPRED ------------------- *)
(*
  Inductive RPred (P:nat -> nat -> Prop): range -> Prop :=
  | r_pred_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    P n1 n2 ->
    RPred P (e1, e2).

  Lemma r_pred_eq:
    forall (P: nat -> nat -> Prop) n1 n2,
    P n1 n2 ->
    RPred P (NNum n1, NNum n2).
  Proof.
    intros.
    eapply r_pred_def; eauto using n_step_num.
  Qed.
*)
  Lemma r_subst_subst_eq_1:
    forall e1 e2 x r,
    r_subst x e1 (r_subst x e2 r)
    =
    r_subst x (n_subst x e1 e2) r.
  Proof.
    intros.
    destruct r as (r1, r2).
    simpl.
    rewrite n_subst_subst_eq_1.
    rewrite n_subst_subst_eq_1.
    reflexivity.
  Qed.

  Lemma r_subst_subst_neq_4:
    forall r e1 e2 x y,
    NClosed e1 -> 
    x <> y ->
    r_subst y e1 (r_subst x e2 r) =
    r_subst y e1 (r_subst x (n_subst y e1 e2) r).
  Proof.
    intros (e1', e2') e1 e2 x y Hc Hn.
    simpl.
    apply eq_pair_def.
    - rewrite n_subst_subst_neq_4; auto.
    - rewrite n_subst_subst_neq_4; auto.
  Qed.

  Lemma r_subst_subst_neq_5:
    forall r x y e1 e2,
    NClosed e1 ->
    x <> y ->
    r_subst y e1 (r_subst x e2 r) =
    r_subst x (n_subst y e1 e2) (r_subst y e1 r).
  Proof.
    intros (e1', e2') x y e1 e2 Hc Hn.
    simpl.
    rewrite n_subst_subst_neq_5; auto.
    rewrite n_subst_subst_neq_5 with (e3:=e2'); auto.
  Qed.


End Defs.
(*

Module RExpNotations.
  Import NExpNotations.
  Notation "x '∈'  r " := (RPick r x) (at level 30, only printing) : exp_scope.
  Notation "r [ x := v ]" := (r_subst x v r) (at level 30, only printing) : exp_scope. 
End RExpNotations.*)