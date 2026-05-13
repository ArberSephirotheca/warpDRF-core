From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import Tictac.
From Stdlib Require Import Lia.
From Faial.Approx Require Import Var.

Section Defs.

  Definition t (x:var) (r:range) : Prop :=
    match r with
    | (e1, e2) => NFree x e1 \/ NFree x e2
    end.

  Lemma subst:
    forall x v r,
    ~ t x r ->
    r_subst x v r = r.
  Proof.
    intros.
    destruct r as (n1, n2).
    simpl in *.
    rewrite n_subst_not_free with (v:=v); auto.
    rewrite n_subst_not_free with (v:=v); auto.
  Qed.

  Lemma subst_subst_trans:
    forall e x v y,
    ~ t x e ->
    r_subst x v (r_subst y (NVar x) e) = r_subst y v e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    rewrite n_subst_subst_trans; auto.
    rewrite n_subst_subst_trans; auto.
  Qed.

  Lemma inv_subst:
    forall e x y v,
    t x (r_subst y v e) ->
    NFree x v \/ t x e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    destruct H as [H|H]; eapply n_free_inv_subst in H; intuition.
  Qed.

  Lemma inv_subst_not_free:
    forall e x y v,
    t x (r_subst y v e) ->
    ~ NFree x v ->
    t x e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    destruct H; eauto using n_free_subst_neq.
  Qed.

  Lemma inv_subst_eq_1:
    forall x y e,
    ~ t x e ->
    t x (r_subst y (NVar x) e) ->
    t y e.
  Proof.
    intros x y (nx, ny); simpl in *; intros.
    destruct H0.
    - left.
      eauto using n_free_subst_eq.
    - right.
      eauto using n_free_subst_eq.
  Qed.

  Lemma inv_subst_eq_2:
    forall x r e,
    t x (r_subst x e r) ->
    NFree x e.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    destruct H; apply n_free_inv_subst_eq in H; auto.
  Qed.

  Lemma not_free_after_subst:
    forall e x v,
    ~ NFree x v ->
    ~ t x (r_subst x v e).
  Proof.
    intros.
    intros N.
    destruct e as (e1, e2).
    simpl in N.
    destruct N as [N|N].
    all: apply NExp.not_free_after_subst in N.
    all: auto.
  Qed.
End Defs.