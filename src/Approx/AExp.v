From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.
From Faial.Core Require Export AVal.

Import ListNotations.
Section Defs.
  Variable tid : nat.

  Record access_exp := {
    ae_index: nexp;
    ae_mode: mode;
  }.

  Definition ae_write (index:nexp) := {|
    ae_index := index;
    ae_mode := m_write;
  |}.

  Definition ae_read (index:nexp) := {|
    ae_index := index;
    ae_mode := m_read;
  |}.

  Definition a_subst x v e :=
  {|
    ae_index := n_subst x v (ae_index e);
    ae_mode := ae_mode e
  |}.

  Inductive AStep : access_exp -> access_val -> Prop :=
  | a_step_def:
    forall e_idx n_idx m,
    NStep tid e_idx n_idx ->
    AStep {| ae_index := e_idx; ae_mode := m |}
          {| av_index := n_idx; av_owner := tid; av_mode := m |}.

  Lemma a_step_write:
    forall e n,
    NStep tid e n ->
    AStep (ae_write e) (av_write tid n).
  Proof.
    unfold ae_write, av_write.
    intros.
    constructor.
    assumption.
  Qed.

  Lemma a_step_read:
    forall e n,
    NStep tid e n ->
    AStep (ae_read e) (av_read tid n).
  Proof.
    unfold ae_read, av_read.
    intros.
    constructor.
    assumption.
  Qed.

  Lemma ae_read_subst_commute:
    forall x v e,
    ae_read (n_subst x v e) =
    a_subst x v (ae_read e).
  Proof.
    intros.
    unfold ae_read, a_subst.
    reflexivity.
  Qed.

  Lemma a_step_inv_read:
    forall e n,
    NStep tid e n ->
    forall v,
    AStep (ae_read e) v ->
    v = av_read tid n.
  Proof.
    intros.
    invc H0.
    assert (n = n_idx) by eauto using n_step_fun.
    subst.
    unfold av_read.
    reflexivity.
  Qed.

  Lemma a_step_inv_write:
    forall e n,
    NStep tid e n ->
    forall v,
    AStep (ae_write e) v ->
    v = av_write tid n.
  Proof.
    intros.
    invc H0.
    assert (n = n_idx) by eauto using n_step_fun.
    subst.
    unfold av_write.
    reflexivity.
  Qed.

  Lemma a_step_inv_tid:
    forall e a,
    AStep e a ->
    av_owner a = tid.
  Proof.
    intros.
    invc H.
    reflexivity.
  Qed.

  Lemma a_step_fun:
    forall e v1 v2,
    AStep e v1 ->
    AStep e v2 ->
    v1 = v2.
  Proof.
    intros.
    invc H.
    invc H0.
    f_equal.
    eauto using n_step_fun.
  Qed.

  Lemma a_subst_subst_eq:
    forall x n1 n2 a,
    a_subst x (NNum n1) (a_subst x (NNum n2) a) = a_subst x (NNum n2) a.
  Proof.
    intros.
    unfold a_subst.
    simpl.
    rewrite NExp.n_subst_subst_eq.
    reflexivity.
  Qed.

  Lemma a_subst_subst_eq_2:
    forall (x : Var.var) n v e ,
    ~ NFree x v -> a_subst x e (a_subst x v n) = a_subst x v n.
  Proof.
    intros.
    unfold a_subst.
    simpl.
    rewrite NExp.n_subst_subst_eq_2; auto.
  Qed.

  Lemma a_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    a_subst x (NNum n1) (a_subst y (NNum n2) a) =
    a_subst y (NNum n2) (a_subst x (NNum n1) a).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_neq.
    { reflexivity. }
    { apply H. }
  Qed.

  Lemma a_subst_subst_neq_2:
    forall x y z n a,
    x <> z ->
    y <> z ->
    a_subst x (NVar y) (a_subst z (NNum n) a)
    =
    a_subst z (NNum n) (a_subst x (NVar y) a).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_neq_2.
    { reflexivity. }
    { apply H0. }
    { apply H. }
  Qed.

  Lemma a_subst_subst_neq_3 :
    forall e (x y : Var.var) v1 v2,
       x <> y ->
       ~ NFree y v1 ->
       ~ NFree x v2 ->
       a_subst x v1 (a_subst y v2 e) =
       a_subst y v2 (a_subst x v1 e).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_neq_3.
    { reflexivity. }
    { apply H. }
    { apply H0. }
    { apply H1. }
  Qed.

  Lemma a_subst_subst_neq_5 :
    forall e3 (x y : Var.var) (e1 e2 : nexp),
       NClosed e1 ->
       x <> y ->
       a_subst y e1 (a_subst x e2 e3) =
       a_subst x (n_subst y e1 e2) (a_subst y e1 e3).
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_neq_5.
    { reflexivity. }
    { apply H. }
    { apply H0. }
  Qed.

  Lemma a_subst_subst_eq_1 :
      forall (e1 e2 : nexp) (x : Var.VAR.t) a,
       a_subst x e1 (a_subst x e2 a) = a_subst x (n_subst x e1 e2) a.
  Proof.
    unfold a_subst.
    intros.
    simpl.
    rewrite NExp.n_subst_subst_eq_1.
    reflexivity.
  Qed.

  Lemma a_subst_subst_trans
     : forall e (x : Var.var) v (y : Var.VAR.t),
       ~ NFree x (ae_index e) ->
       a_subst x v (a_subst y (NVar x) e) = a_subst y v e.
  Proof.
    unfold In, a_subst.
    intros.
    simpl in *.
    rewrite NExp.n_subst_subst_trans.
    { reflexivity. }
    { apply H. }
  Qed.

  Lemma a_subst_not_free
     : forall (x : Var.var) v n,
     ~ NFree x (ae_index n) ->
     a_subst x v n = n.
  Proof.
    unfold a_subst.
    intros.
    rewrite NExp.n_subst_not_free.
    { destruct n. simpl. reflexivity. }
    { apply H. }
  Qed.

  Lemma to_closed:
    forall e v,
    AStep e v ->
    NClosed (ae_index e).
  Proof.
    intros.
    invc H.
    simpl.
    eauto using n_step_to_closed.
  Qed.

End Defs.
