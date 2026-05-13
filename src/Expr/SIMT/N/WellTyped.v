From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import InUtil.
From Faial.Expr Require SIMT.N.MultiSubst.
From Faial.Expr Require SIMT.N.Equal.

Import ListNotations.

  Inductive t (env: list var) : nexp -> Prop :=
  | num:
    forall n,
    t env (NNum n)
  | tid:
    t env NTid
  | var:
    forall x,
    List.In x env ->
    t env (NVar x)
  | n_bin:
    forall o e1 e2,
    t env e1 ->
    t env e2 ->
    t env (NBin o e1 e2).

  Lemma progress:
    forall e,
    t [] e ->
    forall tid,
    exists n, NStep tid e n.
  Proof.
    induction e; intros.
    - exists tid0.
      constructor.
    - eauto using n_step_num.
    - invc H.
      contradiction.
    - invc H.
      destruct IHe1 with (tid:=tid0) as (n1, Hn1); auto.
      destruct IHe2 with (tid:=tid0) as (n2, Hn2); auto.
      eauto using n_step_bin.
  Qed.

  Lemma to_closed:
    forall e,
    t [] e ->
    NClosed e.
  Proof.
    intros.
    apply progress with (tid:=0) in H.
    destruct H as (n, H).
    eauto using n_step_to_closed.
  Qed.

  Lemma subst:
    forall env e,
    t env e ->
    forall x n,
    t env (n_subst x (NNum n) e).
  Proof.
    induction e; intros.
    all: simpl.
    - constructor.
    - constructor.
    - destruct (Set_VAR.MF.eq_dec x v). {
        constructor.
      }
      assumption.
    - invc H.
      constructor; eauto.
  Qed.

  Lemma to_not_free:
    forall x env,
    ~ In x env ->
    forall e,
    t env e ->
    ~ NFree x e.
  Proof.
    induction e.
    all: intros wt.
    all: simpl.
    all: try (intuition; fail).
    - invc wt.
      intros N.
      subst.
      contradiction.
    - invc wt.
      intuition.
  Qed.

  Lemma strengthen:
    forall x env e,
    ~ NFree x e ->
    t (x :: env) e ->
    t env e.
  Proof.
    induction e.
    all: intros nf wt.
    all: invc wt.
    - constructor.
    - constructor.
    - constructor.
      simpl in *.
      intuition.
      contradict nf.
      auto.
    - simpl in nf.
      constructor; auto.
  Qed.

  Lemma from_closed:
    forall e,
    NClosed e ->
    forall env,
    t env e.
  Proof.
    induction e.
    all: intros closed env.
    - constructor.
    - constructor.
    - contradict closed.
      auto using n_closed_var.
    - apply n_closed_inv_bin in closed.
      destruct closed.
      constructor; eauto.
  Qed.

  Lemma rw_subst tid:
    forall x  e n' n,
    NStep tid (n_subst x (NNum n) e) n' ->
    forall env,
    t env e ->
    ~ List.In x env ->
    NStep tid e n'.
  Proof.
    induction e.
    all: intros n_dest n_orig r_e1 env wt nin.
    all: simpl in r_e1.
    all: auto.
    - destruct (Set_VAR.MF.eq_dec x v).
      + subst.
        invc wt.
        contradiction.
      + assumption.
    - invc r_e1.
      invc wt.
      constructor.
      all: eauto.
  Qed.

  Lemma n_step_subst_func tid:
    forall x env,
    ~ In x env ->
    forall e,
    t env e ->
    forall n1 n1',
    NStep tid (n_subst x (NNum n1) e) n1' ->
    forall n2 n2',
    NStep tid (n_subst x (NNum n2) e) n2' ->
    n1' = n2'.
  Proof.
    intros.
    eapply rw_subst in H1; eauto.
    eapply rw_subst in H2; eauto.
    eauto using n_step_fun.
  Qed.

  Lemma reorder:
    forall e env1 env2,
    SetEq.t env1 env2 ->
    t env1 e ->
    t env2 e.
  Proof.
    induction e.
    all: intros env1 env2 eq1 wt.
    all: invc wt.
    all: constructor.
    all: eauto.
    apply eq1.
    assumption.
  Qed.

  Lemma free_1:
    forall env e,
    t env e ->
    forall x,
    NFree x e ->
    List.In x env.
  Proof.
    intros env e H.
    induction H.
    all: intros y Hf.
    all: simpl in Hf.
    all: intuition.
    subst.
    assumption.
  Qed.

  Lemma subst_strengthen:
    forall x env e,
    t (x :: env) e ->
    forall n,
    t env (n_subst x (NNum n) e).
  Proof.
    intros.
    apply strengthen with (x:=x).
    - apply not_free_after_subst.
      apply n_free_num.
    - apply subst.
      assumption.
  Qed.

  Lemma multi_subst_to_equal tid:
    forall e env,
    t env e ->
    forall m1 m2,
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    Equal.t tid (MultiSubst.f m1 e) (MultiSubst.f m2 e).
  Proof.
    induction e.
    all: intros e wt m1 m2 S.
    all: simpl.
    - reflexivity.
    - reflexivity.
    - invc wt.
      destruct (Map_VAR.find v m1) eqn:eq1. {
        assert (e1: Map_VAR.find v m2 = Some n). {
          apply Map_VAR.find_1.
          apply S; auto.
          apply Map_VAR.find_2.
          assumption.
        }
        rewrite e1.
        reflexivity.
      }
      assert (e1: Map_VAR.find v m2 = None). {
        destruct (Map_VAR.find v m2) eqn:eq3. {
          assert (e1: Map_VAR.find v m1 = Some n). {
            apply Map_VAR.find_1.
            apply S; auto.
            apply Map_VAR.find_2.
            assumption.
          }
          rewrite e1 in *.
          invc eq1.
        }
        reflexivity.
      }
      rewrite e1.
      reflexivity.
    - invc wt.
      erewrite IHe1; eauto.
      erewrite IHe2; eauto.
      reflexivity.
  Qed.

  Lemma multisubst:
    forall env n,
    t env n ->
    forall m,
    (forall x, In x env <-> Map_VAR.In x m) ->
    t [] (N.MultiSubst.f m n).
  Proof.
    intros env n H.
    induction H.
    all: intros m Ha.
    all: simpl.
    - constructor.
    - constructor.
    - apply Ha in H.
      apply Map_VAR_Extra.in_to_mapsto in H.
      destruct H as (e, H).
      apply Map_VAR.find_1 in H.
      rewrite H.
      constructor.
    - specialize (IHt1 m Ha).
      specialize (IHt2 m Ha).
      constructor.
      all: assumption.
  Qed.

(*
  Lemma multi_subst_rw tid:
    forall e env,
    t env e ->
    forall m1 v,
    NStep tid (MultiSubst.f m1 e) v ->
    forall m2,
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    NStep tid (MultiSubst.f m2 e) v.
  Proof.
    intros.
    erewrite <- multi_subst_to_equal; eauto.
  Qed.

  Lemma multi_subst_fun tid:
    forall e env,
    t env e ->
    forall m1 v1,
    NStep tid (MultiSubst.f m1 e) v1 ->
    forall m2 v2,
    NStep tid (MultiSubst.f m2 e) v2 ->
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    v1 = v2.
  Proof.
    intros.
    assert (NStep tid (MultiSubst.f m2 e) v1). {
      eapply multi_subst_rw; eauto.
    }
    eauto using n_step_fun.
  Qed.
  *)