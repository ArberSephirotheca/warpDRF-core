From Stdlib Require Import Lists.List.
From Faial.Approx Require Import Var.
Import ListNotations.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Faial.Approx Require Import InUtil.

Section Defs.

  Inductive nrel := NEquals | NLe | NLt.

  Inductive brel := BOr | BAnd.

  Inductive bexp :=
  | BBool: bool -> bexp
  | NRel : nrel -> nexp -> nexp -> bexp
  | BRel : brel -> bexp -> bexp -> bexp
  | BNot : bexp -> bexp.

End Defs.

Section SO.
  Variable tid: nat.
  Notation NStep := (NStep tid).
  Definition eval_nrel (o:nrel) :=
  match o with
  | NEquals => Nat.eqb
  | NLt => Nat.ltb
  | NLe => Nat.leb
  end.

  Definition eval_brel (o:brel) :=
  match o with
  | BOr => orb
  | BAnd => andb
  end.

  Inductive BStep: bexp -> bool -> Prop :=
  | b_step_bool:
    forall b,
    BStep (BBool b) b
  | b_step_nrel:
    forall e1 e2 n1 n2 o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    BStep (NRel o e1 e2) (eval_nrel o n1 n2)
  | b_step_brel:
    forall e1 e2 b1 b2 o,
    BStep e1 b1 ->
    BStep e2 b2 ->
    BStep (BRel o e1 e2) (eval_brel o b1 b2)
  | b_step_not:
    forall e b,
    BStep e b ->
    BStep (BNot e) (negb b).

  Fixpoint b_subst x v e :=
  match e with
  | NRel o e1 e2 => NRel o (n_subst x v e1) (n_subst x v e2)
  | BRel o e1 e2 => BRel o (b_subst x v e1) (b_subst x v e2)
  | BNot b => BNot (b_subst x v b)
  | BBool b => BBool b
  end.

  Lemma b_step_subst_next:
    forall x e n b1,
    BStep (b_subst x (NNum n) e) b1 ->
    forall m, exists b2, BStep (b_subst x (NNum m) e) b2.
  Proof.
    induction e; intros; inversion H; subst; clear H; simpl.
    - exists b1.
      constructor.
    - apply n_step_subst_next with (m1:=m) in H4.
      apply n_step_subst_next with (m1:=m) in H5.
      destruct H4 as (ma, Ha).
      destruct H5 as (mb, Hb).
      exists (eval_nrel n ma mb).
      constructor; auto.
    - apply IHe1 with (m:=m) in H4.
      apply IHe2 with (m:=m) in H5.
      destruct H4 as (ba, Ha).
      destruct H5 as (bb, Hb).
      exists (eval_brel b ba bb).
      constructor; auto.
    - apply IHe with (m:=m) in H1.
      destruct H1 as (b1, Hb).
      exists (negb b1).
      constructor.
      assumption.
  Qed.

  Lemma b_step_lt:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    BStep (NRel NLt e1 e2) true.
  Proof.
    intros.
    assert (R: true = eval_nrel NLt n1 n2). {
      simpl.
      apply PeanoNat.Nat.ltb_lt in H1.
      rewrite H1.
      reflexivity.
    }
    rewrite R.
    auto using b_step_nrel.
  Qed.

  Fixpoint b_step (e:bexp) :=
  match e with
  | BBool b => Some b
  | NRel o e1 e2 =>
    match n_step tid e1, n_step tid e2 with
    | Some n1, Some n2 => Some (eval_nrel o n1 n2)
    | _, _ => None
    end
  | BRel o e1 e2 =>
    match b_step e1, b_step e2 with
    | Some b1, Some b2 => Some (eval_brel o b1 b2)
    | _, _ => None
    end
  | BNot e =>
    match b_step e with
    | Some b => Some (negb b)
    | None => None
    end
  end.

  Lemma b_step_to_prop:
    forall e b,
    b_step e = Some b ->
    BStep e b.
  Proof.
    induction e; intros; simpl in *.
    - inversion H; subst; clear H.
      auto using b_step_bool.
    - destruct (n_step tid n0) eqn:He1. {
        destruct (n_step tid n1) eqn:He2; inversion H; subst; clear H.
        auto using n_step_to_prop, b_step_nrel.
      }
      inversion H.
    - destruct (b_step e1) eqn:He1. {
        destruct (b_step e2) eqn:He2; inversion H; subst; clear H.
        auto using b_step_brel.
      }
      inversion H.
    - destruct (b_step e) eqn:He1; inversion H.
      auto using b_step_not.
  Qed.

  Lemma prop_to_b_step:
    forall e b,
    BStep e b ->
    b_step e = Some b.
  Proof.
    induction e; intros; inversion H; subst; clear H; simpl.
    - reflexivity.
    - apply prop_to_n_step in H4.
      apply prop_to_n_step in H5.
      rewrite H4.
      rewrite H5.
      reflexivity.
    - apply IHe1 in H4.
      apply IHe2 in H5.
      rewrite H4.
      rewrite H5.
      reflexivity.
    - apply IHe in H1.
      rewrite H1.
      reflexivity.
  Qed.

  Lemma b_step_fun:
    forall e b1 b2,
    BStep e b1 ->
    BStep e b2 ->
    b1 = b2.
  Proof.
    intros.
    apply prop_to_b_step in H.
    apply prop_to_b_step in H0.
    rewrite H in *.
    inversion H0.
    reflexivity.
  Qed.

  Fixpoint BFree (x: var) (b:bexp): Prop :=
    match b with
    | NRel _ n1 n2 => NFree x n1 \/ NFree x n2
    | BRel _ b1 b2 => BFree x b1 \/ BFree x b2
    | BNot b => BFree x b
    | BBool _ => False
    end.

  Lemma b_subst_not_free:
    forall x v b,
    ~ BFree x b ->
    b_subst x v b = b.
  Proof.
    induction b; simpl; intros.
    - reflexivity.
    - rewrite n_subst_not_free; auto.
      rewrite n_subst_not_free; auto.
    - simpl in *.
      rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma b_subst_subst_neq_2:
    forall x y z n e,
    y <> z ->
    x <> z ->
    b_subst x (NVar y) (b_subst z (NNum n) e)
    =
    b_subst z (NNum n) (b_subst x (NVar y) e).
  Proof.
    induction e; intros; simpl.
    - reflexivity.
    - rewrite n_subst_subst_neq_2; auto.
      rewrite n_subst_subst_neq_2; auto.
    - rewrite IHe1; auto.
      rewrite IHe2; auto.
    - rewrite IHe; auto.
  Qed.

  Lemma b_subst_subst_neq_3:
    forall e x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    b_subst x v1 (b_subst y v2 e)
    =
    b_subst y v2 (b_subst x v1 e).
  Proof.
    induction e; intros; simpl; auto.
    - rewrite n_subst_subst_neq_3; auto.
      rewrite n_subst_subst_neq_3 with (x:=y) (y:=x) (e:=n1); auto.
    - rewrite IHe1; auto.
      rewrite IHe2; auto.
    - rewrite IHe; auto.
  Qed.

  Lemma b_free_subst_neq:
    forall e x y v,
    BFree x (b_subst y v e) ->
    ~ NFree x v ->
    BFree x e.
  Proof.
    induction e; simpl; intros.
    - assumption.
    - destruct H; eauto using n_free_subst_neq.
    - destruct H; eauto using n_free_subst_neq.
    - eauto.
  Qed.

  Lemma b_subst_subst_trans:
    forall e x v y,
    ~ BFree x e ->
    b_subst x v (b_subst y (NVar x) e) = b_subst y v e.
  Proof.
    induction e; simpl; intros.
    - reflexivity.
    - rewrite n_subst_subst_trans; auto.
      rewrite n_subst_subst_trans; auto.
    - rewrite IHe1; auto.
      rewrite IHe2; auto.
    - rewrite IHe; auto.
  Qed.

  Lemma b_subst_subst_eq:
    forall x n1 n2 b,
    b_subst x (NNum n1) (b_subst x (NNum n2) b) = b_subst x (NNum n2) b.
  Proof.
    induction b; simpl.
    - reflexivity.
    - repeat rewrite n_subst_subst_eq.
      reflexivity.
    - rewrite IHb2.
      rewrite IHb1.
      reflexivity.
    - rewrite IHb.
      reflexivity.
  Qed.

  Lemma b_subst_subst_eq_2:
    forall x b v e,
    ~ NFree x v ->
    b_subst x e (b_subst x v b) = b_subst x v b.
  Proof.
    induction b; intros; simpl.
    - reflexivity.
    - rewrite n_subst_subst_eq_2; auto.
      rewrite n_subst_subst_eq_2; auto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma b_subst_subst_neq:
    forall x y n1 n2 b,
    x <> y ->
    b_subst x (NNum n1) (b_subst y (NNum n2) b) =
    b_subst y (NNum n2) (b_subst x (NNum n1) b).
  Proof.
    induction b; simpl; intros.
    - reflexivity.
    - remember (n_subst x _ _) as a.
      symmetry in Heqa.
      remember (n_subst y _ (n_subst _ _ n3)) as b.
      symmetry in Heqb.
      rewrite n_subst_subst_neq in Heqa; auto.
      rewrite n_subst_subst_neq in Heqb; auto.
      subst.
      reflexivity.
    - assert (IHb1 := IHb1 H).
      assert (IHb2 := IHb2 H).
      rewrite IHb1.
      rewrite IHb2.
      reflexivity.
    - rewrite IHb; auto.
  Qed.

  Lemma eval_brel_sym:
    forall o b1 b2,
    eval_brel o b1 b2 = eval_brel o b2 b1.
  Proof.
    intros.
    destruct o; simpl.
    - destruct b1, b2; auto.
    - destruct b1, b2; auto.
  Qed.


  Lemma b_free_inv_subst:
    forall e x y v,
    BFree x (b_subst y v e) ->
    NFree x v \/ BFree x e.
  Proof.
    induction e; simpl; intros; auto.
    - intuition; apply n_free_inv_subst in H0; intuition.
    - intuition; rename_hyp (BFree _ _) as hb.
      + apply IHe1 in hb; intuition.
      + apply IHe2 in hb; intuition.
    - apply IHe in H.
      intuition.
  Qed.

  Lemma b_free_inv_subst_eq:
    forall x e b,
    BFree x (b_subst x e b) ->
    NFree x e.
  Proof.
    induction b; simpl; intros.
    - invc H.
    - destruct H;
        eauto using n_free_inv_subst_eq.
    - destruct H; auto.
    - auto.
  Qed.

  Lemma b_subst_subst_eq_1:
    forall e1 e2 x b,
    b_subst x e1 (b_subst x e2 b)
    =
    b_subst x (n_subst x e1 e2) b.
  Proof.
    induction b; intros; simpl.
    - reflexivity.
    - erewrite n_subst_subst_eq_1; eauto.
      erewrite n_subst_subst_eq_1; eauto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma b_subst_subst_neq_4:
    forall b e1 e2 x y,
    x <> y ->
    NClosed e1 ->
    b_subst y e1 (b_subst x e2 b) =
    b_subst y e1 (b_subst x (n_subst y e1 e2) b).
  Proof.
    induction b; intros.
    - reflexivity.
    - simpl.
      rewrite n_subst_subst_neq_4; auto.
      assert (r1: n_subst y e1 (n_subst x e2 n1) =
              n_subst y e1 (n_subst x (n_subst y e1 e2) n1)). {
        rewrite n_subst_subst_neq_4; auto.
      }
      rewrite r1.
      reflexivity.
    - simpl.
      rewrite IHb1; auto.
      rewrite IHb2; auto.
    - simpl.
      rewrite IHb; auto.
  Qed.

  Lemma b_subst_subst_neq_5:
    forall b x y e1 e2,
    NClosed e1 ->
    x <> y ->
    b_subst y e1 (b_subst x e2 b) =
    b_subst x (n_subst y e1 e2) (b_subst y e1 b).
  Proof.
    induction b; intros; simpl.
    - reflexivity.
    - rewrite n_subst_subst_neq_5; auto.
      rewrite n_subst_subst_neq_5 with (e3:=n1); auto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma not_free_after_subst:
    forall e x v,
    ~ NFree x v ->
    ~ BFree x (b_subst x v e).
  Proof.
    induction e.
    all: intros x_orig v_orig hn.
    all: simpl in *.
    all: intuition.
    - rename_hyp (NFree _ (n_subst _ _ _)) as hb.
      apply NExp.not_free_after_subst in hb; auto.
    - rename_hyp (NFree _ (n_subst _ _ _)) as hb.
      apply NExp.not_free_after_subst in hb; auto.
    - rename_hyp (BFree _ (b_subst _ _ _)) as hb.
      apply IHe1 in hb; auto.
    - rename_hyp (BFree _ (b_subst _ _ _)) as hb.
      apply IHe2 in hb; auto.
    - rename_hyp (BFree _ (b_subst _ _ _)) as hb.
      apply IHe in hb; auto.
  Qed.

End SO.
Module Closed.
  Definition t e := forall x, ~ BFree x e.

  Lemma b_bool:
    forall b,
    t (BBool b).
  Proof.
    unfold t.
    intros b x N.
    invc N.
  Qed.

  Lemma b_not:
    forall e,
    t e ->
    t (BNot e).
  Proof.
    unfold t.
    intros.
    intros N.
    specialize (H x).
    simpl in *.
    contradiction.
  Qed.

  Lemma n_rel:
    forall e1 e2 o,
    NClosed e1 ->
    NClosed e2 ->
    t (NRel o e1 e2).
  Proof.
    unfold t.
    intros.
    intros N.
    simpl in *.
    destruct N as [N|N].
    - apply n_closed_to_not_free in N; auto.
    - apply n_closed_to_not_free in N; auto.
  Qed.

  Lemma b_rel:
    forall e1 e2 o,
    t e1 ->
    t e2 ->
    t (BRel o e1 e2).
  Proof.
    unfold t.
    intros.
    intros N.
    simpl in *.
    destruct N as [N|N].
    - specialize (H x). contradiction.
    - specialize (H0 x). contradiction.
  Qed.

  Lemma inv_n_rel_l:
    forall o n1 n2,
    t (NRel o n1 n2) ->
    NClosed n1.
  Proof.
    intros.
    unfold t in *.
    unfold NClosed.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    simpl.
    intuition.
  Qed.

  Lemma inv_n_rel_r:
    forall o n1 n2,
    t (NRel o n1 n2) ->
    NClosed n2.
  Proof.
    intros.
    unfold t in *.
    unfold NClosed.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    simpl.
    intuition.
  Qed.

  Lemma inv_n_rel:
    forall o e1 e2,
    t (NRel o e1 e2) ->
    NClosed e1 /\ NClosed e2.
  Proof.
    intros.
    split.
    - eauto using inv_n_rel_l.
    - eauto using inv_n_rel_r.
  Qed.

  Lemma inv_b_rel_l:
    forall o e1 e2,
    t (BRel o e1 e2) ->
    t e1.
  Proof.
    intros.
    unfold t in *.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    simpl.
    intuition.
  Qed.

  Lemma inv_b_rel_r:
    forall o e1 e2,
    t (BRel o e1 e2) ->
    t e2.
  Proof.
    intros.
    unfold t in *.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    simpl.
    intuition.
  Qed.

  Lemma inv_b_rel:
    forall o e1 e2,
    t (BRel o e1 e2) ->
    t e1 /\ t e2.
  Proof.
    intros.
    split.
    - eauto using inv_b_rel_l.
    - eauto using inv_b_rel_r.
  Qed.

  Lemma inv_b_not:
    forall e,
    t (BNot e) ->
    t e.
  Proof.
    unfold t.
    intros.
    intros N.
    specialize (H x).
    contradict H.
    simpl.
    assumption.
  Qed.

  Lemma to_step tid:
    forall e,
    t e ->
    exists b, BStep tid e b.
  Proof.
    induction e; intros.
    - eauto using b_step_bool.
    - apply inv_n_rel in H.
      destruct H as [Ha Hb].
      destruct (n_closed_to_step tid _ Ha) as (a, Ha').
      destruct (n_closed_to_step tid _ Hb) as (b, Hb').
      eauto using b_step_nrel.
    - apply inv_b_rel in H.
      destruct H as [Ha Hb].
      apply IHe1 in Ha.
      apply IHe2 in Hb.
      destruct Ha as (e1_v, Ha).
      destruct Hb as (e2_v, Hb).
      eauto using b_step_brel.
    - apply inv_b_not in H.
      apply IHe in H.
      destruct H as (e_v, H).
      eauto using b_step_not.
  Qed.

  Lemma from_step tid:
    forall b e,
    BStep tid e b ->
    t e.
  Proof.
    intros.
    induction H.
    - apply b_bool.
    - eauto using n_rel, n_step_to_closed.
    - auto using b_rel.
    - auto using b_not.
  Qed.

End Closed.

  Lemma b_step_subst_num tid:
    forall b e,
    BStep tid e b ->
    forall x n,
    BStep tid (b_subst x (NNum n) e) b.
  Proof.
    intros.
    rewrite b_subst_not_free.
    { assumption. }
    apply Closed.from_step in H.
    apply H.
  Qed.
