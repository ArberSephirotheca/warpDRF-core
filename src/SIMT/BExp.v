Require Import Coq.Lists.List.
Require Import Var.
Import ListNotations.
Require Import SIMT.NExp.
Require Import Pure.BExp.
Require Import Tictac.

Section Defs.

  Inductive bexp :=
  | BBool: bool -> bexp
  | NRel : nrel -> nexp -> nexp -> bexp
  | BRel : brel -> bexp -> bexp -> bexp
  | BNot : bexp -> bexp.

End Defs.

Section SO.
  Notation p_nexp := Pure.NExp.nexp.
  Notation P_NVar := Pure.NExp.NVar.
  Notation p_bexp := Pure.BExp.bexp.
  Notation P_NRel := Pure.BExp.NRel.
  Notation P_BRel := Pure.BExp.BRel.
  Notation P_BNot := Pure.BExp.BNot.
  Notation P_BBool := Pure.BExp.BBool.

  Fixpoint to_pure (tid:p_nexp) (b:bexp) : p_bexp :=
    match b with
    | NRel o n1 n2 => P_NRel o (SIMT.NExp.to_pure tid n1) (SIMT.NExp.to_pure tid n2)
    | BRel o b1 b2 => P_BRel o (to_pure tid b1) (to_pure tid b2)
    | BNot b => P_BNot (to_pure tid b)
    | BBool b => P_BBool b
    end.

  Variable tid: nat.
  Notation NStep := (NStep tid).  

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

  Lemma b_subst_to_pure:
    forall b tid x (v:nexp),
    ~ Pure.NExp.NFree x tid ->
    to_pure tid (b_subst x v b) =
    Pure.BExp.b_subst x (SIMT.NExp.to_pure tid v) (to_pure tid b).
  Proof.
    induction b; intros; simpl.
    - reflexivity.
    - repeat rewrite n_subst_to_pure; eauto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma b_step_to_pure:
    forall e b,
    BExp.BStep (to_pure (Pure.NExp.NNum tid) e) b <-> BStep e b.
  Proof.
    split; intros.
    - generalize dependent b.
      induction e; intros b' Hs.
      all: simpl in Hs.
      all: invc Hs.
      all: constructor.
      all: eauto.
      all: rewrite n_step_to_pure in *.
      all: assumption.
    - induction H.
      all: simpl.
      all: constructor.
      all: eauto.
      all: rewrite n_step_to_pure.
      all: assumption.
  Qed.

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
  Notation n_step := (n_step tid).

  Fixpoint b_step (e:bexp) :=
  match e with
  | BBool b => Some b
  | NRel o e1 e2 =>
    match n_step e1, n_step e2 with
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
    - destruct (n_step n0) eqn:He1. {
        destruct (n_step n1) eqn:He2; inversion H; subst; clear H.
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

  Lemma b_subst_to_pure_eq:
    forall tid v (b:bexp),
    ~ Pure.NExp.NFree tid v ->
    ~ BFree tid b ->
    Pure.BExp.b_subst tid v (to_pure (Pure.NExp.NVar tid) b)
    = to_pure v b.
  Proof.
    induction b; simpl; intros.
    - reflexivity.
    - repeat rewrite n_subst_to_pure_eq; auto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma b_free_to_pure:
    forall x tid b,
    ~ Pure.NExp.NFree x tid ->
    Pure.BExp.BFree x (to_pure tid b) ->
    BFree x b.
  Proof.
    induction b; simpl; intros; auto.
    all: intuition.
    all: eauto using n_free_to_pure.
  Qed.

  Lemma b_free_n_rel_l:
    forall x n1,
    NFree x n1 ->
    forall o n2,
    BFree x (NRel o n1 n2).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma b_free_n_rel_r:
    forall x n2,
    NFree x n2 ->
    forall o n1,
    BFree x (NRel o n1 n2).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma b_free_b_rel_l:
    forall x e1,
    BFree x e1 ->
    forall o e2,
    BFree x (BRel o e1 e2).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma b_free_b_rel_r:
    forall x e2,
    BFree x e2 ->
    forall o e1,
    BFree x (BRel o e1 e2).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma b_free_not:
    forall x e,
    BFree x e ->
    BFree x (BNot e).
  Proof.
    intros.
    simpl.
    assumption.
  Qed.

  Lemma b_free_inv_bool:
    forall x b,
    ~ BFree x (BBool b).
  Proof.
    auto.
  Qed.

  Lemma b_free_inv_not:
    forall x e,
    BFree x (BNot e) ->
    BFree x e.
  Proof.
    auto.
  Qed.

  Lemma b_free_inv_n_rel:
    forall x o e1 e2,
    BFree x (NRel o e1 e2) ->
    NFree x e1 \/ NFree x e2.
  Proof.
    auto.
  Qed.

  Lemma b_free_inv_b_rel:
    forall x o e1 e2,
    BFree x (BRel o e1 e2) ->
    BFree x e1 \/ BFree x e2.
  Proof.
    auto.
  Qed.

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

  Definition BEq b1 b2 :=
    forall b,
    BStep b1 b <-> BStep b2 b.

  Lemma b_eq_refl:
    forall b,
    BEq b b.
  Proof.
    unfold BEq; tauto.
  Qed.

  Lemma b_eq_sym:
    forall b1 b2,
    BEq b1 b2 ->
    BEq b2 b1.
  Proof.
    unfold BEq; intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma b_eq_trans:
    forall b1 b2 b3,
    BEq b1 b2 ->
    BEq b2 b3 ->
    BEq b1 b3.
  Proof.
    unfold BEq.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [BEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ BEq
    reflexivity proved by b_eq_refl
    symmetry proved by b_eq_sym
    transitivity proved by b_eq_trans
    as b_eq_setoid.
  Import Morphisms.

  Lemma b_eq_proper_1:
    forall b b1 b1' b2 b2' o,
    BEq b1 b1' ->
    BEq b2 b2' ->
    BStep (BRel o b1 b2) b ->
    BStep (BRel o b1' b2') b.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply H in H6.
    apply H0 in H7.
    apply b_step_brel; auto.
  Qed.

  Global Instance b_eq_proper_2: Proper (eq ==> BEq ==> BEq ==> BEq) BRel.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using b_eq_proper_1.
    - symmetry in H0.
      symmetry in H1.
      eauto using b_eq_proper_1.
  Qed.

  Global Instance b_eq_proper_3: Proper (BEq ==> eq ==> iff) BStep.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  Lemma b_eq_and_true:
    forall b,
    BEq (BRel BAnd b (BBool true)) b.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      inversion H5; subst; clear H5.
      simpl.
      rewrite Bool.andb_true_r.
      assumption.
    - assert (R: b0 = eval_brel BAnd b0 true). {
        simpl.
        rewrite Bool.andb_true_r.
        reflexivity.
      }
      rewrite R.
      apply b_step_brel; auto using b_step_bool.
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

  Lemma b_eq_brel_sym:
    forall o b1 b2,
    BEq (BRel o b1 b2) (BRel o b2 b1).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite eval_brel_sym.
      apply b_step_brel; auto.
    - inversion H; subst; clear H.
      rewrite eval_brel_sym.
      apply b_step_brel; auto.
  Qed.

  Lemma b_eq_and_false:
    forall b b',
    BStep b b' ->
    BEq (BRel BAnd b (BBool false)) (BBool false).
  Proof.
    split; intros.
    - inversion H0; subst; clear H0.
      inversion H6; subst; clear H6.
      simpl.
      rewrite Bool.andb_false_r.
      auto using b_step_bool.
    - inversion H0; subst; clear H0.
      assert (R: false = eval_brel BAnd b' false). {
        simpl.
        rewrite Bool.andb_false_r.
        reflexivity.
      }
      rewrite R.
      apply b_step_brel; auto using b_step_bool.
      simpl in *.
      rewrite Bool.andb_false_r.
      auto using b_step_bool.
  Qed.

  Notation NEq := (NEq tid).

  Lemma b_eq_proper_4:
    forall b n1 n1' n2 n2' o,
    NEq n1 n1' ->
    NEq n2 n2' ->
    BStep (NRel o n1 n2) b ->
    BStep (NRel o n1' n2') b.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply H in H6.
    apply H0 in H7.
    apply b_step_nrel; auto.
  Qed.

  Global Instance b_eq_proper_5: Proper (eq ==> NEq ==> NEq ==> BEq) NRel.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using b_eq_proper_4.
    - symmetry in H0.
      symmetry in H1.
      eauto using b_eq_proper_4.
  Qed.


  Lemma b_eq_proper_6:
    forall x v v' e n, 
    NEq v v' ->
    BStep (b_subst x v e) n ->
    BStep (b_subst x v' e) n.
  Proof.
    induction e; intros.
    - simpl in *.
      assumption.
    - simpl in *.
      rewrite H in H0.
      assumption.
    - simpl in *.
      inversion H0; subst; clear H0.
      eauto using b_step_brel.
    - simpl in *.
      inversion H0; subst; clear H0.
      apply b_step_not; auto.
  Qed.

  Global Instance b_eq_proper_7: Proper (eq ==> NEq ==> eq ==> BEq) b_subst.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - eapply b_eq_proper_6; eauto.
    - symmetry in H0.
      eapply b_eq_proper_6; eauto.
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

  Definition BClosed e := forall x, ~ BFree x e.

  Lemma b_closed_bool:
    forall b,
    BClosed (BBool b).
  Proof.
    unfold BClosed.
    intros b x N.
    apply b_free_inv_bool in N.
    assumption.
  Qed.

  Lemma b_closed_not:
    forall e,
    BClosed e ->
    BClosed (BNot e).
  Proof.
    unfold BClosed.
    intros.
    intros N.
    specialize (H x).
    apply b_free_inv_not in N.
    contradiction.
  Qed.

  Lemma b_closed_n_rel:
    forall e1 e2 o,
    NClosed e1 ->
    NClosed e2 ->
    BClosed (NRel o e1 e2).
  Proof.
    unfold BClosed.
    intros.
    intros N.
    apply b_free_inv_n_rel in N.
    destruct N as [N|N].
    - apply n_closed_to_not_free in N; auto.
    - apply n_closed_to_not_free in N; auto.
  Qed.

  Lemma b_closed_b_rel:
    forall e1 e2 o,
    BClosed e1 ->
    BClosed e2 ->
    BClosed (BRel o e1 e2).
  Proof.
    unfold BClosed.
    intros.
    intros N.
    apply b_free_inv_b_rel in N.
    destruct N as [N|N].
    - specialize (H x). contradiction.
    - specialize (H0 x). contradiction.
  Qed.

  Lemma b_closed_inv_n_rel_l:
    forall o n1 n2,
    BClosed (NRel o n1 n2) ->
    NClosed n1.
  Proof.
    intros.
    unfold BClosed in *.
    unfold NClosed.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    auto using b_free_n_rel_l.
  Qed.

  Lemma b_closed_inv_n_rel_r:
    forall o n1 n2,
    BClosed (NRel o n1 n2) ->
    NClosed n2.
  Proof.
    intros.
    unfold BClosed in *.
    unfold NClosed.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    auto using b_free_n_rel_r.
  Qed.

  Lemma b_closed_inv_n_rel:
    forall o e1 e2,
    BClosed (NRel o e1 e2) ->
    NClosed e1 /\ NClosed e2.
  Proof.
    intros.
    split.
    - eauto using b_closed_inv_n_rel_l.
    - eauto using b_closed_inv_n_rel_r.
  Qed.

  Lemma b_closed_inv_b_rel_l:
    forall o e1 e2,
    BClosed (BRel o e1 e2) ->
    BClosed e1.
  Proof.
    intros.
    unfold BClosed in *.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    auto using b_free_b_rel_l.
  Qed.

  Lemma b_closed_inv_b_rel_r:
    forall o e1 e2,
    BClosed (BRel o e1 e2) ->
    BClosed e2.
  Proof.
    intros.
    unfold BClosed in *.
    intros x.
    specialize (H x).
    intros N.
    contradict H.
    auto using b_free_b_rel_r.
  Qed.

  Lemma b_closed_inv_b_rel:
    forall o e1 e2,
    BClosed (BRel o e1 e2) ->
    BClosed e1 /\ BClosed e2.
  Proof.
    intros.
    split.
    - eauto using b_closed_inv_b_rel_l.
    - eauto using b_closed_inv_b_rel_r.
  Qed.

  Lemma b_closed_inv_not:
    forall e,
    BClosed (BNot e) ->
    BClosed e.
  Proof.
    unfold BClosed.
    intros.
    intros N.
    specialize (H x).
    contradict H.
    auto using b_free_not.
  Qed.

  Lemma b_closed_to_step:
    forall e,
    BClosed e ->
    exists b, BStep e b.
  Proof.
    induction e; intros.
    - eauto using b_step_bool.
    - apply b_closed_inv_n_rel in H.
      destruct H as [Ha Hb].
      apply (n_closed_to_step tid) in Ha.
      apply (n_closed_to_step tid) in Hb.
      destruct Ha as (a, Ha).
      destruct Hb as (b, Hb).
      eauto using b_step_nrel.
    - apply b_closed_inv_b_rel in H.
      destruct H as [Ha Hb].
      apply IHe1 in Ha.
      apply IHe2 in Hb.
      destruct Ha as (e1_v, Ha).
      destruct Hb as (e2_v, Hb).
      eauto using b_step_brel.
    - apply b_closed_inv_not in H.
      apply IHe in H.
      destruct H as (e_v, H).
      eauto using b_step_not.
  Qed.

  Lemma b_step_to_closed:
    forall b e,
    BStep e b ->
    BClosed e.
  Proof.
    intros.
    induction H.
    - apply b_closed_bool.
    - eauto using b_closed_n_rel, n_step_to_closed.
    - auto using b_closed_b_rel.
    - auto using b_free_inv_not.
  Qed.

  Lemma b_step_iff_closed:
    forall e,
    (exists b, BStep e b) <-> BClosed e.
  Proof.
    split; intros.
    - destruct H.
      eauto using b_step_to_closed.
    - auto using b_closed_to_step.
  Qed.

End SO.
