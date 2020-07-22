Require Import Coq.Lists.List.
Require Import Var.
Require Import RangeList.
Import ListNotations.
Require Coq.omega.Omega.
Require Import NExp.

Section Defs.

  Inductive nrel := NEquals | NLe | NLt.

  Inductive brel := BOr | BAnd.

  Inductive bexp :=
  | BBool: bool -> bexp
  | NRel : nrel -> nexp -> nexp -> bexp
  | BRel : brel -> bexp -> bexp -> bexp
  | BNot : bexp -> bexp.

  Inductive mode := R | W.

  Definition mode_eqb m1 m2 :=
  match m1, m2 with
  | R, R | W, W => true
  | _, _ => false
  end.

End Defs.

Section SO.

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

  Inductive RStep: range -> list nat -> Prop :=
  | r_step_def:
    forall e1 e2 n1 n2 l,
    NStep e1 n1 ->
    NStep e2 n2 ->
    RangeList n1 n2 l ->
    RStep (e1, e2) l.

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

  Inductive BIn (x: var): bexp -> Prop :=
  | b_in_n_rel_l:
    forall o n1 n2,
    NIn x n1 ->
    BIn x (NRel o n1 n2)
  | b_in_n_rel_r:
    forall o n1 n2,
    NIn x n2 ->
    BIn x (NRel o n1 n2)
  | b_in_b_rel_l:
    forall o b1 b2,
    BIn x b1 ->
    BIn x (BRel o b1 b2)
  | b_in_b_rel_r:
    forall o b1 b2,
    BIn x b2 ->
    BIn x (BRel o b1 b2)
  | b_in_not:
    forall b,
    BIn x b ->
    BIn x (BNot b).

  Lemma not_in_n_rel:
    forall x o n1 n2,
    ~ BIn x (NRel o n1 n2) ->
    ~ NIn x n1 /\ ~ NIn x n2.
  Proof.
    intros.
    split; intros N; contradict H; auto using b_in_n_rel_l, b_in_n_rel_r.
  Qed.

  Lemma not_in_b_rel:
    forall x o b1 b2,
    ~ BIn x (BRel o b1 b2) ->
    ~ BIn x b1 /\ ~ BIn x b2.
  Proof.
    intros.
    repeat split; intros N; contradict H; auto using b_in_b_rel_l, b_in_b_rel_r.
  Qed.

  Lemma not_in_not:
    forall x b,
    ~ BIn x (BNot b) ->
    ~ BIn x b.
  Proof.
    intros.
    intros N; contradict H; auto using b_in_not.
  Qed.

  Lemma b_subst_not_in:
    forall x v b,
    ~ BIn x b ->
    b_subst x v b = b.
  Proof.
    induction b; simpl; intros.
    - reflexivity.
    - apply not_in_n_rel in H.
      destruct H.
      rewrite n_subst_not_in; auto.
      rewrite n_subst_not_in; auto.
    - apply not_in_b_rel in H.
      destruct H.
      rewrite IHb1; auto.
      rewrite IHb2; auto.
    - apply not_in_not in H.
      rewrite IHb; auto.
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

  Lemma in_b_subst_neq:
    forall e x y v,
    BIn x (b_subst y v e) ->
    ~ NIn x v ->
    BIn x e.
  Proof.
    induction e; simpl; intros; inversion H; subst; rename H into N.
    - apply in_n_subst_neq in H2; auto using b_in_n_rel_l.
    - apply in_n_subst_neq in H2; auto using b_in_n_rel_r.
    - apply IHe1 in H2; auto using b_in_b_rel_l.
    - apply IHe2 in H2; auto using b_in_b_rel_r.
    - apply IHe in H2; auto using b_in_not.
  Qed.

  Lemma not_in_n_bin_n_rel:
    forall o n1 n2 x,
    ~ BIn x (NRel o n1 n2) ->
    ~ NIn x n1 /\ ~ NIn x n2.
  Proof.
    intros.
    split; contradict H; auto using b_in_n_rel_l, b_in_n_rel_r.
  Qed.

  Lemma not_in_n_bin_b_rel:
    forall o b1 b2 x,
    ~ BIn x (BRel o b1 b2) ->
    ~ BIn x b1 /\ ~ BIn x b2.
  Proof.
    intros.
    split; contradict H; auto using b_in_b_rel_l, b_in_b_rel_r.
  Qed.

  Lemma b_subst_subst_trans:
    forall e x v y,
    ~ BIn x e ->
    b_subst x v (b_subst y (NVar x) e) = b_subst y v e.
  Proof.
    induction e; simpl; intros.
    - reflexivity.
    - apply not_in_n_bin_n_rel in H.
      destruct H.
      rewrite n_subst_subst_trans; auto.
      rewrite n_subst_subst_trans; auto.
    - apply not_in_n_bin_b_rel in H.
      destruct H.
      rewrite IHe1; auto.
      rewrite IHe2; auto.
    - apply not_in_not in H.
      rewrite IHe; auto.
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


End SO.

