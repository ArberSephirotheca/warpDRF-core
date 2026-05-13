From Faial.Expr Require Import SIMT.B.Exp.
From Stdlib Require Import Classes.Morphisms.
From Faial.Core Require Import Tictac.
From Faial.Expr Require Import SIMT.N.Equal.

Section Equal.
  Variable tid: nat.
  Definition t b1 b2 :=
    forall b,
    BStep tid b1 b <-> BStep tid b2 b.

  Lemma refl:
    forall b,
    t b b.
  Proof.
    unfold t; tauto.
  Qed.

  Lemma sym:
    forall b1 b2,
    t b1 b2 ->
    t b2 b1.
  Proof.
    unfold t; intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma trans:
    forall b1 b2 b3,
    t b1 b2 ->
    t b2 b3 ->
    t b1 b3.
  Proof.
    unfold t.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [BEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ t
    reflexivity proved by refl
    symmetry proved by sym
    transitivity proved by trans
    as setoid.

  Lemma proper_1:
    forall b b1 b1' b2 b2' o,
    t b1 b1' ->
    t b2 b2' ->
    BStep tid (BRel o b1 b2) b ->
    BStep tid (BRel o b1' b2') b.
  Proof.
    intros.
    invc H1.
    apply H in H6.
    apply H0 in H7.
    apply b_step_brel; auto.
  Qed.

  Global Instance proper_2: Proper (eq ==> t ==> t ==> t) BRel.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using proper_1.
    - symmetry in H0.
      symmetry in H1.
      eauto using proper_1.
  Qed.

  Global Instance proper_3: Proper (t ==> eq ==> iff) (BStep tid).
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  Lemma and_true:
    forall b,
    t (BRel BAnd b (BBool true)) b.
  Proof.
    split; intros.
    - invc H.
      invc H5.
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


  Lemma brel_sym:
    forall o b1 b2,
    t (BRel o b1 b2) (BRel o b2 b1).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite eval_brel_sym.
      apply b_step_brel; auto.
    - inversion H; subst; clear H.
      rewrite eval_brel_sym.
      apply b_step_brel; auto.
  Qed.

  Lemma and_false:
    forall b b',
    BStep tid b b' ->
    t (BRel BAnd b (BBool false)) (BBool false).
  Proof.
    split; intros.
    - invc H0.
      invc H6.
      simpl.
      rewrite Bool.andb_false_r.
      auto using b_step_bool.
    - invc H0.
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

  Lemma proper_4:
    forall b n1 n1' n2 n2' o,
    N.Equal.t tid n1 n1' ->
    N.Equal.t tid n2 n2' ->
    BStep tid (NRel o n1 n2) b ->
    BStep tid (NRel o n1' n2') b.
  Proof.
    intros.
    invc H1.
    apply H in H6.
    apply H0 in H7.
    apply b_step_nrel; auto.
  Qed.

  Global Instance proper_5: Proper (eq ==> N.Equal.t tid ==> N.Equal.t tid ==> t) NRel.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using proper_4.
    - symmetry in H0.
      symmetry in H1.
      eauto using proper_4.
  Qed.

  Global Instance proper_not: Proper (t ==> t) BNot.
  Proof.
    unfold Proper, respectful.
    intros b1 b2 eq1.
    split.
    all: intros ha.
    all: invc ha.
    all: constructor.
    - rewrite <- eq1.
      assumption.
    - rewrite <- eq1 in *.
      assumption.
  Qed.

  Lemma proper_6:
    forall x v v' e n, 
    N.Equal.t tid v v' ->
    BStep tid (b_subst x v e) n ->
    BStep tid (b_subst x v' e) n.
  Proof.
    induction e; intros.
    all: simpl in *.
    - assumption.
    - rewrite H in H0.
      assumption.
    - invc H0.
      eauto using b_step_brel.
    - invc H0.
      apply b_step_not; auto.
  Qed.

  Global Instance proper_7: Proper (eq ==> N.Equal.t tid ==> eq ==> t) b_subst.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - eapply proper_6; eauto.
    - symmetry in H0.
      eapply proper_6; eauto.
  Qed.
End Equal.
