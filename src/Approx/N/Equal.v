From Faial.Approx Require Import NExp.
From Stdlib Require Import Classes.Morphisms.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Var.

Section Equal.
  Variable tid: nat.
  Definition t e1 e2 :=
    forall n,
    NStep tid e1 n <-> NStep tid e2 n.

  Lemma refl:
    forall e,
    t e e.
  Proof.
    unfold t; tauto.
  Qed.

  Lemma sym:
    forall e1 e2,
    t e1 e2 ->
    t e2 e1.
  Proof.
    unfold t; intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma trans:
    forall e1 e2 e3,
    t e1 e2 ->
    t e2 e3 ->
    t e1 e3.
  Proof.
    unfold t.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [NEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ t
    reflexivity proved by refl
    symmetry proved by sym
    transitivity proved by trans
    as r_eq_setoid.

  Lemma to_n_step:
    forall e n,
    t e (NNum n) ->
    NStep tid e n.
  Proof.
    intros.
    apply H.
    auto using n_step_num.
  Qed.

  Lemma from_n_step:
    forall e n,
    NStep tid e n ->
    t e (NNum n).
  Proof.
    split; intros.
    - assert (n0 = n) by eauto using n_step_fun.
      subst.
      auto using n_step_num.
    - inversion H0; subst; clear H0.
      assumption.
  Qed.

  Lemma bin_1:
    forall n e1 e1' e2 e2' o,
    t e1 e1' ->
    t e2 e2' ->
    NStep tid (NBin o e1 e2) n ->
    NStep tid (NBin o e1' e2') n.
  Proof.
    intros.
    invc H1.
    apply H in H6.
    apply H0 in H7.
    apply n_step_bin; auto.
  Qed.

  Global Instance proper_1: Proper (eq ==> t ==> t ==> t) NBin.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using bin_1.
    - symmetry in H0.
      symmetry in H1.
      eauto using bin_1.
  Qed.

  Global Instance proper_2: Proper (t ==> eq ==> iff) (NStep tid).
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  Lemma n_step_n_subst_proper:
    forall x v v' e n,
    t v v' ->
    NStep tid (n_subst x v e) n ->
    NStep tid (n_subst x v' e) n.
  Proof.
    induction e; intros.
    - simpl in *.
      assumption.
    - assumption.
    - simpl in *.
      destruct (VAR.eq_dec x v0); auto.
      subst.
      apply H; auto.
    - simpl in *.
      inversion H0; subst; clear H0.
      eauto using n_step_bin.
  Qed.

  Lemma n_step_subst:
    forall x v v' e n n',
    NStep tid v n ->
    NStep tid v' n ->
    NStep tid (n_subst x v e) n' ->
    NStep tid (n_subst x v' e) n'.
  Proof.
    intros.
    eapply n_step_n_subst_proper; eauto.
    split; intros Hn; assert (n0 = n) by eauto using n_step_fun; subst; auto.
  Qed.

  Lemma rw_subst:
    forall x v v' e, 
    t v v' ->
    t (n_subst x v e) (n_subst x v' e).
  Proof.
    intros.
    split; intros.
    - eauto using n_step_n_subst_proper.
    - symmetry in H.
      eauto using n_step_n_subst_proper.
  Qed.

  Global Instance proper_3: Proper (eq ==> t ==> eq ==> t) n_subst.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - eapply n_step_n_subst_proper; eauto.
    - symmetry in H0.
      eapply n_step_n_subst_proper; eauto.
  Qed.

  Lemma subst_subst:
    forall x v e v' n,
    t v v' ->
    NStep tid (n_subst x v e) n ->
    t (n_subst x v' (n_subst x v e)) (n_subst x v' e).
  Proof.
    intros.
    split; intros.
    - edestruct n_step_inv_subst as [Hx|(n', Hx)]; eauto. {
        rewrite n_subst_not_free in H1; auto.
        rewrite <- H.
        assumption.
      }
      rewrite <- H in Hx.
      rewrite n_subst_subst_eq_2 in H1; eauto using n_step_to_not_free.
      rewrite <- H.
      assumption.
    - rewrite <- H in H1.
      assert (n0 = n) by eauto using n_step_fun.
      subst.
      edestruct n_step_inv_subst as [Hx|(n', Hx)]; eauto. {
        rewrite n_subst_not_free;
        eauto using n_step_to_not_free.
      }
      rewrite n_subst_subst_eq_2; eauto using n_step_to_not_free.
  Qed.

  Lemma def:
    forall e1 e2 n,
    NStep tid e1 n ->
    NStep tid e2 n ->
    t e1 e2.
  Proof.
    intros.
    split; intros;
      assert (n0 = n) by eauto using n_step_fun; subst; auto.
  Qed.
End Equal.