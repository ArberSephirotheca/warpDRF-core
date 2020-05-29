Require Import Coq.Setoids.Setoid.
Require Coq.Classes.Morphisms.

Set Implicit Arguments.
Section Defs.
  Variable A:Type.
  Definition lang := A -> Prop.
  Definition Member (S:lang) : lang := fun x => S x.
  Definition Either (S1 S2:lang) : lang := fun x => Member S1 x \/ Member S2 x.
  Definition Both (S1 S2:lang) : lang := fun x => Member S1 x /\ Member S2 x.
  Definition Incl S1 S2 := forall x, Member S1 x -> Member S2 x.
  Definition Intersect S1 S2 := forall x, Member S1 x /\ Member S2 x.
  Definition Union S1 S2 := forall x, Member S1 x \/ Member S2 x.
  Definition Equiv S1 S2 := forall x, Member S1 x <-> Member S2 x.

  Lemma incl_def:
    forall (S1 S2:lang),
    (forall x, S1 x -> S2 x) ->
    Incl S1 S2.
  Proof.
    unfold Incl; auto.
  Qed.

  Lemma equiv_def:
    forall (S1 S2:lang),
    (forall x, S1 x -> S2 x) ->
    (forall x, S2 x -> S1 x) ->
    Equiv S1 S2.
  Proof.
    unfold Equiv, Member.
    split; intros; auto.
  Qed.

  Lemma member_either_l:
    forall P Q x,
    Member P x ->
    Member (Either P Q) x.
  Proof.
    intros.
    left.
    assumption.
  Qed.

  Lemma member_either_r:
    forall P Q x,
    Member Q x ->
    Member (Either P Q) x.
  Proof.
    intros.
    right.
    assumption.
  Qed.

  Lemma member_both:
    forall P Q x,
    Member P x ->
    Member Q x ->
    Member (Both P Q) x.
  Proof.
    intros.
    split; auto.
  Qed.

  (* ------------------ Incl + Both ---------------- *)

  (* Both on the left *)
  Lemma incl_l_both:
    forall P Q R,
    Incl P R ->
    Incl Q R ->
    Incl (Both P Q) R.
  Proof.
    unfold Incl.
    intros.
    destruct H1; auto.
  Qed.

  (* no inversion possible *)

  (* Both on the right *)

  Lemma incl_r_both:
    forall P Q R,
    Incl P Q ->
    Incl P R ->
    Incl P (Both Q R).
  Proof.
    unfold Incl.
    intros.
    apply member_both; auto.
  Qed.

  Lemma incl_r_both_inv:
    forall P Q R,
    Incl P (Both Q R) ->
    Incl P Q /\ Incl P R.
  Proof.
    unfold Incl; split; intros; apply H in H0; destruct H0; auto.
  Qed.

  Lemma incl_r_both_inv_l:
    forall P Q R,
    Incl P (Both Q R) ->
    Incl P Q.
  Proof.
    intros.
    apply incl_r_both_inv in H.
    destruct H; auto.
  Qed.

  Lemma incl_r_both_inv_r:
    forall P Q R,
    Incl P (Both Q R) ->
    Incl P R.
  Proof.
    intros.
    apply incl_r_both_inv in H.
    destruct H; auto.
  Qed.

  Lemma incl_r_both_iff:
    forall P Q R,
    Incl P (Both Q R) <->
    Incl P Q /\ Incl P R.
  Proof.
    split; intros; auto using incl_r_both_inv.
    destruct H.
    auto using incl_r_both.
  Qed.

  (* ------------------ Incl + Either ---------------- *)

  Lemma incl_l_either:
    forall P Q R,
    Incl P R ->
    Incl Q R ->
    Incl (Either P Q) R.
  Proof.
    unfold Incl.
    intros.
    destruct H1; auto.
  Qed.

  (* Either on the left *)

  Lemma incl_l_either_inv:
    forall P Q R,
    Incl (Either P Q) R ->
    Incl P R /\ Incl Q R.
  Proof.
    unfold Incl; intros.
    split; intros.
    - auto using member_either_l.
    - auto using member_either_r.
  Qed.

  Lemma incl_l_either_inv_l:
    forall P Q R,
    Incl (Either P Q) R ->
    Incl P R.
  Proof.
    intros.
    apply incl_l_either_inv in H.
    destruct H; auto.
  Qed.

  Lemma incl_l_either_inv_r:
    forall P Q R,
    Incl (Either P Q) R ->
    Incl Q R.
  Proof.
    intros.
    apply incl_l_either_inv in H.
    destruct H; auto.
  Qed.

  Lemma incl_l_either_iff:
    forall P Q R,
    Incl (Either P Q) R <-> (Incl P R /\ Incl Q R).
  Proof.
    split; intros.
    - apply incl_l_either_inv; assumption.
    - destruct H.
      auto using incl_l_either.
  Qed.

  (* Either on the right *)

  Lemma incl_r_either_l:
    forall P Q R,
    Incl P Q ->
    Incl P (Either Q R).
  Proof.
    unfold Incl.
    intros.
    left.
    auto.
  Qed.

  Lemma incl_r_either_r:
    forall P Q R,
    Incl P R ->
    Incl P (Either Q R).
  Proof.
    unfold Incl.
    intros.
    right.
    auto.
  Qed.

  (* no inversion possible *)

  Lemma incl_to_equiv:
    forall P Q,
    Incl P Q ->
    Incl Q P ->
    Equiv P Q.
  Proof.
    unfold Incl, Equiv.
    split; intros.
    - apply H.
      assumption.
    - apply H0.
      assumption.
  Qed.

  Lemma equiv_to_incl:
    forall P Q,
    Equiv P Q ->
    Incl P Q /\ Incl Q P.
  Proof.
    unfold Incl, Equiv; split; intros.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  Lemma incl_trans:
    forall P Q R,
    Incl P Q ->
    Incl Q R ->
    Incl P R.
  Proof.
    unfold Incl; auto.
  Qed.

  Lemma incl_refl:
    forall P,
    Incl P P.
  Proof.
    unfold Incl; auto.
  Qed.

  Lemma equiv_trans:
    forall P Q R,
    Equiv P Q ->
    Equiv Q R ->
    Equiv P R.
  Proof.
    unfold Equiv; intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma equiv_refl:
    forall P,
    Equiv P P.
  Proof.
    unfold Equiv; reflexivity.
  Qed.

  Lemma equiv_sym:
    forall P Q,
    Equiv P Q ->
    Equiv Q P.
  Proof.
    unfold Equiv.
    intros.
    symmetry.
    auto.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : lang Equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
    as l_equiv_setoid.

  (* We can now use reflexivity: *)
  Goal
    forall P,
    Equiv P P.
  Proof.
    reflexivity.
  Qed.

  Import Morphisms.

  Global Instance member_equiv_proper: Proper (Equiv ==> eq ==> iff) Member.
  Proof.
    unfold Proper, respectful, Equiv.
    intros.
    subst.
    rewrite H.
    reflexivity.
  Qed.

  (* Show that we can rewrite the set in the first param *)
  Goal forall P Q x,
    Equiv P Q ->
    Member P x ->
    Member Q x.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.

  Lemma either_equiv_proper_1:
    forall a b c d f,
    Equiv a b ->
    Equiv c d ->
    Either a c f ->
    Either b d f.
  Proof.
    intros.
    destruct H1; unfold Either.
    - rewrite <- H.
      rewrite <- H0.
      auto.
    - rewrite <- H.
      rewrite <- H0.
      auto.
  Qed.

  Global Instance either_equiv_proper: Proper (Equiv ==> Equiv ==> eq ==> iff) Either.
  Proof.
    unfold Proper, respectful.
    intros a b eq1 c d eq2 e f ?.
    subst.
    split; intros Ha.
    - eauto using either_equiv_proper_1.
    - symmetry in eq1.
      symmetry in eq2.
      eauto using either_equiv_proper_1.
  Qed.

  (* Show that we can rewrite the languages in the paramters of Equiv *)
  Goal forall P Q R x,
    Equiv P Q ->
    Either P R x ->
    Either Q R x.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.

  Lemma both_equiv_proper_1:
    forall a b c d f,
    Equiv a b ->
    Equiv c d ->
    Both a c f ->
    Both b d f.
  Proof.
    intros.
    destruct H1; unfold Both.
    rewrite <- H.
    rewrite <- H0.
    auto.
  Qed.

  Global Instance both_equiv_proper: Proper (Equiv ==> Equiv ==> eq ==> iff) Both.
  Proof.
    unfold Proper, respectful.
    intros a b eq1 c d eq2 e f ?.
    subst.
    split; intros Ha.
    - eauto using both_equiv_proper_1.
    - symmetry in eq1.
      symmetry in eq2.
      eauto using both_equiv_proper_1.
  Qed.


  (* Show that we can rewrite the languages in the paramters of Equiv *)
  Goal forall P Q R x,
    Equiv P Q ->
    Both P R x ->
    Both Q R x.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.

  Lemma incl_equiv_proper_1:
    forall S1 S2 S3 S4,
    Equiv S1 S2 ->
    Equiv S3 S4 ->
    Incl S1 S3 ->
    Incl S2 S4.
  Proof.
    unfold Equiv, Incl.
    intros.
    apply H in H2.
    apply H0.
    auto.
  Qed.


  (* Allow rewriting under Incl *)
  Global Instance incl_equiv_proper: Proper (Equiv ==> Equiv ==> iff) Incl.
  Proof.
    unfold Proper.
    unfold respectful.
    intros a b eq1 c d eq2.
    split; intros Ha.
    - eauto using incl_equiv_proper_1.
    - symmetry in eq1.
      symmetry in eq2.
      eauto using incl_equiv_proper_1.
  Qed.


  (* Show that we can rewrite an argument of incl *)
  Goal
    forall P Q R,
    Equiv P Q ->
    Incl P R ->
    Incl Q R.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.

  Global Instance either_equiv_equiv_proper: Proper (Equiv ==> Equiv ==> Equiv) Either.
  Proof.
    unfold Proper, respectful.
    intros S1 S2 eq1 S3 S4 eq2.
    split; unfold Member; intros.
    - rewrite <- eq1.
      rewrite <- eq2.
      assumption.
    - rewrite eq1.
      rewrite eq2.
      assumption.
  Qed.

  Goal
    forall P Q R S,
    Equiv P Q ->
    Incl (Either P S) R ->
    Incl (Either Q S) R.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.

  Global Instance both_equiv_equiv_proper: Proper (Equiv ==> Equiv ==> Equiv) Both.
  Proof.
    unfold Proper, respectful.
    intros S1 S2 eq1 S3 S4 eq2.
    split; unfold Member; intros.
    - rewrite <- eq1.
      rewrite <- eq2.
      assumption.
    - rewrite eq1.
      rewrite eq2.
      assumption.
  Qed.

  Goal
    forall P Q R S,
    Equiv P Q ->
    Incl (Both P S) R ->
    Incl (Both Q S) R.
  Proof.
    intros.
    rewrite <- H.
    assumption.
  Qed.
End Defs.
