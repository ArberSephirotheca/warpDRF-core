From Faial.Approx Require Import AExp.
Require Import N.Equal.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Classes.RelationPairs.

Section AExp_Equal.
  Variable tid: nat.
  Inductive t x y : Prop :=
    def:
      ae_mode x = ae_mode y ->
      N.Equal.t tid (ae_index x) (ae_index y) ->
      t x y.

(*
  Lemma step_proper:
    forall (e' e) (n n' : nexp) (h : list access_val),
  access_eq e e' -> NEq n n' -> OneDim.Step (e, n) h -> OneDim.Step (e', n') h.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    rewrite H0 in *.
    apply step_def.
    { auto. apply H in H4. apply H4. }
    { auto. }
    { apply H. }
  Qed.

  Lemma free_subst_neq : 
    forall e (x y : Var.var) (v : nexp),
    Free x (subst y v e) -> ~ NFree x v -> Free x e.
  Proof.
    intros.
    unfold Free in *.
    simpl in *.
    apply n_free_subst_neq in H.
    - apply H.
    - apply H0.
  Qed.
*)
  Lemma subst:
    forall (x : Var.var) (v v' : nexp) (e : access_exp),
    N.Equal.t tid v v' ->
    t (a_subst x v e) (a_subst x v' e).
  Proof.
    intros.
    split; intros.
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
  Qed.

  Lemma refl:
    forall x, 
    t x x.
  Proof.
    intros.
    apply def.
    all: reflexivity.
  Qed.

  Lemma sym:
    forall x y, 
    t x y -> 
    t y x.
  Proof.
    intros.
    destruct H as (Ha, Hb).
    apply def.
    - rewrite Ha.
      reflexivity.
    - rewrite Hb.
      reflexivity.
  Qed.

  Lemma trans: 
    forall x y z,
    t x y -> 
    t y z -> 
    t x z.
  Proof.
    intros x y z (Ha, Hb) (Hc, Hd).
    apply def.
    all: etransitivity; eauto.
  Qed.

  (** Register [BEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ t
    reflexivity proved by refl
    symmetry proved by sym
    transitivity proved by trans
    as setoid.

  #[global] Instance proper_subst: Proper (eq ==> N.Equal.t tid ==> eq ==> t)
    a_subst.
  Proof.
    unfold Proper, respectful.
    intros y x ? v' v eq1 (e1, e2) (e1', e2') ?.
    invc H0.
    constructor.
    + reflexivity.
    + simpl.
      rewrite eq1.
      reflexivity.
  Qed.

  #[global] Instance proper_step: Proper (t ==> eq ==> iff) (AStep tid).
  Proof.
    unfold Proper, respectful.
    intros (e1,o1) (e2, o2) eq1 v' v ?.
    subst.
    split.
    all: intros ha.
    all: invc ha.
    all: invc eq1.
    all: simpl in *.
    all: subst.
    all: constructor.
    - rewrite <- H0.
      assumption.
    - rewrite H0.
      assumption.
  Qed.

(*
  Lemma free_inv_subst_eq : 
    forall (x : Var.var) (e : nexp) (a : E),
       Free x (subst x e a) -> NFree x e.
  Proof.
    intros.
    unfold Free in *.
    unfold subst in *. 
    simpl in *.
    apply n_free_inv_subst_eq in H.
    auto.
  Qed.
  *)
End AExp_Equal.