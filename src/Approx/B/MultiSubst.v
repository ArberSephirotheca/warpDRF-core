From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import Var.
Require N.MultiSubst.

Fixpoint f (m:Map_VAR.t nat) (e:bexp) : bexp :=
  match e with
  | BBool _ => e
  | NRel o e1 e2 => NRel o (MultiSubst.f m e1) (MultiSubst.f m e2)
  | BRel o e1 e2 => BRel o (f m e1) (f m e2)
  | BNot e => BNot (f m e)
  end.

Lemma rw_add_not_in:
  forall x n m e,
  ~ Map_VAR.In x m ->
  b_subst x (NNum n) (f m e) = f (Map_VAR.add x n m) e.
Proof.
  induction e.
  all: intros nin.
  all: simpl.
  - reflexivity.
  - repeat rewrite N.MultiSubst.rw_add_not_in; auto.
  - rewrite IHe1; auto.
    rewrite IHe2; auto.
  - rewrite IHe; auto.
Qed.

Lemma subst_eq:
  forall m1 m2,
  Map_VAR.Equal m1 m2 ->
  forall e,
  f m1 e = f m2 e.
Proof.
  induction e.
  all: simpl.
  - reflexivity.
  - f_equal.
    all: erewrite N.MultiSubst.subst_eq; eauto.
  - rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - rewrite IHe.
    reflexivity.
Qed.

Lemma rw_is_empty:
  forall e m,
  Map_VAR.Empty m ->
  f m e = e.
Proof.
  induction e.
  all: intros m mt.
  all: simpl.
  - reflexivity.
  - repeat rewrite N.MultiSubst.rw_is_empty; auto.
  - rewrite IHe1; auto.
    rewrite IHe2; auto.
  - rewrite IHe; auto.
Qed.

Lemma from_subst:
  forall x n e,
  b_subst x (NNum n) e = f (Map_VAR.add x n (Map_VAR.empty _)) e.
Proof.
  induction e.
  all: simpl.
  - reflexivity.
  - repeat rewrite <- N.MultiSubst.from_subst.
    reflexivity.
  - rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - rewrite IHe.
    reflexivity.
Qed.