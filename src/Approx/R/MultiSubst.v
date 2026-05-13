From Faial.Approx Require Import NExp.
From Faial.Approx Require Import RExp.
Require N.MultiSubst.
From Faial.Approx Require Import Var.
Require R.Closed.

Definition f (m:Map_VAR.t nat) (r:range) : range :=
  let (e1, e2) := r in
  (N.MultiSubst.f m e1, N.MultiSubst.f m e2).

Lemma rw_add_not_in:
  forall x n m e,
  ~ Map_VAR.In x m ->
  r_subst x (NNum n) (f m e) = f (Map_VAR.add x n m) e.
Proof.
  intros.
  destruct e as (a, b).
  unfold r_subst.
  simpl.
  f_equal.
  all: auto using N.MultiSubst.rw_add_not_in.
Qed.

Lemma subst_eq:
  forall m1 m2,
  Map_VAR.Equal m1 m2 ->
  forall e,
  f m1 e = f m2 e.
Proof.
  intros.
  destruct e as (e1, e2).
  simpl.
  f_equal.
  all: erewrite N.MultiSubst.subst_eq; eauto.
Qed.

Lemma rw_closed:
  forall e m,
  R.Closed.t e ->
  f m e = e.
Proof.
  intros (e1, e2) m hr.
  simpl in *.
  apply R.Closed.inv in hr.
  destruct hr as (ha, hb).
  repeat rewrite N.MultiSubst.rw_closed; auto.
Qed.

Lemma rw_is_empty:
  forall e m,
  Map_VAR.Empty m ->
  f m e = e.
Proof.
  intros (e1, e2) m is_e.
  simpl.
  repeat rewrite N.MultiSubst.rw_is_empty; auto. 
Qed.

Lemma from_subst:
  forall x n e,
  r_subst x (NNum n) e = f (Map_VAR.add x n (Map_VAR.empty _)) e.
Proof.
  intros x n (e1, e2).
  simpl.
  repeat rewrite N.MultiSubst.from_subst.
  reflexivity.
Qed.
