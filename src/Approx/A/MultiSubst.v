From Faial.Approx Require Import AExp.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Var.
Require N.MultiSubst.

Definition f (m:Map_VAR.t nat) (a:access_exp) : access_exp :=
  match a with
  | {| ae_index := e; ae_mode := o |} =>
    {| ae_index := N.MultiSubst.f m e; ae_mode := o |}
  end.

Lemma rw_add_not_in:
  forall x n m e,
  ~ Map_VAR.In x m ->
  a_subst x (NNum n) (f m e) = f (Map_VAR.add x n m) e.
Proof.
  intros.
  destruct e as (a, b).
  unfold a_subst.
  simpl.
  f_equal.
  auto using N.MultiSubst.rw_add_not_in.
Qed.

Lemma subst_eq:
  forall m1 m2,
  Map_VAR.Equal m1 m2 ->
  forall e,
  f m1 e = f m2 e.
Proof.
  intros.
  destruct e as (a, b).
  unfold a_subst.
  simpl.
  f_equal.
  eauto using N.MultiSubst.subst_eq.
Qed.

Lemma rw_is_empty:
  forall e m,
  Map_VAR.Empty m ->
  f m e = e.
Proof.
  intros (a, b) m is_e.
  simpl.
  f_equal.
  auto using N.MultiSubst.rw_is_empty; auto.
Qed.

Lemma eq_mode:
  forall m1 m2 a,
  ae_mode (f m1 a) = ae_mode (f m2 a).
Proof.
  intros m1 m2 (e, o).
  reflexivity.
Qed.

Lemma from_subst:
  forall x n e,
  a_subst x (NNum n) e = f (Map_VAR.add x n (Map_VAR.empty _)) e.
Proof.
  intros.
  destruct e as (a, b).
  simpl in *.
  unfold a_subst.
  f_equal.
  rewrite N.MultiSubst.from_subst.
  reflexivity.
Qed.