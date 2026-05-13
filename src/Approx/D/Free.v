From Faial.Approx Require Import Var.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import RExp.
Require Import D.Lang.
Require R.Free.
Require D.Subst.

Fixpoint t (x:var) (s:t) : Prop :=
  match s with
  | Write idx val => NFree x idx \/ NFree x val
  | Read y idx s =>
    NFree x idx \/
    (x <> y /\ t x s)
  | Seq s1 s2 => t x s1 \/ t x s2
  | Cond b s1 s2 => BFree x b \/ t x s1 \/ t x s2
  | Loop y r s => R.Free.t x r \/ (x <> y /\ t x s)
  | Decl y s => (x <> y /\ t x s)
  | Skip => False
  end.

Lemma inv_subst_eq:
  forall u x e,
  t x (Subst.f x e u) ->
  NFree x e.
Proof.
  induction u.
  all: intros x_orig e_orig hn.
  all: simpl in *.
  all: intuition.
  all: eauto using
    n_free_inv_subst_eq,
    b_free_inv_subst_eq,
    R.Free.inv_subst_eq_2.
  all: destruct (Set_VAR.MF.eq_dec x_orig v).
  all: subst.
  all: auto.
  all: intuition.
Qed.

Lemma not_free_after_subst:
  forall u x e,
  ~ NFree x e ->
  ~ t x (Subst.f x e u).
Proof.
  intros.
  intros N.
  contradict H.
  eauto using inv_subst_eq.
Qed.

