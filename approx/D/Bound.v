Require Import D.Lang.
Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import RExp.
Require D.Free.
Require D.Subst.

Fixpoint t (x:var) (s:Lang.t) : Prop :=
  match s with
  | Write _ _ | Skip => False
  | Read y _ s | Loop y _ s | Decl y s => (x = y /\ D.Free.t x s) \/ t x s
  | Seq s1 s2 | Cond _ s1 s2 => t x s1 \/ t x s2
  end.

Lemma inv_subst_eq:
  forall s x e,
  t x (Subst.f x e s) ->
  t x s.
Proof.
  induction s.
  all: intros x e wf.
  all: simpl in *.
  all: intuition.
  all: subst.
  all: eauto.
  all: destruct (Set_VAR.MF.eq_dec v v).
  all: intuition.
  all: destruct (Set_VAR.MF.eq_dec x v).
  all: subst.
  all: intuition.
  all: eauto.
Qed.

Lemma not_free_after_subst:
  forall u x e,
  ~ t x u ->
  ~ t x (Subst.f x e u).
Proof.
  intros.
  intros N.
  contradict H.
  eauto using inv_subst_eq.
Qed.
