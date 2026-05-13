Require U.Free.
From Faial.Core Require Import Var.
Require Import U.Lang.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Core Require Import Tictac.
Require U.Subst.

Fixpoint t (x:var) (u:Lang.t) : Prop :=
  match u with
  | MemAcc _ | Skip => False
  | For y _ s | Decl y s => (x = y /\ U.Free.t x s) \/ t x s
  | Seq s1 s2 | If _ s1 s2 => t x s1 \/ t x s2
  end.

Section Defs.

Let inv_subst_eq:
  forall u x e,
  t x (Subst.f x e u) ->
  t x u.
Proof.
  induction u.
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


Let inv_subst_neq:
  forall u x y n,
  t x (Subst.f y (NNum n) u) ->
  x <> y ->
  t x u.
Proof.
  induction u.
  all: intros x y n Hb neq.
  all: simpl in *.
  all: intuition.
  all: eauto.
  all: destruct (Set_VAR.MF.eq_dec y v).
  all: subst.
  all: intuition.
  all: eauto.
  - rename_hyp (Free.t _ _) as hf.
    apply Free.inv_subst in hf.
    simpl in *.
    intuition.
  - rename_hyp (Free.t _ _) as hf.
    apply Free.inv_subst in hf.
    simpl in *.
    intuition.
Qed.

Lemma inv_subst:
  forall u x y n,
  t x (Subst.f y (NNum n) u) ->
  t x u.
Proof.
  intros.
  destruct (Set_VAR.MF.eq_dec x y). { subst. eauto using inv_subst_eq. }
  eauto using inv_subst_neq.
Qed.
End Defs.