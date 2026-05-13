Require Import D.Lang.
Require D.Subst.
Require N.MultiSubst.
Require B.MultiSubst.
Require A.MultiSubst.
Require R.MultiSubst.
From Faial.Core Require Import Var.
From Faial.Approx Require Import NExp.

Fixpoint f (m:Map_VAR.t nat) (s:Lang.t) : Lang.t :=
  match s with
  | Skip => Skip
  | Cond b u1 u2 => Cond (B.MultiSubst.f m b) (f m u1) (f m u2)
  | Seq u1 u2 => Seq (f m u1) (f m u2)
  | Read x e s => Read x (N.MultiSubst.f m e) (f (Map_VAR.remove x m) s)
  | Write idx e => Write (N.MultiSubst.f m idx) (N.MultiSubst.f m e)
  | Loop x r u => Loop x (R.MultiSubst.f m r) (f (Map_VAR.remove x m) u)
  | Decl x u => Decl x (f (Map_VAR.remove x m) u)
  end.

Lemma subst_eq:
  forall u m1 m2,
  Map_VAR.Equal m1 m2 ->
  f m1 u = f m2 u.
Proof.
  induction u.
  all: intros m1 m2 Heq.
  all: simpl.
  - rewrite (IHu (Map_VAR.remove v m1) (Map_VAR.remove v m2)).
    + f_equal.
      eauto using N.MultiSubst.subst_eq.
    + rewrite Heq.
      reflexivity.
  - f_equal.
    all: eauto using N.MultiSubst.subst_eq.
  - rewrite (IHu1 m1 m2 Heq).
    rewrite (IHu2 m1 m2 Heq).
    reflexivity.
  - rewrite (IHu1 m1 m2 Heq).
    rewrite (IHu2 m1 m2 Heq).
    f_equal.
    eauto using B.MultiSubst.subst_eq.
  - f_equal.
    + eauto using R.MultiSubst.subst_eq.
    + rewrite (IHu (Map_VAR.remove v m1) (Map_VAR.remove v m2)).
      * reflexivity.
      * rewrite Heq.
        reflexivity.
  - reflexivity.
  - f_equal.
    rewrite (IHu (Map_VAR.remove v m1) (Map_VAR.remove v m2)).
    + reflexivity.
    + rewrite Heq.
      reflexivity.
Qed.

Lemma rw_add_not_in:
  forall e x m,
  ~ Map_VAR.In x m ->
  forall n,
  Subst.f x (NNum n) (f m e) = f (Map_VAR.add x n m) e.
Proof.
  induction e.
  all: intros x m Hi n_val.
  all: simpl.
  all: f_equal.
  all: try (rewrite N.MultiSubst.rw_add_not_in; auto).
  all: try (rewrite B.MultiSubst.rw_add_not_in; auto).
  all: auto.
  - destruct (VAR.eq_dec x v). {
      subst.
      apply subst_eq.
      symmetry.
      apply rw_remove_add_eq.
    }
    rewrite IHe.
    + apply subst_eq.
      symmetry.
      rewrite rw_add_remove_neq. 2: { assumption. }
      reflexivity.
    + intros N.
      contradict Hi.
      eauto using in_remove_3.
  - rewrite R.MultiSubst.rw_add_not_in; auto.
  - destruct (VAR.eq_dec x v). {
      apply subst_eq.
      subst.
      rewrite rw_remove_add_eq.
      reflexivity.
    }
    rewrite IHe.
    + apply subst_eq.
      symmetry.
      rewrite rw_add_remove_neq. 2: { assumption. }
      reflexivity.
    + intros N.
      contradict Hi.
      eauto using in_remove_3.
  - destruct (VAR.eq_dec x v). {
      subst.
      apply subst_eq.
      rewrite rw_remove_add_eq.
      reflexivity.
    }
    rewrite IHe.
    + apply subst_eq.
      symmetry.
      rewrite rw_add_remove_neq. 2: { assumption. }
      reflexivity.
    + intros N.
      contradict Hi.
      eauto using in_remove_3.
Qed.

Lemma rw_is_empty:
  forall s m,
  Map_VAR.Empty m ->
  f m s = s.
Proof.
  induction s.
  all: intros m is_empty.
  all: simpl.
  all: f_equal.
  all: auto using N.MultiSubst.rw_is_empty, B.MultiSubst.rw_is_empty, R.MultiSubst.rw_is_empty, empty_to_empty_remove.
Qed.