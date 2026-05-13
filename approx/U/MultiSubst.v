Require Import Var.
Require Import U.Lang.
Require N.MultiSubst.
Require B.MultiSubst.
Require A.MultiSubst.
Require R.MultiSubst.
Require Import NExp.
Require U.Subst.

Fixpoint f (m:Map_VAR.t nat) (u:Lang.t) : Lang.t :=
  match u with
  | Skip => Skip
  | If b u1 u2 => If (B.MultiSubst.f m b) (f m u1) (f m u2)
  | Seq u1 u2 => Seq (f m u1) (f m u2)
  | MemAcc a => MemAcc (A.MultiSubst.f m a)
  | For x r u => For x (R.MultiSubst.f m r) (f (Map_VAR.remove x m) u)
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
  - reflexivity.
  - rewrite (IHu1 m1 m2 Heq).
    rewrite (IHu2 m1 m2 Heq).
    f_equal.
    eauto using B.MultiSubst.subst_eq.
  - rewrite (IHu1 m1 m2 Heq).
    rewrite (IHu2 m1 m2 Heq).
    auto.
  - f_equal.
    eauto using A.MultiSubst.subst_eq.
  - f_equal.
    + eauto using R.MultiSubst.subst_eq.
    + rewrite (IHu (Map_VAR.remove v m1) (Map_VAR.remove v m2)).
      * reflexivity.
      * rewrite Heq.
        reflexivity.
  - f_equal.
    rewrite (IHu (Map_VAR.remove v m1) (Map_VAR.remove v m2)).
    + reflexivity.
    + rewrite Heq.
      reflexivity.
Qed.

Lemma subst_to_add:
  forall u x n m,
  ~ Map_VAR.In x m ->
  Subst.f x (NNum n) (f m u) = f (Map_VAR.add x n m) u.
Proof.
  induction u.
  all: intros x n m nin.
  all: simpl.
  - reflexivity.
  - rewrite IHu1; auto.
    rewrite IHu2; auto.
    f_equal.
    rewrite B.MultiSubst.rw_add_not_in; auto.
  - rewrite IHu1; auto.
    rewrite IHu2; auto.
  - rewrite A.MultiSubst.rw_add_not_in; auto.
  - rewrite R.MultiSubst.rw_add_not_in; auto.
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      f_equal.
      erewrite subst_eq; eauto.
      rewrite rw_remove_add_eq.
      reflexivity.
    }
    f_equal.
    assert (IHu := IHu x n (Map_VAR.remove (elt:=nat) v m)).
    rewrite IHu.
    + apply subst_eq.
      rewrite rw_add_remove_neq; auto.
      reflexivity.
    + intros N.
      contradict nin.
      eauto using Map_VAR_Extra.remove_in.
  - destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      f_equal.
      apply subst_eq.
      rewrite rw_remove_add_eq.
      reflexivity.
    }
    f_equal.
    assert (IHu := IHu x n (Map_VAR.remove (elt:=nat) v m)).
    rewrite IHu.
    + apply subst_eq.
      rewrite rw_add_remove_neq; auto.
      reflexivity.
    + intros N.
      contradict nin.
      eauto using Map_VAR_Extra.remove_in.
Qed.

Lemma rw_is_empty:
  forall u m,
  Map_VAR.Empty m ->
  f m u = u.
Proof.
  induction u.
  all: intros m empty.
  all: simpl.
  - reflexivity.
  - rewrite IHu1; auto.
    rewrite IHu2; auto.
    rewrite B.MultiSubst.rw_is_empty; auto.
  - rewrite IHu1; auto.
    rewrite IHu2; auto.
  - rewrite A.MultiSubst.rw_is_empty; auto.
  - rewrite R.MultiSubst.rw_is_empty; auto.
    f_equal.
    rewrite IHu; auto using empty_to_empty_remove.
  - f_equal.
    rewrite IHu; auto using empty_to_empty_remove.
Qed.

Lemma rw_empty:
  forall u,
  f (Map_VAR.empty _) u = u.
Proof.
  intros.
  apply rw_is_empty, Map_VAR.empty_1.
Qed.

Lemma from_subst:
  forall u x n,
  Subst.f x (NNum n) u = f (Map_VAR.add x n (Map_VAR.empty _)) u.
Proof.
  induction u.
  all: intros x_orig n_orig.
  all: simpl.
  all: repeat rewrite B.MultiSubst.from_subst.
  all: repeat rewrite A.MultiSubst.from_subst.
  all: repeat rewrite R.MultiSubst.from_subst.
  all: f_equal.
  all: auto.
  - destruct (VAR.eq_dec x_orig v). {
      subst.
      assert (rw1: f (Map_VAR.remove (elt:=nat) v (Map_VAR.add v n_orig (Map_VAR.empty nat))) u =
        f (Map_VAR.empty nat) u). {
        apply subst_eq.
        rewrite rw_remove_add_eq.
        rewrite rw_remove_empty.
        reflexivity.
      }
      rewrite rw1.
      rewrite rw_empty.
      reflexivity.
    }
    rewrite IHu.
    apply subst_eq.
    rewrite <- rw_add_remove_neq; auto.
    rewrite rw_remove_empty.
    reflexivity.
  - destruct (VAR.eq_dec x_orig v). {
      subst.
      assert (rw1: f (Map_VAR.remove (elt:=nat) v (Map_VAR.add v n_orig (Map_VAR.empty nat))) u
        = f (Map_VAR.empty nat) u). {
        apply subst_eq.
        rewrite rw_remove_add_eq.
        rewrite rw_remove_empty.
        reflexivity.
      }
      rewrite rw1.
      rewrite rw_empty.
      reflexivity.
    }
    rewrite IHu.
    apply subst_eq.
    rewrite <- rw_add_remove_neq; auto.
    rewrite rw_remove_empty.
    reflexivity.
Qed.
