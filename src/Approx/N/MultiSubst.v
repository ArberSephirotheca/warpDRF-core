From Faial.Approx Require Import NExp.
From Faial.Approx Require Import Var.
From Faial.Approx Require Import Tictac.

Fixpoint f (m:Map_VAR.t nat) (e:nexp) : nexp :=
  match e with
  | NTid
  | NNum _ => e
  | NVar x =>
    match Map_VAR.find x m with
    | Some n => NNum n
    | None => e
    end
  | NBin o e1 e2 => NBin o (f m e1) (f m e2)
  end.

Section Defs.

Lemma subst_eq:
  forall m1 m2,
  Map_VAR.Equal m1 m2 ->
  forall e,
  f m1 e = f m2 e.
Proof.
  induction e.
  all: auto.
  all: simpl.
  - destruct (Map_VAR.find v m1) eqn:eq1. {
      rewrite H in eq1.
      rewrite eq1.
      reflexivity.
    }
    rewrite H in eq1.
    rewrite eq1.
    reflexivity.
  - rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.

Lemma rw_add_not_in:
  forall x n m e,
  ~ Map_VAR.In x m ->
  n_subst x (NNum n) (f m e) = f (Map_VAR.add x n m) e.
Proof.
  induction e.
  all: intros nin.
  all: auto.
  - destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      simpl.
      rewrite find_add_1.
      rewrite not_in_to_find_none; auto.
      rewrite n_subst_eq_rw.
      reflexivity.
    }
    simpl.
    rewrite find_add_2. 2:{ auto. }
    destruct (Map_VAR.find v m). { reflexivity. }
    simpl.
    destruct (Set_VAR.MF.eq_dec x v). { contradiction. }
    reflexivity.
  - simpl.
    rewrite IHe1; auto.
    rewrite IHe2; auto.
Qed.

Lemma rw_closed:
  forall e m,
  NClosed e ->
  f m e = e.
Proof.
  unfold NClosed.
  induction e.
  all: intros m hn.
  all: simpl in *.
  all: auto.
  - specialize (hn v).
    contradiction.
  - rewrite IHe1. 2 :{ intros x N. specialize (hn x). intuition. }
    rewrite IHe2. 2 :{ intros x N. specialize (hn x). intuition. }
    reflexivity.
Qed.

Lemma rw_is_empty:
  forall e m,
  Map_VAR.Empty m ->
  f m e = e.
Proof.
  induction e.
  all: intros m is_e.
  all: simpl.
  all: auto.
  - rewrite not_in_to_find_none; auto using empty_to_not_in.
  - rewrite IHe1; auto.
    rewrite IHe2; auto.
Qed.

Lemma from_subst:
  forall x n e,
  n_subst x (NNum n) e = f (Map_VAR.add x n (Map_VAR.empty _)) e.
Proof.
  induction e.
  all: simpl.
  all: auto.
  - destruct (VAR.eq_dec x v). {
      subst.
      rewrite find_add_1.
      reflexivity.
    }
    rewrite find_add_2; auto.
  - rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.
End Defs.