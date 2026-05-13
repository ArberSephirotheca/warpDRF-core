From Faial.Approx Require Import Var.
Require Import U.Lang.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import AExp.
From Faial.Approx Require Import Tictac.
Require R.Free.
Require U.Subst.

Section Free.
  Fixpoint t (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => NFree x (ae_index e)
    | If b i j => BFree x b \/ t x i \/ t x j
    | Seq i j => t x i \/ t x j
    | For y r i => R.Free.t x r \/ (x <> y /\ t x i)
    | Decl y i => (x <> y /\ t x i)
    end.

  Lemma inv_subst:
    forall u x y e,
    t x (Subst.f y e u) ->
    NExp.NFree x e \/ t x u.
  Proof.
    induction u.
    all: simpl.
    all: intros x_orig y_orig e_orig hf.
    all: intuition.
    - rename_hyp (BFree _ _ ) as hb.
      apply b_free_inv_subst in hb.
      intuition.
    - rename_hyp (t _ _) as hf.
      apply IHu1 in hf.
      intuition.
    - rename_hyp (t _ _) as hf.
      apply IHu2 in hf.
      intuition.
    - rename_hyp (t _ _) as hf.
      apply IHu1 in hf.
      intuition.
    - rename_hyp (t _ _) as hf.
      apply IHu2 in hf.
      intuition.
    - destruct a as (e1, e2).
      simpl in *.
      eauto using n_free_inv_subst.
    - rename_hyp (R.Free.t _ _) as hf.
      apply R.Free.inv_subst in hf.
      intuition.
    - destruct (Set_VAR.MF.eq_dec y_orig v). {
        subst.
        intuition.
      }
      rename_hyp (t _ _) as hf.
      apply IHu in hf.
      intuition.
    - destruct (Set_VAR.MF.eq_dec y_orig v). {
        subst.
        intuition.
      }
      rename_hyp (t _ _) as hf.
      apply IHu in hf.
      intuition.
  Qed.

  Lemma i_subst_not_free:
    forall x c,
    ~ t x c ->
    forall v,
    Subst.f x v c = c.
  Proof.
    induction c; simpl; intros.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      assert (~ BExp.BFree x b) by intuition.
      rewrite BExp.b_subst_not_free; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_not_free; auto.
    - rewrite R.Free.subst; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
    - destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
  Qed.

  Lemma not_free_after_subst:
    forall u x e,
    ~ NFree x e ->
    ~ t x (Subst.f x e u).
  Proof.
    induction u.
    all: intros x_orig e_orig hn.
    all: simpl.
    all: intuition.
    all: eauto.
    - rename_hyp (BFree _ _) as hb.
      apply BExp.not_free_after_subst in hb.
      all: intuition.
    - rename_hyp (NFree _ _) as hb.
      apply NExp.not_free_after_subst in hb.
      all: intuition.
    - rename_hyp (R.Free.t _ _) as hb.
      apply R.Free.not_free_after_subst in hb.
      all: intuition.
    - destruct (Set_VAR.MF.eq_dec x_orig v). {
        subst.
        contradiction.
      }
      eauto.
    - destruct (Set_VAR.MF.eq_dec x_orig v). {
        subst.
        contradiction.
      }
      eauto.
  Qed.

End Free.