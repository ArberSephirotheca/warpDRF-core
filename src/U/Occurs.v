From Faial.Core Require Import Var.
From Faial.Core Require Import Tictac.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.U Require Import Lang.
From Faial.U Require Import Subst.
From Faial.U Require Var.

Section Occurs.
  Fixpoint t (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => NFree x (ae_index e)
    | If b i j => BFree x b \/ t x i \/ t x j
    | Seq i j => t x i \/ t x j
    | For y r i => x = y \/ RFree x r \/ t x i
    | Decl y i => x = y \/ t x i
    end.

  Lemma inv_subst:
    forall y x v i,
    t y (f x v i) ->
    t y i \/ NFree y v.
  Proof.
    induction i; simpl; intros; auto; intuition.
    - rename_hyp (BFree _ _) as hb.
      apply b_free_inv_subst in hb.
      intuition.
    - apply n_free_inv_subst in H.
      intuition.
    - apply r_free_inv_subst in H; intuition.
    - destruct (Set_VAR.MF.eq_dec x v0); auto.
      intuition.
    - destruct (Set_VAR.MF.eq_dec x v0); auto.
      intuition.
  Qed.

  Lemma inv_subst_num:
    forall y x n i,
    t y (f x (NNum n) i) ->
    t y i.
  Proof.
    intros.
    apply inv_subst in H.
    intuition.
    invc H0.
  Qed.

  Lemma inv_subst_eq:
    forall x e c,
    ~ Var.t x c ->
    t x (f x e c) ->
    NFree x e.
  Proof.
    intros.
    induction c; simpl in *; intros; intuition.
    - eauto using b_free_inv_subst_eq.
    - eauto using n_free_inv_subst_eq.
    - eauto using r_free_inv_subst_eq.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradiction.
      }
      auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradiction.
      }
      auto.
  Qed.

  Lemma subst_not_occurs:
    forall x c,
    ~ t x c ->
    forall v,
    f x v c = c.
  Proof.
    induction c; simpl; intros.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      assert (~ B.Exp.BFree x b) by intuition.
      rewrite B.Exp.b_subst_not_free; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_not_free; auto.
    - rewrite IHc; auto.
      rewrite r_subst_not_free; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
    - rewrite IHc; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
  Qed.
End Occurs.
