From Faial.Core Require Import Var.
From Faial.Core Require Import Tictac.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.

Section Defs.
  Fixpoint Occurs (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => NFree x (ae_index e)
    | If b i j => BFree x b \/ Occurs x i \/ Occurs x j
    | Seq i j => Occurs x i \/ Occurs x j
    | For y r i => x = y \/ RFree x r \/ Occurs x i
    end.

  Fixpoint Free (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => NFree x (ae_index e)
    | If b i j => BFree x b \/ Free x i \/ Free x j
    | Seq i j => Free x i \/ Free x j
    | For y r i => RFree x r \/ (x <> y /\ Free x i)
    end.

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => Var x i \/ Var x j
  | For y _ i => x = y \/ Var x i
  end.

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => InRange x i \/ InRange x j
  | For _ r i => RFree x r \/ InRange x i
  end.

  Lemma var_inv_subst:
    forall y x e i,
    Var y (i_subst x e i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; intuition.
    destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma var_subst:
    forall i x y,
    x <> y ->
    Var y i ->
    forall e,
    Var y (i_subst x e i).
  Proof.
    induction i; simpl; auto; intros.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]; eauto.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]; eauto.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]. {
        subst.
        auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        auto.
      }
      auto.
  Qed.

  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply r_free_subst_neq in H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma occurs_inv_subst:
    forall y x v i,
    Occurs y (i_subst x v i) ->
    Occurs y i \/ NFree y v.
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
  Qed.

  Lemma occurs_inv_subst_num:
    forall y x n i,
    Occurs y (i_subst x (NNum n) i) ->
    Occurs y i.
  Proof.
    intros.
    apply occurs_inv_subst in H.
    intuition.
    invc H0.
  Qed.

  Lemma occurs_inv_subst_eq:
    forall x e c,
    ~ Var x c ->
    Occurs x (i_subst x e c) ->
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
  Qed.

  Lemma i_subst_not_occurs:
    forall x c,
    ~ Occurs x c ->
    forall v,
    i_subst x v c = c.
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
  Qed.

  Lemma i_subst_not_free:
    forall x c,
    ~ Free x c ->
    forall v,
    i_subst x v c = c.
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
    - rewrite r_subst_not_free; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
  Qed.

  Lemma i_subst_subst_neq_5:
    forall c x y e1 e2,
    NClosed e1 ->
    y <> x ->
    ~ Var y c ->
    i_subst y e1 (i_subst x e2 c) =
    i_subst x (n_subst y e1 e2) (i_subst y e1 c).
  Proof.
    induction c; intros; simpl in *.
    - reflexivity.
    - rewrite b_subst_subst_neq_5; auto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_subst_neq_5; auto.
    - rename v into z.
      rewrite <- r_subst_subst_neq_5; auto.
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        intuition.
      }
      destruct (Set_VAR.MF.eq_dec x z). {
        subst.
        intuition.
      }
      rewrite IHc; auto.
  Qed.
End Defs.
