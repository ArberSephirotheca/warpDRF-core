From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.

Section Free.
  Fixpoint t (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => NFree x (ae_index e)
    | If b i j => BFree x b \/ t x i \/ t x j
    | Seq i j => t x i \/ t x j
    | For y r i => RFree x r \/ (x <> y /\ t x i)
    | Decl y i => x <> y /\ t x i
    end.

  Lemma subst_not_free:
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
    - rewrite r_subst_not_free; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
    - destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
  Qed.
End Free.
