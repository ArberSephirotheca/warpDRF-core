From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.U Require Import Lang.
From Faial.U Require Import Subst.

Section InRange.
  Fixpoint t x i :=
    match i with
    | Skip | MemAcc _ => False
    | If _ i j | Seq i j => t x i \/ t x j
    | For _ r i => RFree x r \/ t x i
    | Decl _ i => t x i
    end.

  Lemma inv_subst:
    forall y x n i,
    t y (f x (NNum n) i) ->
    t y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply r_free_subst_neq in H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.
End InRange.
