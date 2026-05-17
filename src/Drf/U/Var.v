From Faial.Core Require Import Var.
From Faial.Core Require Import Tictac.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.

Section Var.
  Fixpoint t x i :=
    match i with
    | Skip | MemAcc _ => False
    | If _ i j | Seq i j => t x i \/ t x j
    | For y _ i | Decl y i => x = y \/ t x i
    end.

  Lemma inv_subst:
    forall y x e i,
    t y (f x e i) ->
    t y i.
  Proof.
    induction i; simpl; intros; auto; intuition.
    all: destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma subst:
    forall i x y,
    x <> y ->
    t y i ->
    forall e,
    t y (f x e i).
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

  Lemma subst_neq_5:
    forall c x y e1 e2,
    NClosed e1 ->
    y <> x ->
    ~ t y c ->
    f y e1 (f x e2 c) =
    f x (n_subst y e1 e2) (f y e1 c).
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
    - rename v into z.
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
End Var.
