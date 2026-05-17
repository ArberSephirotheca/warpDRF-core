From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.U Require Import Lang.

Section Defs.
  Fixpoint f x v i :=
  match i with
  | Skip => Skip
  | If b i j => If (b_subst x v b) (f x v i) (f x v j)
  | Seq i j => Seq (f x v i) (f x v j)
  | MemAcc a => MemAcc (a_subst x v a)
  | For y r i =>
    let i' := if VAR.eq_dec x y then i else f x v i in
    For y (r_subst x v r) i'
  | Decl y i =>
    let i' := if VAR.eq_dec x y then i else f x v i in
    Decl y i'
  end.

  Lemma seq:
    forall x n i1 i2,
    f x n (Seq i1 i2) = Seq (f x n i1) (f x n i2).
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma inv_seq:
    forall x v k i j,
    f x v k = Seq i j ->
    exists i' j',
    k = Seq i' j' /\
    i = f x v i' /\
    j = f x v j'.
  Proof.
    destruct k; simpl; intros i j H; inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma subst_subst_eq:
    forall x i n1 n2,
    f x (NNum n1) (f x (NNum n2) i) = f x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_eq.
      reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite a_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi.
      rewrite r_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHi.
      reflexivity.
  Qed.

  Lemma subst_subst_eq_2
     : forall (x : var) i (v e : nexp),
       ~ NFree x v -> f x e (f x v i) = f x v i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite b_subst_subst_eq_2; auto.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto; rewrite IHi2; auto.
    - rewrite a_subst_subst_eq_2; auto.
    - rewrite r_subst_subst_eq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). { reflexivity. }
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). { reflexivity. }
      rewrite IHi; auto.
  Qed.

  Lemma subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    f x (NNum n1) (f y (NNum n2) i) =
    f y (NNum n2) (f x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_neq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite a_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi; auto.
      rewrite r_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      rewrite IHi; auto.
  Qed.

  Lemma subst_subst_neq_3:
    forall c x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    f x v1 (f y v2 c)
    =
    f y v2 (f x v1 c).
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      rewrite b_subst_subst_neq_3; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_subst_neq_3; auto.
    - rewrite r_subst_subst_neq_3; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          reflexivity.
        }
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      rewrite IHc; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          reflexivity.
        }
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      rewrite IHc; auto.
  Qed.

  Lemma subst_subst_eq_1:
    forall e1 e2 x c,
    f x e1 (f x e2 c) = f x (n_subst x e1 e2) c.
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - erewrite b_subst_subst_eq_1; eauto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_subst_eq_1.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq_1.
        reflexivity.
      }
      rewrite r_subst_subst_eq_1.
      rewrite IHc; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHc; auto.
  Qed.
End Defs.
