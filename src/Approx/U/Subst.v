From Faial.Approx Require Import Var.
Require Import U.Lang.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import AExp.
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
      rewrite r_subst_subst_neq; auto.
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      rewrite IHi; auto.
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

End Defs.