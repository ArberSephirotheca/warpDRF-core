Require Import D.Lang.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import AExp.
From Faial.Approx Require Import Var.

Fixpoint f x v d :=
  match d with
  | Write i j => Write (n_subst x v i) (n_subst x v j)
  | Read y i j => 
      let i' := n_subst x v i in
      let j' := if VAR.eq_dec x y then j else f x v j in
      Read y i' j'
  | Seq i j => Seq (f x v i) (f x v j)
  | Cond b i j => Cond (b_subst x v b) (f x v i) (f x v j)
  | Loop y r j => 
      let r' := r_subst x v r in
      let j' := if VAR.eq_dec x y then j else f x v j in
      Loop y r' j'
  | Decl y j => 
      let j' := if VAR.eq_dec x y then j else f x v j in
      Decl y j'
  | Skip => d
end.

Lemma subst_subst_neq:
  forall x y s n1 n2,
  x <> y ->
  f x (NNum n1) (f y (NNum n2) s) =
  f y (NNum n2) (f x (NNum n1) s).
Proof.
  induction s.
  all: intros.
  all: simpl.
  - destruct (Set_VAR.MF.eq_dec y v). {
      subst.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradiction.
      }
      rewrite n_subst_subst_neq; auto.
    }
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      rewrite n_subst_subst_neq; auto.
    }
    rewrite IHs; auto.
    f_equal.
    rewrite n_subst_subst_neq; auto.
  - f_equal.
    all: rewrite n_subst_subst_neq.
    all: auto.
  - f_equal; eauto.
  - f_equal; eauto.
    rewrite b_subst_subst_neq.
    all: auto.
  - destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        contradiction.
      }
      f_equal.
      rewrite r_subst_subst_neq.
      all: auto.
    }
    f_equal.
    + rewrite r_subst_subst_neq.
      all: auto.
    + destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      eauto.
  - reflexivity.
  - destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      reflexivity.
    }
    destruct (Set_VAR.MF.eq_dec y v). {
      reflexivity.
    }
    rewrite IHs; auto.
Qed.
