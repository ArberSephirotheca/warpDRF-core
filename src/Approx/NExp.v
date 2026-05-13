From Stdlib Require Import Lists.List.
Import ListNotations.

From Faial.Approx Require Import Var.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationPairs.
From Faial.Approx Require Import Tictac.
From Faial.Approx Require Import InUtil.

Section Defs.

  Inductive nbin :=
  | NPlus
  | NMinus
  | NMult
  | NDiv
  | NMod.

  Inductive nexp :=
  | NNum : nat -> nexp
  | NTid : nexp
  | NVar : var -> nexp
  | NBin : nbin ->  nexp -> nexp -> nexp.

End Defs.

Section SO.

  Definition eval_nbin o :=
    match o with
    | NPlus => Nat.add
    | NMinus => Nat.sub
    | NMult => Nat.mul
    | NDiv => Nat.div
    | NMod => Nat.modulo
    end.

  Variable tid: nat.

  Inductive NStep : nexp -> nat -> Prop :=
  | n_step_num:
    forall m,
    NStep (NNum m) m
  | n_step_tid:
    NStep NTid tid
  | n_step_bin:
    forall n1 n2 o e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin o e1 e2) (eval_nbin o n1 n2). 

  Fixpoint n_subst x v e :=
    match e with
    | NBin o e1 e2 => NBin o (n_subst x v e1) (n_subst x v e2)
    | NVar y => if VAR.eq_dec x y then v else e  
    | NNum n => NNum n
    | NTid => NTid
    end.

  Lemma n_step_subst_next:
    forall x a n1 n2,
    NStep (n_subst x (NNum n1) a) n2 ->
    forall m1, exists m2, NStep (n_subst x (NNum m1) a) m2.
  Proof.
    induction a; simpl; intros.
    - exists n.
      constructor.
    - exists tid.
      constructor.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        exists m1.
        constructor.
      }
      exists n2.
      assumption.
    - inversion H; subst; clear H.
      assert (Ha1 := IHa1 _ _ H4 m1).
      assert (Ha2 := IHa2 _ _ H5 m1).
      destruct Ha1 as (ma1, Ha1).
      destruct Ha2 as (ma2, Ha2).
      exists (eval_nbin n ma1 ma2).
      constructor; auto.
  Qed.

  Fixpoint n_step (e:nexp) : option nat :=
    match e with
    | NNum n => Some n
    | NBin o e1 e2 =>
      match n_step e1, n_step e2 with
      | Some n1, Some n2 => Some (eval_nbin o n1 n2)
      | _ , _ => None
      end
    | NVar _ => None
    | NTid => Some tid
    end.

  Lemma n_step_to_prop:
    forall e n,
    n_step e = Some n ->
    NStep e n.
  Proof.
    induction e; intros; simpl in *; inversion H; subst; clear H.
    - constructor.
    - constructor.
    - destruct (n_step e1). {
        destruct (n_step e2);
           inversion H1; subst; clear H1.
        constructor; eauto.
      }
      inversion H1.
  Qed.

  Lemma prop_to_n_step:
    forall e n,
    NStep e n ->
    n_step e = Some n.
  Proof.
    induction e; intros; inversion H; subst; clear H.
    - reflexivity.
    - reflexivity.
    - apply IHe1 in H4.
      apply IHe2 in H5.
      simpl.
      rewrite H4.
      rewrite H5.
      reflexivity.
  Qed.

  Lemma n_step_fun:
    forall n n1 n2,
    NStep n n1 ->
    NStep n n2 ->
    n1 = n2.
  Proof.
    intros.
    apply prop_to_n_step in H.
    apply prop_to_n_step in H0.
    rewrite H in *.
    inversion H0.
    auto.
  Qed.

  Lemma add_inv_n_0:
    forall n1 n2, NStep (NBin NPlus (NNum n1) (NNum 0)) n2 ->
    n1 = n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst; clear H5.
    inversion H4; subst; clear H4.
    simpl.
    apply plus_n_O.
  Qed.

  Lemma n_step_plus:
    forall n1 n2 e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin NPlus e1 e2) (n1 + n2).
  Proof.
    intros.
    assert (NStep (NBin NPlus e1 e2) (eval_nbin NPlus n1 n2))
      by auto using n_step_bin.
    unfold eval_nbin in *.
    assumption.
  Qed.

  Lemma n_step_minus:
    forall n1 n2 e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin NMinus e1 e2) (n1 - n2).
  Proof.
    intros.
    assert (NStep (NBin NMinus e1 e2) (eval_nbin NMinus n1 n2))
      by auto using n_step_bin.
    unfold eval_nbin in *.
    assumption.
  Qed.

  Lemma n_step_add_eq:
    forall n1 n2 n3 e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 + n2 = n3 ->
    NStep (NBin NPlus e1 e2) n3.
  Proof.
    intros.
    subst.
    auto using n_step_plus.
  Qed.

  Lemma n_step_minus_eq:
    forall n1 n2 n3 e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 - n2 = n3 ->
    NStep (NBin NMinus e1 e2) n3.
  Proof.
    intros.
    subst.
    auto using n_step_minus.
  Qed.

  Lemma n_step_add:
    forall n1 n2 e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin NPlus e1 e2) (n1 + n2).
  Proof.
    apply n_step_plus.
  Qed.

  Lemma n_step_inv_plus:
    forall e1 e2 n,
    NStep (NBin NPlus e1 e2) n ->
    exists n1 n2, n = n1 + n2 /\ NStep e1 n1 /\ NStep e2 n2.
  Proof.
    destruct e1; intros; inversion H; subst; clear H.
    all: simpl.
    all: eauto.
  Qed.

  Lemma n_step_plus_num:
    forall n1 n2,
    NStep (NBin NPlus (NNum n1) (NNum n2)) (n1 + n2).
  Proof.
    auto using n_step_plus, n_step_num.
  Qed.

  Lemma n_step_add_num:
    forall n1 n2,
    NStep (NBin NPlus (NNum n1) (NNum n2)) (n1 + n2).
  Proof.
    apply n_step_plus_num.
  Qed.

  Lemma n_step_inv_plus_num:
    forall n1 n2 n3,
    NStep (NBin NPlus (NNum n1) (NNum n2)) n3 ->
    n3 = n1 + n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold eval_nbin.
    inversion H4; subst; clear H4.
    inversion H5; subst; clear H5.
    reflexivity.
  Qed.

  Lemma n_step_inv_nbin:
    forall o e1 e2 n,
    NStep (NBin o e1 e2) n ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    n = eval_nbin o n1 n2.
  Proof.
    intros.
    invc H.
    exists n1.
    exists n2.
    auto.
  Qed.

  Lemma n_step_inv_add_num:
    forall n1 n2 n3,
    NStep (NBin NPlus (NNum n1) (NNum n2)) n3 ->
    n3 = n1 + n2.
  Proof.
    auto using n_step_inv_plus_num. 
  Qed.

  Lemma n_step_add_n_0:
    forall n, NStep (NBin NPlus (NNum n) (NNum 0)) n.
  Proof.
    intros.
    rewrite <- PeanoNat.Nat.add_0_r.
    apply n_step_plus_num.
  Qed.

  Lemma n_step_inv_add_n_0:
    forall n1 n2,
    NStep (NBin NPlus (NNum n1) (NNum 0)) n2 ->
    n1 = n2.
  Proof.
    intros.
    assert (Hx := n_step_add_n_0 n1).
    eauto using n_step_fun.
  Qed.

  Lemma n_step_add_0_n:
    forall e1 e2 n,
    NStep (NBin NPlus e1 e2) n ->
    NStep (NBin NPlus e1 (NBin NPlus (NNum 0) e2)) n.
  Proof.
    intros.
    inversion H; subst.
    simpl in *.
    apply n_step_add; auto.
    assert (NStep (NBin NPlus (NNum 0) e2) (0 + n2)). {
      apply n_step_add; auto using n_step_num.
    }
    simpl in *.
    assumption.
  Qed.

  Fixpoint NFree (x:var) (e: nexp) : Prop := 
    match e with
    | NVar y => y = x
    | NBin _ e1 e2 => NFree x e1 \/ NFree x e2
    | NNum _ | NTid => False
    end.

  Lemma n_subst_not_free:
    forall x v n,
    ~ NFree x n ->
    n_subst x v n = n.
  Proof.
    induction n; intros.
    - reflexivity.
    - reflexivity.
    - simpl in *.
      destruct (Set_VAR.MF.eq_dec x v0). {
        subst.
        contradiction.
      }
      reflexivity.
    - simpl in *.
      rewrite IHn1; auto.
      rewrite IHn2; auto.
  Qed.

  Lemma n_free_inv_subst_eq:
    forall x e n,
    NFree x (n_subst x e n) ->
    NFree x e.
  Proof.
    induction n; intros; simpl in *.
    - invc H.
    - invc H.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assumption.
      }
      invc H.
      contradiction.
    - invc H; auto.
  Qed.

  Lemma n_subst_to_not_free:
    forall x v n1 n2,
    n_subst x (NNum v) n1 = n2 ->
    ~ NFree x n2.
  Proof.
    intros.
    intros N.
    rewrite <- H in N.
    apply n_free_inv_subst_eq in N.
    simpl in *.
    assumption.
  Qed.

  Lemma n_subst_subst_eq_2:
    forall x n v e,
    ~ NFree x v ->
    n_subst x e (n_subst x v n) = n_subst x v n.
  Proof.
    intros.
    rewrite n_subst_not_free; auto.
    intros N.
    apply n_free_inv_subst_eq in N.
    contradiction.
  Qed.

  Lemma n_free_subst_neq:
    forall e x y v,
    NFree x (n_subst y v e) ->
    ~ NFree x v ->
    NFree x e.
  Proof.
    induction e; simpl; intros; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        contradiction.
      }
      auto.
    - destruct H; eauto.
  Qed.

  Lemma n_free_inv_subst:
    forall e x y v,
    NFree x (n_subst y v e) ->
    NFree x v \/ NFree x e.
  Proof.
    induction e; simpl; intros; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        auto.
      }
      simpl in *.
      auto.
    - intuition.
      + apply IHe1 in H0; intuition.
      + apply IHe2 in H0; intuition.
  Qed.


  Lemma n_free_subst_eq:
    forall x y e,
    ~ NFree x e ->
    NFree x (n_subst y (NVar x) e) ->
    NFree y e.
  Proof.
    induction e; simpl; intros.
    - contradiction.
    - contradiction.
    - destruct (Set_VAR.MF.eq_dec y v); auto.
      simpl in *.
      subst.
      contradiction.
    - destruct H0.
      + left.
        eauto.
      + right.
        eauto.
  Qed.

  Lemma n_subst_subst_neq_2:
    forall x y z n e,
    y <> z ->
    x <> z ->
    n_subst x (NVar y) (n_subst z (NNum n) e)
    =
    n_subst z (NNum n) (n_subst x (NVar y) e).
  Proof.
    induction e; intros.
    - reflexivity.
    - reflexivity.
    - (* variable v *)
      simpl.
      destruct (Set_VAR.MF.eq_dec z v). {
        (* z = v *)
        destruct (Set_VAR.MF.eq_dec x v). {
          (* x = v *)
          subst.
          contradiction.
        }
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]. {
          reflexivity.
        }
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec v v). {
          destruct (Set_VAR.MF.eq_dec z y). {
            subst.
            contradiction.
          }
          reflexivity.
        }
        contradiction.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec z v). {
        subst.
        contradiction.
      }
      reflexivity.
    - simpl.
      rewrite IHe1; auto.
      rewrite IHe2; auto.
  Qed.

  Lemma n_subst_subst_neq_3:
    forall e x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    n_subst x v1 (n_subst y v2 e)
    =
    n_subst y v2 (n_subst x v1 e).
  Proof.
    induction e; intros; simpl; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        destruct (Set_VAR.MF.eq_dec x v). {
          subst.
          contradiction.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec v v) as [_|N]; try contradiction.
        rewrite n_subst_not_free; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec v v) as [_|N]; try contradiction.
        rewrite n_subst_not_free; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        contradiction.
      }
      reflexivity.
    - rewrite IHe1; auto.
      rewrite IHe2; auto.
  Qed.

  Lemma not_free_after_subst:
    forall e x v,
    ~ NFree x v ->
    ~ NFree x (n_subst x v e).
  Proof.
    induction e; intros x_orig v_orig hn.
    all: intuition.
    all: simpl in *.
    - destruct (Set_VAR.MF.eq_dec x_orig v). {
        subst.
        contradiction.
      }
      simpl in *.
      subst.
      contradiction.
    - rename_hyp (_ \/ _) as N.
      destruct N as [N|N].
      + eapply IHe1; eauto.
      + eapply IHe2; eauto.
  Qed.

  (* TODO: remove me and replace it by n_subst_subst_eq_2 *)
  Lemma n_subst_subst_eq:
    forall x n n1 n2,
    n_subst x (NNum n1) (n_subst x (NNum n2) n) = n_subst x (NNum n2) n.
  Proof.
    induction n; intros; simpl.
    - reflexivity.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        reflexivity.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      reflexivity.
    - assert (IHn1 := IHn1 n0 n4).
      rewrite IHn1.
      assert (IHn2 := IHn2 n0 n4).
      rewrite IHn2.
      reflexivity.
  Qed.

  Lemma n_subst_subst_neq:
    forall x y n n1 n2,
    x <> y ->
    n_subst x (NNum n1) (n_subst y (NNum n2) n) =
    n_subst y (NNum n2) (n_subst x (NNum n1) n).
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec x v). {
          contradiction.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec v v). {
          reflexivity.
        }
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec v v). {
          reflexivity.
        }
        contradiction.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        contradiction.
      }
      reflexivity.
    - rewrite IHn1; auto.
      rewrite IHn2; auto.
  Qed.

  Lemma n_subst_subst_trans:
    forall e x v y,
    ~ NFree x e ->
    n_subst x v (n_subst y (NVar x) e) = n_subst y v e.
  Proof.
    induction e; simpl; intros.
    - reflexivity.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec x x). {
          reflexivity.
        }
        contradiction.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradict H.
        reflexivity.
      }
      reflexivity.
    - simpl in *.
      rewrite IHe1; auto.
      rewrite IHe2; auto.
  Qed.

  Lemma n_step_inv_subst:
    forall x v e n,
    NStep (n_subst x v e) n ->
    ~ NFree x e \/ exists n', NStep v n'.
  Proof.
    induction e; intros; simpl in *.
    - left.
      intros N.
      inversion N.
    - inversion H; subst; clear H.
      intuition.
    - destruct (Set_VAR.MF.eq_dec x v0). {
        eauto.
      }
      inversion H.
    - inversion H; subst; clear H.
      apply IHe1 in H4.
      apply IHe2 in H5.
      destruct H4, H5; auto.
      left.
      intros N.
      inversion N; subst; clear N; contradiction.
  Qed.

  Lemma n_step_to_not_free:
    forall e n,
    NStep e n ->
    forall x,
    ~ NFree x e.
  Proof.
    intros e n H.
    induction H; intros; intros N; inversion N; subst; clear N.
    - apply IHNStep1 in H1.
      auto.
    - apply IHNStep2 in H1; auto.
  Qed.

  Inductive IStep: list nexp -> list nat -> Prop :=
  | i_step_nil:
    IStep [] []
  | i_step_cons:
    forall i l e n,
    IStep i l ->
    NStep e n ->
    IStep (e::i) (n::l).
  (* ------------------------------ EQUIVALENCE ------------------ *)

  Lemma n_step_inv_subst_var_eq:
    forall x v y n,
    NStep (n_subst x v (NVar y)) n ->
    x = y.
  Proof.
    intros.
    simpl in H.
    destruct (Set_VAR.MF.eq_dec x y); auto.
    inversion H.
  Qed.

  Lemma n_subst_eq_rw:
    forall x v,
    n_subst x v (NVar x) = v.
  Proof.
    intros.
    simpl.
    destruct (Set_VAR.MF.eq_dec x x); auto.
    contradiction.
  Qed.

  Lemma n_subst_subst_eq_1:
    forall e1 e2 x e3,
    n_subst x e1 (n_subst x e2 e3)
    =
    n_subst x (n_subst x e1 e2) e3.
  Proof.
    induction e3; intros; simpl in *.
    - reflexivity.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      reflexivity.
    - rewrite IHe3_1; auto.
      rewrite IHe3_2; auto.
  Qed.

  Definition NClosed e := forall x, ~ NFree x e.

  Lemma n_closed_to_not_free:
    forall e,
    NClosed e ->
    forall x, ~ NFree x e.
  Proof.
    auto.
  Qed.

  Lemma n_closed_to_not_free_subst:
    forall v,
    NClosed v ->
    forall x e,
    ~ NFree x (n_subst x v e).
  Proof.
    intros.
    unfold NClosed in H.
    intros N.
    apply n_free_inv_subst_eq in N.
    assert (H := H x).
    contradiction.
  Qed.

  Lemma n_closed_var:
    forall x,
    ~ NClosed (NVar x).
  Proof.
    intros x N.
    assert (NFree x (NVar x)). {
      constructor.
    }
    assert (N := N x).
    contradiction.
  Qed.

  Lemma n_closed_num:
    forall n,
    NClosed (NNum n).
  Proof.
    intros n x N.
    invc N.
  Qed.

  Lemma n_free_num:
    forall n x,
    ~ NFree x (NNum n).
  Proof.
    intros.
    intros N.
    inversion N.
  Qed.

  Lemma n_closed_inv_bin:
    forall o e1 e2,
    NClosed (NBin o e1 e2) ->
    NClosed e1 /\ NClosed e2.
  Proof.
    unfold NClosed; intros; split. {
      intros.
      intros N.
      assert (H:=H x).
      contradict H.
      simpl.
      intuition.
    }
    intros x N.
    assert (H:=H x).
    contradict H.
    simpl.
    intuition.
  Qed.

  Lemma n_closed_to_step:
    forall e,
    NClosed e ->
    exists m, NStep e m.
  Proof.
    induction e; intros.
    - econstructor.
      econstructor.
    - econstructor.
      constructor.
    - contradict H.
      auto using n_closed_var.
    - apply n_closed_inv_bin in H.
      destruct H as (Ha, Hb).
      destruct IHe1 as (n1, Hn1); auto.
      destruct IHe2 as (n2, Hn2); auto.
      eauto using n_step_bin.
  Qed.

  Lemma n_step_to_closed:
    forall e n,
    NStep e n ->
    NClosed e.
  Proof.
    intros.
    unfold NClosed.
    eauto using n_step_to_not_free.
  Qed.

  Lemma n_step_subst_num:
    forall n e,
    NStep e n ->
    forall x m,
    NStep (n_subst x (NNum m) e) n.
  Proof.
    intros.
    rewrite n_subst_not_free.
    { assumption. }
    apply n_step_to_closed in H.
    apply H.
  Qed.

  Lemma n_subst_subst_neq_4:
    forall e3 e1 e2 x y,
    NClosed e1 -> 
    x <> y ->
    n_subst y e1 (n_subst x e2 e3) =
    n_subst y e1 (n_subst x (n_subst y e1 e2) e3).
  Proof.
    induction e3; intros.
    - reflexivity.
    - reflexivity.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        symmetry.
        rewrite n_subst_not_free; auto using n_closed_to_not_free_subst.
      }
      reflexivity.
    - simpl.
      rewrite IHe3_1; auto.
      rewrite IHe3_2; auto.
  Qed.

  Lemma n_subst_subst_neq_5:
    forall e3 x y e1 e2,
    NClosed e1 ->
    x <> y ->
    n_subst y e1 (n_subst x e2 e3) =
    n_subst x (n_subst y e1 e2) (n_subst y e1 e3).
  Proof.
    induction e3; intros; simpl.
    - reflexivity.
    - reflexivity.
    - rename v into z.
      (* e3 = z *)
      destruct (Set_VAR.MF.eq_dec x z). {
        subst.
        (* e3 = z = x *)
        destruct (Set_VAR.MF.eq_dec y z). {
          subst.
          contradiction.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec z z) as [_|?]; try contradiction.
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec z z) as [_|?]; try contradiction.
        rewrite n_subst_not_free; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec y z) as [?|_]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x z) as [?|_]; try contradiction.
      reflexivity.
    - rewrite IHe3_1; auto.
      rewrite IHe3_2; auto.
  Qed.

  Lemma n_step_inv_succ_l:
    forall e n,
    NStep (NBin NPlus (NNum 1) e) n -> 
    exists n', NStep e n' /\ n = S n'.
  Proof.
    intros.
    invc H.
    assert (n1 = 1) by eauto using n_step_num, n_step_fun.
    subst.
    exists n2.
    split; eauto.
  Qed.

  Lemma n_step_inv_succ_r:
    forall e n,
    NStep (NBin NPlus e (NNum 1)) n -> 
    exists n', NStep e n' /\ n = S n'.
  Proof.
    intros.
    invc H.
    assert (n2 = 1) by eauto using n_step_num, n_step_fun.
    subst.
    exists n1.
    split; eauto.
    simpl.
    lia.
  Qed.

  Lemma n_step_succ_minus_one:
    forall n,
    NStep (NBin NMinus (NNum (S n)) (NNum 1)) n.
  Proof.
    intros.
    assert (NStep (NBin NMinus (NNum (S n)) (NNum 1)) (S n - 1)) by
      (apply n_step_bin; auto using n_step_num).
    remember (S n - 1) as nx.
    assert (r1: nx = n) by lia.
    remember (NBin NMinus (NNum (S n)) (NNum 1)) as e.
    rewrite r1 in H.
    assumption.
  Qed.

  Lemma n_step_inv_dec:
    forall e n,
    NStep (NBin NMinus e (NNum 1)) (S n) ->
    NStep e (S (S n)).
  Proof.
    intros.
    apply n_step_inv_nbin in H.
    destruct H as (n1, (n2, (Hn1, (Hn2, ?)))).
    simpl in *.
    invc Hn2.
    destruct n1. {
      simpl.
      invc H.
    }
    simpl in *.
    destruct n1. {
      invc H.
    }
    simpl in *.
    invc H.
    assumption.
  Qed.
End SO.

Module NExpNotations.
  Declare Scope exp_scope.
  Infix "-" := (NBin NMinus)  (at level 50, left associativity, only printing) : exp_scope. 
  Infix "+" := (NBin NPlus)  (at level 50, left associativity, only printing) : exp_scope. 
  Infix "*" := (NBin NMult)  (at level 40, left associativity, only printing) : exp_scope. 
  Infix "/" := (NBin NDiv)  (at level 40, left associativity, only printing) : exp_scope. 
  Infix "%" := (NBin NMod)  (at level 40, left associativity, only printing) : exp_scope. 
  Coercion NNum : nat >-> nexp.
  Coercion NVar : var >-> nexp.
  Notation "e [ x := v ]" := (n_subst x v e) (at level 30, only printing) : exp_scope. 
  Infix "=?" := Set_VAR.MF.eq_dec (at level 60, only printing) : exp_scope.
End NExpNotations.

