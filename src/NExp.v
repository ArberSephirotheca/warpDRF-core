Require Import Coq.Lists.List.
Import ListNotations.

Require Import Var.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationPairs.
Require Import Tictac.

Section Defs.

  Inductive nbin :=
  | NPlus
  | NMinus
  | NMult
  | NDiv
  | NMod.

  Inductive nexp :=
  | NNum : nat -> nexp
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

  Inductive NStep: nexp -> nat -> Prop :=
  | n_step_num:
    forall n,
    NStep (NNum n) n
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
    end.

  Lemma n_step_subst_next:
    forall x a n1 n2,
    NStep (n_subst x (NNum n1) a) n2 ->
    forall m1, exists m2, NStep (n_subst x (NNum m1) a) m2.
  Proof.
    induction a; simpl; intros.
    - exists n.
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
    end.

  Lemma n_step_to_prop:
    forall e n,
    n_step e = Some n ->
    NStep e n.
  Proof.
    induction e; intros; simpl in *; inversion H; subst; clear H.
    - auto using n_step_num.
    - destruct (n_step e1). {
        destruct (n_step e2);
           inversion H1; subst; clear H1.
        auto using n_step_bin.
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

  Inductive NTypes (l: list var) : nexp -> Prop :=
  | n_types_num:
    forall n,
    NTypes l (NNum n)
  | n_types_var:
    forall v,
    List.In v l ->
    NTypes l (NVar v)
  | n_types_nbin:
    forall x y o,
    NTypes l x ->
    NTypes l y ->
    NTypes l (NBin o x y).

  Lemma n_progress:
    forall e,
    NTypes [] e ->
    exists n, NStep e n.
  Proof.
    induction e; intros.
    - eauto using n_step_num.
    - inversion H; subst; clear H.
      contradiction.
    - inversion H; subst; clear H.
      destruct IHe1 as (n1, Hn1); auto.
      destruct IHe2 as (n2, Hn2); auto.
      eauto using n_step_bin.
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
    - eauto.
    - eauto.
    - simpl.
      eauto.
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

  Fixpoint NFree (e: nexp) (x:var) : Prop := 
    match e with
    | NVar y => y = x
    | NBin _ e1 e2 => NFree e1 x \/ NFree e2 x
    | NNum _ => False
    end.

  Lemma n_subst_not_free:
    forall x v n,
    ~ NFree n x ->
    n_subst x v n = n.
  Proof.
    induction n; intros.
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
    NFree (n_subst x e n) x ->
    NFree e x.
  Proof.
    induction n; intros; simpl in *.
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
    ~ NFree n2 x.
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
    ~ NFree v x ->
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
    NFree (n_subst y v e) x ->
    ~ NFree v x ->
    NFree e x.
  Proof.
    induction e; simpl; intros; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        contradiction.
      }
      auto.
    - destruct H; eauto.
  Qed.

  Lemma n_free_inv_subst:
    forall x y z n,
    x <> y ->
    x <> z ->
    NFree (n_subst z (NVar y) n) x ->
    NFree n x.
  Proof.
    intros.
    apply n_free_subst_neq in H1; auto.
  Qed.

  Lemma n_free_subst_eq:
    forall x y e,
    ~ NFree e x ->
    NFree (n_subst y (NVar x) e) x ->
    NFree e y.
  Proof.
    induction e; simpl; intros.
    - inversion H0.
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
    ~ NFree v1 y ->
    ~ NFree v2 x ->
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

  (* TODO: remove me and replace it by n_subst_subst_eq_2 *)
  Lemma n_subst_subst_eq:
    forall x n n1 n2,
    n_subst x (NNum n1) (n_subst x (NNum n2) n) = n_subst x (NNum n2) n.
  Proof.
    induction n; intros; simpl.
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
    ~ NFree e x ->
    n_subst x v (n_subst y (NVar x) e) = n_subst y v e.
  Proof.
    induction e; simpl; intros.
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
    ~ NFree e x \/ exists n', NStep v n'.
  Proof.
    induction e; intros; simpl in *.
    - left.
      intros N.
      inversion N.
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
    ~ NFree e x.
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

  Definition NEq e1 e2 :=
    forall n,
    NStep e1 n <-> NStep e2 n.

  Lemma n_eq_refl:
    forall e,
    NEq e e.
  Proof.
    unfold NEq; tauto.
  Qed.

  Lemma n_eq_sym:
    forall e1 e2,
    NEq e1 e2 ->
    NEq e2 e1.
  Proof.
    unfold NEq; intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma n_eq_trans:
    forall e1 e2 e3,
    NEq e1 e2 ->
    NEq e2 e3 ->
    NEq e1 e3.
  Proof.
    unfold NEq.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [NEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ NEq
    reflexivity proved by n_eq_refl
    symmetry proved by n_eq_sym
    transitivity proved by n_eq_trans
    as b_eq_setoid.
  Import Morphisms.

  Lemma n_eq_to_n_step:
    forall e n,
    NEq e (NNum n) ->
    NStep e n.
  Proof.
    intros.
    apply H.
    auto using n_step_num.
  Qed.

  Lemma n_step_to_n_eq:
    forall e n,
    NStep e n ->
    NEq e (NNum n).
  Proof.
    split; intros.
    - assert (n0 = n) by eauto using n_step_fun.
      subst.
      auto using n_step_num.
    - inversion H0; subst; clear H0.
      assumption.
  Qed.

  Lemma n_eq_bin_1:
    forall n e1 e1' e2 e2' o,
    NEq e1 e1' ->
    NEq e2 e2' ->
    NStep (NBin o e1 e2) n ->
    NStep (NBin o e1' e2') n.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply H in H6.
    apply H0 in H7.
    apply n_step_bin; auto.
  Qed.

  Global Instance n_eq_proper_1: Proper (eq ==> NEq ==> NEq ==> NEq) NBin.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros; subst.
    - eauto using n_eq_bin_1.
    - symmetry in H0.
      symmetry in H1.
      eauto using n_eq_bin_1.
  Qed.

  Global Instance n_eq_proper_2: Proper (NEq ==> eq ==> iff) NStep.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

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

  Lemma eq_n_step_n_subst_proper:
    forall x v v' e n, 
    NEq v v' ->
    NStep (n_subst x v e) n ->
    NStep (n_subst x v' e) n.
  Proof.
    induction e; intros.
    - simpl in *.
      assumption.
    - simpl in *.
      destruct (Set_VAR.MF.eq_dec x v0); auto.
      subst.
      apply H; auto.
    - simpl in *.
      inversion H0; subst; clear H0.
      eauto using n_step_bin.
  Qed.

  Lemma n_eq_subst_rw:
    forall x v v' e, 
    NEq v v' ->
    NEq (n_subst x v e) (n_subst x v' e).
  Proof.
    intros.
    split; intros.
    - eauto using eq_n_step_n_subst_proper.
    - symmetry in H.
      eauto using eq_n_step_n_subst_proper.
  Qed.

  Global Instance n_eq_proper_3: Proper (eq ==> NEq ==> eq ==> NEq) n_subst.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - eapply eq_n_step_n_subst_proper; eauto.
    - symmetry in H0.
      eapply eq_n_step_n_subst_proper; eauto.
  Qed.

  Lemma n_eq_subst_subst:
    forall x v e v' n,
    NEq v v' ->
    NStep (n_subst x v e) n ->
    NEq (n_subst x v' (n_subst x v e)) (n_subst x v' e).
  Proof.
    intros.
    split; intros.
    - edestruct n_step_inv_subst as [Hx|(n', Hx)]; eauto. {
        rewrite n_subst_not_free in H1; auto.
        rewrite <- H.
        assumption.
      }
      rewrite <- H in Hx.
      rewrite n_subst_subst_eq_2 in H1; eauto using n_step_to_not_free.
      rewrite <- H.
      assumption.
    - rewrite <- H in H1.
      assert (n0 = n) by eauto using n_step_fun.
      subst.
      edestruct n_step_inv_subst as [Hx|(n', Hx)]; eauto. {
        rewrite n_subst_not_free;
        eauto using n_step_to_not_free.
      }
      rewrite n_subst_subst_eq_2; eauto using n_step_to_not_free.
  Qed.

  Lemma n_subst_subst_eq_1:
    forall e1 e2 x e3,
    n_subst x e1 (n_subst x e2 e3)
    =
    n_subst x (n_subst x e1 e2) e3.
  Proof.
    induction e3; intros; simpl in *.
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

  Definition NClosed e := forall x, ~ NFree e x.

  Lemma n_closed_to_not_free:
    forall e,
    NClosed e ->
    forall x, ~ NFree e x.
  Proof.
    auto.
  Qed.

  Lemma n_closed_to_not_free_subst:
    forall v,
    NClosed v ->
    forall x e,
    ~ NFree (n_subst x v e) x.
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
    assert (NFree (NVar x) x). {
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
    ~ NFree (NNum n) x.
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
    exists n, NStep e n.
  Proof.
    induction e; intros.
    - eauto using n_step_num.
    - contradict H.
      auto using n_closed_var.
    - apply n_closed_inv_bin in H.
      destruct H as (Ha, Hb).
      destruct IHe1 as (n1, Hn1); auto.
      destruct IHe2 as (n2, Hn2); auto.
      eauto using n_step_bin.
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

