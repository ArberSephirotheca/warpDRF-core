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

  Inductive NIn (x: var): nexp -> Prop :=
  | n_in_eq:
    NIn x (NVar x)
  | n_in_bin_l:
    forall o n1 n2,
    NIn x n1 ->
    NIn x (NBin o n1 n2)
  | n_in_bin_r:
    forall o n1 n2,
    NIn x n2 ->
    NIn x (NBin o n1 n2).


  Lemma not_n_in_bin_l:
    forall x o n1 n2,
    ~ NIn x (NBin o n1 n2) ->
    ~ NIn x n1.
  Proof.
    intros.
    intros N.
    contradict H.
    constructor; auto.
  Qed.

  Lemma not_n_in_bin_r:
    forall x o n1 n2,
    ~ NIn x (NBin o n1 n2) ->
    ~ NIn x n2.
  Proof.
    intros.
    intros N.
    contradict H.
    apply n_in_bin_r.
    assumption.
  Qed.

  Lemma not_n_in_bin:
    forall x o n1 n2,
    ~ NIn x (NBin o n1 n2) ->
    ~ NIn x n1 /\ ~ NIn x n2.
  Proof.
    intros.
    split.
    - eauto using not_n_in_bin_l.
    - eauto using not_n_in_bin_r.
  Qed.

  Lemma n_subst_not_in:
    forall x v n,
    ~ NIn x n ->
    n_subst x v n = n.
  Proof.
    induction n; intros.
    - reflexivity.
    - assert (x <> v0). {
        intros N.
        subst.
        contradict H.
        constructor.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v0). {
        contradiction.
      }
      reflexivity.
    - apply not_n_in_bin in H.
      destruct H as (Ha, Hb).
      apply IHn1 in Ha.
      apply IHn2 in Hb.
      simpl.
      rewrite Ha.
      rewrite Hb.
      reflexivity.
  Qed.

  Lemma n_subst_to_not_in:
    forall x v n1 n2,
    n_subst x (NNum v) n1 = n2 ->
    ~ NIn x n2.
  Proof.
    induction n1; simpl; intros; subst; intros N.
    - inversion N.
    - destruct (Set_VAR.MF.eq_dec x v0). {
        subst.
        inversion N.
      }
      inversion N; subst.
      contradiction.
    - inversion N; subst; clear N.
      + remember (n_subst _ _ _) as j.
        symmetry in Heqj.
        apply IHn1_1 in H0; auto.
      + remember (n_subst _ _ _) as j.
        symmetry in Heqj.
        apply IHn1_2 in H0; auto.
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
    ~ NIn y v1 ->
    ~ NIn x v2 ->
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
        rewrite n_subst_not_in; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        destruct (Set_VAR.MF.eq_dec v v) as [_|N]; try contradiction.
        rewrite n_subst_not_in; auto.
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

  Lemma n_subst_subst_eq_2:
    forall x n v e,
    ~ NIn x v ->
    n_subst x e (n_subst x v n) = n_subst x v n.
  Proof.
    induction n; intros; simpl.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite n_subst_not_in; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). { contradiction. }
      reflexivity.
    - rewrite IHn1; auto.
      rewrite IHn2; auto.
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
    ~ NIn x e ->
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
        auto using n_in_eq.
      }
      reflexivity.
    - apply not_n_in_bin in H.
      destruct H as (Ha, Hb).
      rewrite IHe1; auto.
      rewrite IHe2; auto.
  Qed.

  Lemma in_n_subst_neq:
    forall e x y v,
    NIn x (n_subst y v e) ->
    ~ NIn x v ->
    NIn x e.
  Proof.
    induction e; simpl; intros; inversion H; subst; rename H into N.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        contradiction.
      }
      auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        contradiction.
      }
      (* contradiction *)
      inversion H1.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        contradiction.
      }
      (* contradiction *)
      inversion H1.
    - subst.
      apply IHe1 in H2; auto using n_in_bin_l.
    - apply IHe2 in H2; auto using n_in_bin_r.
  Qed.

  Lemma n_in_inv_subst:
    forall x y z n,
    x <> y ->
    x <> z ->
    NIn x (n_subst z (NVar y) n) ->
    NIn x n.
  Proof.
    intros.
    apply in_n_subst_neq in H1; auto.
    intros N.
    inversion N; subst; clear N.
    contradiction.
  Qed.

  Lemma n_in_subst_eq:
    forall x y e,
    ~ NIn x e ->
    NIn x (n_subst y (NVar x) e) ->
    NIn y e.
  Proof.
    induction e; simpl; intros.
    - inversion H0.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        auto using n_in_eq.
      }
      contradiction.
    - inversion H0; subst; clear H0.
      + apply IHe1 in H2; auto using n_in_bin_l.
      + apply IHe2 in H2; auto using n_in_bin_r.
  Qed.

  Lemma n_step_inv_subst:
    forall x v e n,
    NStep (n_subst x v e) n ->
    ~ NIn x e \/ exists n', NStep v n'.
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

  Lemma n_step_to_not_in:
    forall e n,
    NStep e n ->
    forall x,
    ~ NIn x e.
  Proof.
    intros e n H.
    induction H; intros; intros N; inversion N; subst; clear N.
    - apply IHNStep1 in H2.
      auto.
    - apply IHNStep2 in H2; auto.
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
        rewrite n_subst_not_in in H1; auto.
        rewrite <- H.
        assumption.
      }
      rewrite <- H in Hx.
      rewrite n_subst_subst_eq_2 in H1; eauto using n_step_to_not_in.
      rewrite <- H.
      assumption.
    - rewrite <- H in H1.
      assert (n0 = n) by eauto using n_step_fun.
      subst.
      edestruct n_step_inv_subst as [Hx|(n', Hx)]; eauto. {
        rewrite n_subst_not_in;
        eauto using n_step_to_not_in.
      }
      rewrite n_subst_subst_eq_2; eauto using n_step_to_not_in.
  Qed.


  Lemma n_subst_not_in_rw:
    forall x e,
    ~ NIn x e ->
    forall v,
    n_subst x v e = e.
  Proof.
    induction e; intros; simpl; rename_hyp (~ _) as N.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradict N.
        apply n_in_eq.
      }
      reflexivity.
    - apply not_n_in_bin in N.
      destruct N as (Ha, Hb).
      rewrite IHe1; auto.
      rewrite IHe2; auto.
  Qed.

End SO.

