Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationPairs.

Require Import ALang.
Require Import AccExp.
Require Import Tasks.
Require Import NExp.
Require Import RExp.
Require Import Var.
(*
Require Import Tid.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.
Require Import VHist.
Require Import RangeList.

Require RangeList.
*)
Require Import Lia.

Import ListNotations.
Require Conc.

Section Defs.

  Context `{T:Tasks}.
  Context {A:Access}.

  Open Scope vhist_scope.

  Inductive phase :=
  | PhZero
  | PhOne
  | PhPlus: phase -> phase -> phase
  | PhSum : var -> range -> phase -> phase
  .

  (* ------------------------------- IN PHASE OF ------------------------ *)

  Fixpoint ph_not_zero_weak (ph:phase) :=
    match ph with
    | PhZero => False
    | PhOne => True
    | PhPlus ph1 ph2 => ph_not_zero_weak ph1 \/ ph_not_zero_weak ph2
    | PhSum x r ph => True
    end.

  (* ------------------------- OPERATIONAL SEMANTICS ----------------- *)

  Fixpoint ph_subst (x:var) (v:nexp) (ph:phase) : phase :=
  match ph with
  | PhZero => PhZero
  | PhOne => PhOne
  | PhPlus ph1 ph2 => PhPlus (ph_subst x v ph1) (ph_subst x v ph2)
  | PhSum y r ph =>
    let ph' := if VAR.eq_dec x y then ph else ph_subst x v ph in
    PhSum y (r_subst x v r) ph'
  end.

  Inductive RunPh : phase -> nat -> Prop :=
  | run_ph_zero:
    RunPh PhZero 0
  | run_ph_one:
    RunPh PhOne 1
  | run_ph_plus:
    forall ph1 ph2 n1 n2 n,
    RunPh ph1 n1 ->
    RunPh ph2 n2 ->
    n = n1 + n2 ->
    RunPh (PhPlus ph1 ph2) n
  | run_ph_sum_cons:
    forall x e1 e2 ni nj ph n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RunPh (ph_subst x (NNum n1) ph) ni ->
    RunPh (PhSum x (NNum (S n1), e2) ph) nj ->
    n = ni + nj -> 
    RunPh (PhSum x (e1, e2) ph) n
  | run_ph_sum_nil:
    forall x e1 e2 ph n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    RunPh (PhSum x (e1, e2) ph) 0.

  (* Same as RunPh but all sums are nonempty. *)

  Inductive Nonempty : phase -> Prop :=
  | nonempty_zero:
    Nonempty PhZero
  | nonempty_sync:
    Nonempty PhOne
  | nonempty_plus:
    forall ph1 ph2,
    Nonempty ph1 ->
    Nonempty ph2 ->
    Nonempty (PhPlus ph1 ph2)
  | nonempty_sum_cons:
    forall x e1 e2 ph n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Nonempty (ph_subst x (NNum n1) ph) ->
    Nonempty (PhSum x (NNum (S n1), e2) ph) -> 
    Nonempty (PhSum x (e1, e2) ph)
  | nonempty_sum_eq:
    forall x e1 e2 ph n,
    NStep e1 n ->
    NStep e2 (S n) ->
    Nonempty (ph_subst x (NNum n) ph) ->
    Nonempty (PhSum x (e1, e2) ph).

  Inductive RunPhNE : phase -> nat -> Prop :=
  | run_ph_ne_zero:
    RunPhNE PhZero 0
  | run_ph_ne_one:
    RunPhNE PhOne 1
  | run_ph_ne_plus:
    forall ph1 ph2 n1 n2 n,
    RunPhNE ph1 n1 ->
    RunPhNE ph2 n2 ->
    n = n1 + n2 ->
    RunPhNE (PhPlus ph1 ph2) n
  | run_ph_ne_sum_cons:
    forall x e1 e2 ni nj ph n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RunPhNE (ph_subst x (NNum n1) ph) ni ->
    RunPhNE (PhSum x (NNum (S n1), e2) ph) nj ->
    n = ni + nj -> 
    RunPhNE (PhSum x (e1, e2) ph) n
  | run_ph_ne_sum_eq:
    forall x e1 e2 ph n m,
    NStep e1 n ->
    NStep e2 (S n) ->
    RunPhNE (ph_subst x (NNum n) ph) m ->
    RunPhNE (PhSum x (e1, e2) ph) m.

  (* --------------------- PhEq -------- *)

  Definition PhEq ph1 ph2 : Prop :=
    forall n,
    RunPh ph1 n <-> RunPh ph2 n.

  Lemma nonempty_run_to_run_ph_ne:
    forall ph,
    Nonempty ph ->
    forall n,
    RunPh ph n ->
    RunPhNE ph n.
  Proof.
    intros ph H.
    induction H; intros.
    - inversion H; subst; clear H.
      apply run_ph_ne_zero.
    - inversion H; subst; clear H.
      apply run_ph_ne_one.
    - inversion H1; subst; clear H1.
      apply run_ph_ne_plus with (n1:=n1) (n2:=n2); eauto.
    - inversion H4; subst; clear H4.
      + assert (n0 = n1) by eauto using n_step_fun.
        assert (n3 = n2) by eauto using n_step_fun.
        subst.
        eapply run_ph_ne_sum_cons; eauto.
      + assert (n0 = n1) by eauto using n_step_fun.
        assert (n3 = n2) by eauto using n_step_fun.
        subst.
        lia.
    - inversion H2; subst; clear H2.
      + assert (n1 = n) by eauto using n_step_fun.
        assert (n2 = S n) by eauto using n_step_fun.
        subst.
        assert (nj = 0). {
          inversion H12; subst; clear H12.
          - assert (n1 = S n) by eauto using n_step_fun, n_step_num.
            assert (n2 = S n) by eauto using n_step_fun.
            subst.
            lia.
          - reflexivity.
        }
        subst.
        rewrite PeanoNat.Nat.add_0_r.
        eauto using run_ph_ne_sum_eq.
      + assert (n1 = n) by eauto using n_step_fun.
        assert (n2 = S n) by eauto using n_step_fun.
        subst.
        lia.
  Qed.

  Lemma run_ph_ne_to_run_ph:
    forall ph n,
    RunPhNE ph n ->
    RunPh ph n.
  Proof.
    intros.
    induction H; intros; try (constructor; auto).
    - eapply run_ph_plus; eauto.
    - eapply run_ph_sum_cons; eauto.
    - eapply run_ph_sum_cons; eauto.
      eapply run_ph_sum_nil; eauto using n_step_num. 
  Qed.
  Import Coq.Classes.Morphisms.

  Lemma run_ph_eq_sum:
    forall x nl nr ph n,
    RunPh (PhSum x (nl, nr) ph) n ->
    forall nl' nr',
    NEq nl nl' ->
    NEq nr nr' ->
    RunPh (PhSum x (nl', nr') ph) n.
  Proof.
    intros x nl nr ph n H.
    remember (PhSum _ _ _) as ph'.
    generalize dependent x.
    generalize dependent nl.
    generalize dependent nr.
    generalize dependent ph.
    induction H; intros; inversion Heqph'; subst; clear Heqph'. {
      rename x0 into x.
      eapply run_ph_sum_cons; eauto.
      - rewrite <- H5.
        assumption.
      - rewrite <- H6.
        assumption.
      - eapply IHRunPh2; eauto.
        reflexivity.
    }
    rewrite H2 in H.
    rewrite H3 in H0.
    eapply run_ph_sum_nil; eauto.
  Qed.

  Global Instance ph_eq_proper_1: Proper (eq ==> NEq * NEq ==> eq ==> PhEq ) PhSum.
  Proof.
    unfold Proper, respectful.
    intros x' x ? (nl_1, nr_1) (nl_2, nr_2) Hp ph' ph ?.
    subst.
    destruct Hp as (Ha, Hb).
    unfold RelCompFun in *.
    simpl in *.
    split; intros.
    - eapply run_ph_eq_sum; eauto.
    - symmetry in Ha.
      symmetry in Hb.
      eapply run_ph_eq_sum; eauto.
  Qed.

  Inductive RunPh_S (x:var) (v:nexp) : phase -> nat -> Prop :=
  | run_ph_s_zero:
    RunPh_S x v PhZero 0
  | run_ph_s_one:
    RunPh_S x v PhOne 1
  | run_ph_s_plus:
    forall ph1 ph2 n1 n2 n,
    RunPh_S x v ph1 n1 -> 
    RunPh_S x v ph2 n2 ->
    n = n1 + n2 -> 
    RunPh_S x v (PhPlus ph1 ph2) n
  | run_ph_s_sum_eq:
    forall r ph n,
    RunPh (PhSum x (r_subst x v r) ph) n ->
    RunPh_S x v (PhSum x r ph) n
  | run_ph_s_sum_neq_cons:
    forall y e1 e2 ph ni nj n n1 n2,
    x <> y ->
    NStep (n_subst x v e1) n1 ->
    NStep (n_subst x v e2) n2 ->
    n1 < n2 ->
    RunPh_S x v (ph_subst y (NNum n1) ph) ni ->
    RunPh_S x v (PhSum y (NNum (S n1), e2) ph) nj ->
    n = ni + nj ->
    RunPh_S x v (PhSum y (e1, e2) ph) n
  | run_ph_s_sum_nil:
    forall y e1 e2 ph n1 n2,
    NStep (n_subst x v e1) n1 ->
    NStep (n_subst x v e2) n2 ->
    n1 >= n2 ->
    RunPh_S x v (PhSum y (e1, e2) ph) 0.

  Lemma run_ph_s_spec:
    forall x v e n,
    RunPh (ph_subst x v e) n <-> RunPh_S x v e n.
  Proof.
    split; intros.
    - remember (ph_subst _ _ _) as ph.
      generalize dependent x.
      generalize dependent v.
      generalize dependent e.
      induction H; intros e v y Heq; destruct e; simpl in Heq; inversion Heq; subst; clear Heq; try (constructor; auto).
      + eapply run_ph_s_plus; eauto.
      + destruct r as (e1', e2').
        simpl in *.
        inversion H7; subst; clear H7.
        destruct (Set_VAR.MF.eq_dec y v0). {
          subst.
          apply run_ph_s_sum_eq.
          eapply run_ph_sum_cons; eauto.
        }
        eapply run_ph_s_sum_neq_cons; eauto.
        * apply IHRunPh1.
          admit.
        * apply IHRunPh2.
          simpl.
          destruct (Set_VAR.MF.eq_dec y y) as [_| ?]; try contradiction.
          destruct (Set_VAR.MF.eq_dec y v0) as [?| _]; try contradiction.
          reflexivity.
      + destruct r as (e1', e2').
        simpl in *.
        inversion H4; subst; clear H4.
        eapply run_ph_s_sum_nil; eauto.
    - induction H; simpl.
      + apply run_ph_zero.
      + apply run_ph_one.
      + eauto using run_ph_plus.
      + destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
        assumption.
      + destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
        eapply run_ph_sum_cons; eauto.
        * admit.
        * admit.
      + eauto using run_ph_sum_nil.
  Admitted.

  Lemma eq_run_ph_subst_proper_0:
    forall x v e n, 
    RunPh_S x v e n ->
    forall v',
    NEq v v' ->
    RunPh_S x v' e n.
  Proof.
    intros x v e n H.
    induction H; intros.
    - apply run_ph_s_zero.
    - apply run_ph_s_one.
    - eapply run_ph_s_plus; eauto.
    - apply run_ph_s_sum_eq; auto.
      destruct r as (e1, e2).
      simpl in *.
      eapply run_ph_eq_sum; eauto using n_eq_subst_rw.
    - assert (IHRunPh_S1 := IHRunPh_S1 v' H6).
      assert (IHRunPh_S2 := IHRunPh_S2 v' H6).
      eapply run_ph_s_sum_neq_cons; eauto.
      + rewrite <- H6; assumption.
      + rewrite <- H6; assumption.
    - eapply run_ph_s_sum_nil; eauto.
      + rewrite <- H2.
        assumption.
      + rewrite <- H2.
        assumption.
  Qed.

  Lemma run_ph_subst:
    forall v v' e x n, 
    NEq v v' ->
    RunPh (ph_subst x v e) n ->
    RunPh (ph_subst x v' e) n.
  Proof.
    intros.
    apply run_ph_s_spec in H0.
    apply run_ph_s_spec.
    eauto using eq_run_ph_subst_proper_0.
  Qed.

  Lemma ph_eq_subst:
    forall v v' x e,
    NEq v v' ->
    PhEq (ph_subst x v e) (ph_subst x v' e).
  Proof.
    split; intros.
    + eauto using run_ph_subst.
    + symmetry in H.
      eauto using run_ph_subst.
  Qed.

  Lemma for_unroll:
    forall ph x e1 e2,
    Nonempty (PhSum x (e1, e2) ph) ->
    let e2' := NBin NMinus e2 (NNum 1) in
    let x' := NBin NPlus (NNum 1) (NVar x) in
    PhEq (PhSum x (e1, e2) ph)
      (PhPlus (ph_subst x e1 ph)
         (PhSum x (e1, e2') (ph_subst x x' ph))).
  Proof.
    intros.
    split; intros.
    - apply nonempty_run_to_run_ph_ne in H0; auto.
      inversion H0; subst; clear H0.
      + eapply run_ph_plus; eauto.
        * apply run_ph_ne_to_run_ph in H9.
          apply ph_eq_subst with (v:=NNum n1); auto.
          symmetry.
          auto using n_step_to_n_eq.
        * clear H9.
          admit.
      + (* Only runs once *)
        admit.
    - inversion H0; subst; clear H0.
      inversion H; subst; clear H.
      + rename n0 into e1_n.
        rename n3 into e2_n.
        inversion H8; subst; clear H8. {
          (* Base case *)
          eapply run_ph_sum_cons; eauto. {
            eapply ph_eq_subst; eauto.
            symmetry.
            auto using n_step_to_n_eq.
          }
          assert (n2 = 0). {
            inversion H4; subst; clear H4; auto.
            assert (n0 = e1_n) by eauto using n_step_fun.
            assert (n3 = e1_n). {
              unfold e2' in *.
              inversion H8; subst; clear H8.
              assert (n4 = 1) by eauto using n_step_fun, n_step_num.
              assert (n2 = S e1_n) by eauto using n_step_fun.
              subst.
              simpl in *.
              lia.
            }
            subst.
            lia.
          }
          subst.
          eapply run_ph_sum_nil; eauto using n_step_num.
        }
        eapply run_ph_sum_cons; eauto. {
          eapply ph_eq_subst; eauto.
          symmetry.
          auto using n_step_to_n_eq.
        }
        admit.
      + 
  Admitted.

End Defs.