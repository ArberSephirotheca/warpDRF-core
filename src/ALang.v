Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationPairs.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.
Require Import VHist.
Require Import RangeList.

Require RangeList.
Require Import Lia.

Import ListNotations.
Require Conc.
Require Import NSync.

Section Defs.

  Notation history := (list access_val).

  Notation mhistory := (list history).

  Notation histpair := (mhistory * history) % type.

  Context `{T:Tasks}.
  Context {A:Access}.

  Open Scope vhist_scope.

(* -------------------- RUN --------------------------- *)


  Inductive inst :=
  | Sync
  | Block: Conc.inst -> inst
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst.

  Fixpoint i_subst x v i :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
    | For y r i2 =>
      let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
      For y (r_subst x v r) i2'
    end.

  Inductive Run: inst -> vhist -> Prop :=
  | run_sync:
    Run Sync {{ [] | [] }}
  | run_block:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) {{ h }}
  | run_seq: forall i j mh_i mh_j mh,
    Run i mh_i ->
    Run j mh_j ->
    mh_i @ mh_j = mh ->
    Run (Seq i j) mh
  | run_for_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) m1 ->
    Run (For x (NNum (S n1), NNum n2) i) m2 ->
    m1 @ m2 = m3 ->
    Run (For x (e1, e2) i) m3
  | run_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall x i e1 e2 m n,
    NStep e1 n ->
    NStep e2 (S n) ->
    Run (i_subst x (NNum n) i) m ->
    Run (For x (e1, e2) i) m.


  Goal Run Sync {{ [] | [] }}.
  Proof.
    apply run_sync.
  Qed.

  Goal Run (Seq Sync Sync) {{ [] | [] | [] }}.
  Proof.
    eapply run_seq.
    + apply run_sync.
    + apply run_sync.
    + reflexivity.
  Qed.

  Goal Run (Seq (Seq Sync Sync) Sync) {{ [] | [] | [] | [] }}.
  Proof.
    eapply run_seq.
    - eapply run_seq.
      + apply run_sync.
      + apply run_sync.
      + reflexivity.
    - apply run_sync.
    - reflexivity.
  Qed.

(* ------------------------------ VAR -------------------------- *)

  Fixpoint Var x i :=
    match i with
    | Sync => False
    | Block c => Conc.Var x c
    | Seq i j => Var x i \/ Var x j
    | For y _ i => x = y \/ Var x i
    end.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto.
    - eauto using Conc.var_subst_inv_1.
    - destruct H; auto.
    - destruct H; auto.
      destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

(* ------------------------------- NOSYNC ------------------------ *)

  Fixpoint unsynced (i:inst) : bool :=
    match i with
    | Sync => false
    | Block _ => true
    | Seq i j => unsynced i && unsynced j
    | For _ _ i => unsynced i
    end.

  Definition synced (i:inst) : bool := negb (unsynced i).

  Lemma unsynced_subst:
    forall i x v,
    unsynced (i_subst x v i) = unsynced i.
  Proof.
    induction i; intros; simpl in *; auto.
    - rewrite IHi1 with (x:=x) (v:=v); auto.
      rewrite IHi2 with (x:=x) (v:=v); auto.
    - assert (IHi := IHi x v0).
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      assumption.
  Qed.


(* ------------------------------ PHASE -------------------------- *)
  (* Count how many phases this instruction yields. *)

  Inductive Phase : inst -> nat -> Prop :=
  | phase_block:
    forall c,
    Phase (Block c) 0
  | phase_sync:
    Phase Sync 1
  | phase_seq:
    forall i j n m o,
    Phase i n ->
    Phase j m ->
    o = n + m ->
    Phase (Seq i j) o
  | phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    Phase (For x (NNum (S n1), e2) i) m ->
    n + m = o ->
    Phase (For x (e1, e2) i) o
  | phase_for_eq:
    forall i x e1 e2 n m,
    NStep e1 n ->
    NStep e2 (S n) ->
    Phase (i_subst x (NNum n) i) m ->
    Phase (For x (e1, e2) i) m
  .

  Lemma phase_inv_unsynced:
    forall i n,
    Phase i n ->
    unsynced i = true ->
    n = 0.
  Proof.
    intros i n H.
    induction H; intros; simpl in *.
    - reflexivity.
    - inversion H.
    - apply Bool.andb_true_iff in H2.
      destruct H2 as (Ha, Hb).
      rewrite IHPhase1 in H1; auto.
      rewrite IHPhase2 in H1; auto.
    - rewrite IHPhase2 in H4; clear IHPhase2; auto.
      rewrite IHPhase1 in H4; auto.
      rewrite unsynced_subst.
      assumption.
    - rewrite IHPhase; auto.
      rewrite unsynced_subst.
      assumption.
  Qed.

  Lemma phase_to_unsynced:
    forall i,
    Phase i 0 ->
    unsynced i = true.
  Proof.
    intros i H.
    remember 0.
    generalize dependent Heqn.
    induction H; intros; simpl; auto.
    - inversion Heqn.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      rewrite Bool.andb_true_iff.
      auto.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      subst.
      simpl in *.
      rewrite <- unsynced_subst with (x:=x) (v:=NNum n1); auto.
    - rewrite <- unsynced_subst with (x:=x) (v:=NNum n); auto.
  Qed.

(* ------------------------ IN PHASE ------------------------------ *)

  Inductive InPhase (a:access_val) : nat -> inst -> Prop :=
  | in_phase_block:
    forall c,
    Conc.IIn a c ->
    InPhase a 0 (Block c)
  | in_phase_seq_l:
    forall i j n,
    InPhase a n i ->
    InPhase a n (Seq i j)
  | in_phase_seq_r:
    forall i j n m o,
    Phase i n ->
    InPhase a m j ->
    o = n + m ->
    InPhase a o (Seq i j)
  | in_phase_for_eq:
    forall i x e1 e2 n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    InPhase a n (i_subst x (NNum n1) i) ->
    InPhase a n (For x (NNum (S n1), e2) i)
  | in_phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    InPhase a m (For x (NNum (S n1), e2) i) ->
    o = n + m ->
    InPhase a o (For x (e1, e2) i).

(* -------------------------------- IIN/ IPAIRIN ---------------------- *)

  Definition IIn a i : Prop := exists n, InPhase a n i.

  Definition IPairIn (p:access_val * access_val) i : Prop :=
    let (a1, a2) := p in
    exists n, InPhase a1 n i /\ InPhase a2 n i.

(* ------------------------------ Phase type -------------------------- *)

  Inductive phase :=
  | PhZero
  | PhOne
  | PhPlus: phase -> phase -> phase
  | PhSum : var -> range -> phase -> phase
  .

  (* ------------------------------ PHASE OF ------------------------- *)

  Inductive PhaseOf : inst -> phase -> Prop :=
  | phase_of_block:
    forall c,
    PhaseOf (Block c) PhZero
  | phase_of_sync:
    PhaseOf Sync PhOne
  | phase_of_seq: forall i j ph1 ph2,
    PhaseOf i ph1 ->
    PhaseOf j ph2 ->
    PhaseOf (Seq i j) (PhPlus ph1 ph2)
  | phase_of_for:
    forall x r i ph,
    PhaseOf i ph ->
    PhaseOf (For x r i) (PhSum x r ph)
  .


  Fixpoint phase_of (i:inst) : phase :=
    match i with
    | Block _ => PhZero
    | Sync => PhOne
    | Seq i j => PhPlus (phase_of i) (phase_of j)
    | For x r i => PhSum x r (phase_of i)
    end.

  Lemma phase_of_to_prop:
    forall i,
    PhaseOf i (phase_of i).
  Proof.
    induction i; intros; simpl; constructor; auto.
  Qed.

  Lemma phase_of_from_prop:
    forall i ph,
    PhaseOf i ph ->
    phase_of i = ph.
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H; auto.
    - erewrite IHi1; eauto.
      erewrite IHi2; eauto.
    - erewrite IHi; eauto.
  Qed.

(* ------------------------------- WELL-FORMED ------------------------ *)

  Inductive w_inst :=
  | SSync: Conc.inst -> w_inst
  | SSeq: w_inst -> w_inst -> w_inst
  | SFor : var -> range -> (w_inst * Conc.inst) -> w_inst.

  Inductive w_prog := 
  | prog1: w_inst -> Conc.inst -> w_prog
  | prog2: Conc.inst -> w_prog
  .
 

(* ------------------------------- IN PHASE OF ------------------------ *)

  Inductive sym_acc :=
  | Base: Conc.inst -> sym_acc
  | Decl: var -> range -> sym_acc -> sym_acc
  .

  Fixpoint ph_not_zero_weak (ph:phase) :=
    match ph with
    | PhZero => False
    | PhOne => True
    | PhPlus ph1 ph2 => ph_not_zero_weak ph1 \/ ph_not_zero_weak ph2
    | PhSum x r ph => True
    end.

  Inductive InPhaseOf : sym_acc -> phase -> inst -> Prop :=
  | in_phase_of_block:
    forall c,
    InPhaseOf (Base c) PhZero (Block c)
  | in_phase_of_seq_l:
    forall a i j n,
    InPhaseOf a n i ->
    InPhaseOf a n (Seq i j)
  | in_phase_of_seq_r:
    forall a i j n m,
    PhaseOf i n ->
    InPhaseOf a m j ->
    InPhaseOf a (PhPlus n m) (Seq i j)
  | in_phase_of_for:
    forall a i x r n,
    InPhaseOf a n i ->
    InPhaseOf (Decl x r a) (PhSum x r n) (For x r i).

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

  Lemma phase_of_subst:
    forall i ph,
    PhaseOf i ph ->
    forall x v,
    PhaseOf (i_subst x v i) (ph_subst x v ph).
  Proof.
    intros i ph H.
    induction H; intros y v; simpl.
    - apply phase_of_block.
    - apply phase_of_sync.
    - apply phase_of_seq; auto.
    - destruct (Set_VAR.MF.eq_dec y x); auto using phase_of_for.
  Qed.

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

  Lemma phase_to_run_ph_ne:
    forall n ph,
    RunPhNE ph n ->
    forall i,
    PhaseOf i ph ->
    Phase i n.
  Proof.
    intros n ph H. induction H; intros i Hp; inversion Hp; subst; clear Hp.
    - apply phase_block.
    - apply phase_sync.
    - eauto using phase_seq.
    - eapply phase_for_cons; eauto.
      + eauto using phase_of_subst.
      + auto using phase_of_for.
    - eapply phase_for_eq; eauto using phase_of_subst.
  Qed.

  Lemma run_ph_ne_to_phase:
    forall i n,
    Phase i n ->
    forall ph,
    PhaseOf i ph ->
    RunPhNE ph n.
  Proof.
    intros i n H.
    induction H; intros ph Hp; inversion Hp; subst; clear Hp; try (constructor; fail).
    - econstructor; eauto.
    - eapply run_ph_ne_sum_cons; eauto.
      + auto using phase_of_subst.
      + auto using phase_of_for.
    - eauto using run_ph_ne_sum_eq, phase_of_subst.
  Qed.

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