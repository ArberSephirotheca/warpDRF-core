Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.


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

  Fixpoint Nosync (i:inst) : Prop :=
  match i with
  | Sync => False
  | Block _ => True
  | Seq i j => Nosync i /\ Nosync j
  | For _ _ i => Nosync i
  end.

  Lemma nosync_subst:
    forall i,
    Nosync i ->
    forall x v,
    Nosync (i_subst x v i).
  Proof.
    induction i; intros; simpl in *; auto.
    - destruct H; auto.
    - assert (IHi := IHi H x v0).
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assumption.
      }
      assumption.
  Qed.

  Lemma nosync_inv_subst:
    forall i x v,
    Nosync (i_subst x v i) ->
    Nosync i.
  Proof.
    induction i; intros; simpl in *; auto.
    - destruct H as (Ha, Hb).
      apply IHi1 in Ha.
      apply IHi2 in Hb.
      auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assumption.
      }
      apply IHi in H.
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

  Lemma phase_inv_nosync:
    forall i n,
    Phase i n ->
    Nosync i ->
    n = 0.
  Proof.
    intros i n H.
    induction H; intros; simpl in *.
    - reflexivity.
    - contradiction.
    - destruct H2.
      subst.
      assert (n = 0) by auto.
      assert (m = 0) by auto.
      subst; reflexivity.
    - subst.
      assert (Hx: Nosync (i_subst x (NNum n1) i)) by auto using nosync_subst.
      assert (n = 0) by auto.
      assert (m = 0) by auto.
      subst; reflexivity.
    - auto using nosync_subst.
  Qed.

  Lemma phase_to_nosync:
    forall i,
    Phase i 0 ->
    Nosync i.
  Proof.
    intros i H.
    remember 0.
    generalize dependent Heqn.
    induction H; intros; simpl; auto.
    - inversion Heqn.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      auto.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      subst.
      simpl in *.
      auto.
    - eauto using nosync_inv_subst.
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

End Defs.