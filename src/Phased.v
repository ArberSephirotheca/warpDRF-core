Require Import Coq.Lists.List.
Require Import NExp.
Require Import Var.
Require Import AccExp.
Require Import Tasks.
Require Import VHist.
Require Conc.

Require Import ALang.

Require Import Lia.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.

  Notation history := (list access_val).
  Notation mhistory := (list history).

  Inductive phased :=
  | Phased1: Conc.inst -> phased
  | Phased2: inst -> Conc.inst -> phased
  .

  Definition skip_for (i:inst) :=
    match i with
    | For _ _ j => j
    | _ => i
    end.
(*
  Inductive Norm: inst -> Prop :=
  | norm_sync:
    Norm Sync
  | norm_block:
    forall c,
    Norm (Block c)
  | norm_seq:
    forall i j,
    Norm i ->
    Norm (skip_for j) ->
    Norm (Seq i j).
*)

  Fixpoint NormEx (i: inst) (for_ok:bool) : Prop :=
    match i with
    | Sync => True
    | Block _ => True
    | Seq i j => NormEx i false /\ NormEx j true
    | For _ _ _ => for_ok = true
    end.

  Definition Norm i := NormEx i false.
(*
  Lemma norm_ex_false:
    forall i,
    Norm
*)
(*
  Lemma
    forall i,
    (exists x r j, i = For x r j) \/  
*)
(*
  Lemma skip_for_i_subst_rw:
    forall i x v,
    skip_for (i_subst x v i) = i_subst x v (skip_for i).
  Proof.
    induction i; intros; simpl; auto.
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
  Qed.
*)
  Lemma norm_ex_subst:
    forall i b,
    NormEx i b ->
    forall x v,
    NormEx (i_subst x v i) b.
  Proof.
    induction i; intros; simpl in *; auto.
    destruct H as (Ha, Hb).
    apply IHi1 with (x:=x) (v:=v) in Ha.
    apply IHi2 with (x:=x) (v:=v) in Hb.
    auto.
  Qed.

  Lemma norm_ex_incl:
    forall i,
    NormEx i false ->
    NormEx i true.
  Proof.
    intros.
    destruct i; simpl in *; auto.
  Qed.

  Lemma norm_subst:
    forall i,
    Norm i ->
    forall x v,
    Norm (i_subst x v i).
  Proof.
    unfold Norm.
    intros.
    auto using norm_ex_subst.
  Qed.

  Lemma norm_for:
    forall x r i,
    ~ Norm (For x r i).
  Proof.
    unfold Norm.
    intros.
    intros N.
    simpl in *.
    inversion N.
  Qed.

  Lemma norm_seq_1:
    forall i j,
    Norm i ->
    Norm j ->
    Norm (Seq i j).
  Proof.
    unfold Norm; intros i j Hni Hnj.
    simpl.
    split; auto using norm_ex_incl.
  Qed.

  Lemma norm_seq_for:
    forall i x r j,
    Norm i ->
    Norm j ->
    Norm (Seq i (For x r j)).
  Proof.
    unfold Norm; simpl; intros.
    split; auto.
  Qed.

  Lemma norm_seq_2:
    forall i i' j,
    Norm (Seq i' j) ->
    Norm i ->
    Norm (Seq i j).
  Proof.
    unfold Norm.
    intros.
    inversion H; subst; clear H.
    simpl.
    split; auto.
  Qed.

  Lemma norm_sync:
    Norm Sync.
  Proof.
    unfold Norm; simpl; auto.
  Qed.

  Lemma norm_inv_seq_l:
    forall i j,
    Norm (Seq i j) ->
    Norm i.
  Proof.
    unfold Norm.
    intros.
    simpl in *.
    destruct H; auto.
  Qed.

  Definition PNorm (p:phased) : Prop :=
    match p with
    | Phased1 _ => True
    | Phased2 i _ => Norm i
    end.

  Inductive Run: inst -> list history -> Prop :=
  | run_sync:
    Run Sync []
  | run_block:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) [h]
  | run_seq: forall i j mh_i mh_j mh,
    Run i mh_i ->
    Run j mh_j ->
    mh_i ++ mh_j = mh ->
    Run (Seq i j) mh
  | run_for_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) m1 ->
    Run (For x (NNum (S n1), NNum n2) i) m2 ->
    m1 ++ m2 = m3 ->
    Run (For x (e1, e2) i) m3
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run (For x (e1, e2) i) []
  .

  (* ----------------------- Acces membership ---------------------- *)

  Inductive IPairIn (p:access_val * access_val) : inst -> Prop :=
  | i_pair_in_block:
    forall c,
    CPairIn p c ->
    IPairIn p (Block c)
  | i_pair_in_seq_l:
    forall i j,
    IPairIn p i ->
    IPairIn p (Seq i j)
  | i_pair_in_seq_r:
    forall i j,
    IPairIn p j ->
    IPairIn p (Seq i j)
  | i_pair_in_for:
    forall e1 e2 n1 n2 n i x,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IPairIn p (i_subst x (NNum n) i) ->
    IPairIn p (For x (e1, e2) i)
  .

  Lemma i_pair_in_for_cons:
    forall e1 e2 n1 n2 x i p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    IPairIn p (For x (NNum (S n1), NNum n2) i) ->
    IPairIn p (For x (e1, e2) i).
  Proof.
    intros.
    inversion H2; subst; clear H2.
    assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
    assert (n3 = n2) by eauto using n_step_num, n_step_fun.
    subst.
    eapply i_pair_in_for with (n:=n); eauto.
    lia.
  Qed.

  Lemma i_pair_in_1:
    forall i m,
    Run i m ->
    ~ Var TID i ->
    forall p,
    PairInUtil.MPairIn p m ->
    IPairIn p i.
  Proof.
    intros i m H.
    induction H; intros Hv p Hi.
    - apply PairInUtil.m_pair_in_nil in Hi.
      contradiction.
    - apply PairInUtil.m_pair_in_inv in Hi.
      destruct Hi as [Hi|Hi]. {
        constructor.
        eapply c_pair_in_def_2; eauto.
      }
      apply PairInUtil.m_pair_in_nil in Hi.
      contradiction.
    - subst.
      apply PairInUtil.m_pair_in_app_or in Hi.
      simpl in *.
      destruct Hi as [Hi|Hi]. {
        eapply i_pair_in_seq_l; eauto.
      }
      eapply i_pair_in_seq_r; eauto.
    - subst.
      apply PairInUtil.m_pair_in_app_or in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_pair_in_for with (n:=n1); eauto.
        apply IHRun1; auto.
        intros N.
        apply var_subst_inv_1 in N.
        simpl in *.
        intuition.
      }
      apply IHRun2 in Hi.
      2: { simpl in *. intuition. }
      eauto using i_pair_in_for_cons.
    - apply PairInUtil.m_pair_in_nil in Hi.
      contradiction.
  Qed.

  Inductive Phase : inst -> nat -> Prop :=
  | phase_block:
    forall c,
    Phase (Block c) 1
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
  | phase_for_nil:
    forall i x e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Phase (For x (e1, e2) i) 0
  .

  (* --------------------------- IN PHASE ------------------- *) 

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
    InPhase a o (For x (e1, e2) i)
  .

  (* --------------------- IN PHASE 2 -------------------- *)


  Definition InPhase2 a n (p:phased) :=
    match p with
    | Phased1 c => n = 0 /\ Conc.IIn a c
    | Phased2 i c =>
      InPhase a n i \/
      Phase i n /\ Conc.IIn a c
    end.

  Definition Phase2 (p:phased) (n:nat) : Prop :=
    match p with
    | Phased1 c => n = 0
    | Phased2 i _ => Phase i n
    end.



  Lemma in_phase2_1:
    forall a c,
    Conc.IIn a c ->
    InPhase2 a 0 (Phased1 c).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma in_phase2_2_l:
    forall a n i c,
    InPhase a n i ->
    InPhase2 a n (Phased2 i c).
  Proof.
    intros.
    simpl.
    left.
    assumption.
  Qed.

End Defs.