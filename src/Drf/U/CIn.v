From Stdlib Require Import Lists.List.
From Faial.Core Require Import Var.
From Faial.Core Require Import AVal.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Util.
From Faial.Core Require Import PairInUtil.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Hist.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Pure.N.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.
From Faial.Drf.U Require Import Run.
From Faial.Drf.U Require Import IIn.

Section Defs.
  Context `{T:Tasks}.

  Definition CRun := RunAll TID_COUNT.

  Definition CCanRun u := (forall i, i < TID_COUNT -> CanRun i u).

  Transparent CRun.

  Lemma c_run_to_can_run:
    forall c h,
    CRun c h ->
    CCanRun c.
  Proof.
    intros c h H.
    unfold CCanRun.
    intros.
    apply run_all_inv_run with (m:=i) in H; auto.
    destruct H as (H', (Hr, _)).
    eauto using run_to_can_run.
  Qed.

  Lemma c_run_subst:
    forall x e e' c h n,
    Pure.N.Exp.NEq e e' ->
    Pure.N.Exp.NStep e' n ->
    CRun (f x (from_pure e) c) h ->
    CRun (f x (from_pure e') c) h.
  Proof.
    intros.
    apply run_all_impl with (c1:=f x (from_pure e) c); auto.
    intros.
    apply run_subst with (e1:=from_pure e)(n:=n); eauto.
    - rewrite <- N.Exp.n_step_from_pure.
      rewrite H.
      assumption.
    - rewrite <- N.Exp.n_step_from_pure.
      assumption.
  Qed.

  Inductive CIn : access_val -> t -> Prop :=
  | c_in_def:
    forall a c,
    av_owner a < TID_COUNT ->
    IIn a c ->
    CIn a c.

  Lemma c_in_1:
    forall c h a,
    RunAll TID_COUNT c h ->
    List.In a h ->
    CIn a c.
  Proof.
    intros.
    eauto using c_in_def, run_all_inv_in_eq, run_all_in_to_i_in.
  Qed.

  Lemma c_in_2:
    forall c h a,
    RunAll TID_COUNT c h ->
    CIn a c ->
    List.In a h.
  Proof.
    intros.
    invc H0.
    eapply run_all_i_in_to_in; eauto.
  Qed.

  Lemma c_in_seq_l:
    forall a i j,
    CIn a i ->
    CIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using i_in_seq_l.
  Qed.

  Lemma c_in_seq_r:
    forall a i j,
    CIn a j ->
    CIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using i_in_seq_r.
  Qed.

  Lemma c_in_inv_seq:
    forall a i j,
    CIn a (Seq i j) ->
    CIn a i \/ CIn a j.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H1; subst; clear H1; auto using c_in_def.
  Qed.

  Lemma c_in_subst:
    forall (x : VAR.t) (a : access_val) (i : t) (v v' : Pure.N.Exp.nexp) (n : nat),
    Pure.N.Exp.NStep v n ->
    Pure.N.Exp.NStep v' n ->
    CIn a (f x (from_pure v) i) ->
    CIn a (f x (from_pure v') i).
  Proof.
    intros.
    invc H1.
    eapply i_in_subst with (v':=v') in H3; eauto.
    eauto using c_in_def.
  Qed.

  (* -------------------------------- C PAIR IN ---------------------- *)

  Inductive CPairIn : (access_val * access_val) -> t -> Prop :=
  | c_pair_in_def:
    forall a1 a2 c,
    CIn a1 c ->
    CIn a2 c ->
    CPairIn (a1, a2) c.

  Lemma c_pair_in_1:
    forall c h p,
    RunAll TID_COUNT c h ->
    PairIn p h ->
    CPairIn p c.
  Proof.
    intros.
    invc H0.
    eauto using c_pair_in_def, c_in_1.
  Qed.

  Lemma c_pair_in_seq_l:
    forall a i j,
    CPairIn a i ->
    CPairIn a (Seq i j).
  Proof.
    intros.
    invc H.
    apply c_pair_in_def; auto using c_in_seq_l.
  Qed.

  Lemma c_pair_in_seq_r:
    forall a i j,
    CPairIn a j ->
    CPairIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply c_pair_in_def; auto using c_in_seq_r.
  Qed.

  Lemma c_in_skip:
    forall a,
    ~ CIn a Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    inversion H0; subst; clear H0.
  Qed.

  Lemma c_in_seq_seq:
    forall a c1 c2 c3,
    CIn a (Seq (Seq c1 c2) c3) ->
    CIn a (Seq c1 (Seq c2 c3)).
  Proof.
    intros.
    apply c_in_inv_seq in H.
    destruct H as [H|H]. {
      apply c_in_inv_seq in H.
      destruct H; auto using c_in_seq_l, c_in_seq_r.
    }
    auto using c_in_seq_l, c_in_seq_r.
  Qed.

  Lemma c_pair_in_skip:
    forall p,
    ~ CPairIn p Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    apply c_in_skip in H.
    contradiction.
  Qed.
End Defs.
