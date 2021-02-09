Require Import Coq.Lists.List.

Require Import Tasks.
Require Import AccExp.
Require Import Tictac.
Require SymHist.
Require SymExec.
Require Align.
Require SHCompiler.
Require PhaseSplit.
Require WLang.
Require Hist.
Require VHist.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Fixpoint ph_to_hist (p:PhaseSplit.phase) :=
    match p with
    | PhaseSplit.Phase c => SymHist.translate TID_COUNT c
    | PhaseSplit.Decl x r p => SymExec.Decl x r (ph_to_hist p)
    end.

  Definition aligned_to_sym_hist P :=
    List.map ph_to_hist (PhaseSplit.split P).

  Definition w_to_s P :=
    aligned_to_sym_hist (Align.align P).

  Notation history := (list access_val).

  Inductive SRun : list (SymExec.inst (I:=SymHist.SymAcc)) -> list history -> Prop :=
  | s_run_nil:
    SRun [] []
  | s_run_cons:
    forall l ms h m,
    SRun l ms ->
    SymExec.Run h m ->
    SRun (h::l) (m ++ ms).

  Lemma s_run_inv_in:
    forall hs m,
    SRun hs m ->
    forall p,
    PairInUtil.MPairIn p m ->
    exists h m',
    List.In h hs /\ SymExec.Run h m' /\ PairInUtil.MPairIn p m'.
  Proof.
    intros hs m H.
    induction H; intros. {
      apply PairInUtil.m_pair_in_nil in H.
      contradiction.
    }
    apply PairInUtil.m_pair_in_app_or in H1.
    destruct H1 as [Hi|Hi]. {
      eauto using in_eq.
    }
    edestruct IHSRun as (h1, (m1, (Ha, (Hb, Hc)))); eauto.
    exists h1.
    eauto using in_cons.
  Qed.

  Lemma s_run_inv:
    forall l m,
    SRun l m ->
    forall x,
    List.In x l ->
    exists h,
    SymExec.Run x h /\incl h m.
  Proof.
    intros l m H.
    induction H; intros. {
      contradiction.
    }
    rename_hyp (In _ _) as hi.
    destruct hi as [hi|hi]. {
      subst.
      exists m.
      auto using InUtil.incl_app_refl_l.
    }
    assert (IHSRun := IHSRun x hi).
    destruct IHSRun as (hx, (Hr, hj)).
    exists hx.
    split; auto using incl_appr.
  Qed.

  Lemma in_1:
    forall p ph,
    SymExec.IPairIn p (ph_to_hist ph) ->
    PhaseSplit.PPairIn p ph.
  Proof.
    (* TODO: MEDIUM *)
  Admitted.

  Lemma in_2:
    forall p ph,
    PhaseSplit.PPairIn p ph ->
    SymExec.IPairIn p (ph_to_hist ph).
  Proof.
    (* TODO: MEDIUM *)
  Admitted.

  Theorem drf_1:
    forall P h1 h2,
    ~ WLang.WVar TID P ->
    WLang.WRun P h1 ->
    SRun (w_to_s P) h2 ->
    WLang.Distinct P ->
    PhaseSplit.CanRun (fst (Align.align P)) ->
    VHist.Safe h1 ->
    Hist.MSafeStrong h2.
  Proof.
    intros.
    unfold Hist.MSafeStrong, VHist.Safe in *.
    intros.
    rename_hyp (forall x y, _) as Hi.
    apply Hi; auto; clear Hi.
    rename_hyp (PairInUtil.MPairIn _ _) as Hi.
    eapply s_run_inv_in in Hi; eauto.
    destruct Hi as (hs, (m1, (Hi, (Hr, Hp)))).
    apply WLang.i_pair_in_2 with (i:=P); auto.
    eapply SymExec.run_m_pair_in_to_i_pair_in in Hp; eauto.
    unfold w_to_s, aligned_to_sym_hist in Hi.
    apply in_map_iff in Hi.
    destruct Hi as (ph, (?, Hi)).
    subst.
    apply in_1 in Hp.
    assert (Hp': PhaseSplit.InPhases (x,y) (PhaseSplit.split (Align.align P))). {
      eexists.
      eauto.
    }
    apply PhaseSplit.in_2 in Hp'.
    - apply Align.in_1; auto.
      eauto using WLang.run_to_can_run.
    - eauto using Align.distinct_w_to_a.
    - assumption.
  Qed.

  Theorem drf_2:
    forall P h1 h2,
    ~ WLang.WVar TID P ->
    WLang.WRun P h1 ->
    SRun (w_to_s P) h2 ->
    WLang.Distinct P ->
    PhaseSplit.CanRun (fst (Align.align P)) ->
    Hist.MSafeStrong h2 ->
    VHist.Safe h1.
  Proof.
    intros.
    unfold Hist.MSafeStrong, VHist.Safe in *.
    intros.
    rename_hyp (forall x y, _) as Hi.
    apply Hi; auto; clear Hi.
    rename_hyp (VHist.MPairIn (x, y) h1) as hp.
    (* from mem to proto *)
    eapply WLang.i_pair_in_1 in hp; eauto.
    (* from W to A *)
    apply Align.in_2 in hp; eauto using WLang.run_to_can_run.
    (* From A to PH *)
    apply PhaseSplit.in_1 in hp; auto using Align.distinct_w_to_a.
    (* From PH to S.T. *)
    destruct hp as (ph, (Hi, Hp)).
    apply in_2 in Hp.
    (* symb trace to h2 *)
    unfold w_to_s in *.
    unfold aligned_to_sym_hist in *.
    rename_hyp (SRun _ _) as hs.
    apply s_run_inv with (x:=ph_to_hist ph) in hs; auto. 2: {
      rewrite in_map_iff.
      eauto.
    }
    destruct hs as (h, (Hsr, hi)).
    eapply SymExec.run_i_pair_in_to_m_pair_in with (h0:=h) in Hp; eauto.
    eauto using PairInUtil.m_pair_in_incl.
  Qed.
End Defs.