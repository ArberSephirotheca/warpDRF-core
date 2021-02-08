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

  Lemma i_pair_hist_to_ph:
    forall p ph,
    SymExec.IPairIn p (ph_to_hist ph) ->
    PhaseSplit.PPairIn p ph.
  Proof.
  Admitted.

  Theorem drf_1:
    forall P h1 h2,
    ~ WLang.WVar TID P ->
    WLang.WRun P h1 ->
    SRun (w_to_s P) h2 ->
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
    apply i_pair_hist_to_ph in Hp.
    assert (Hp': PhaseSplit.InPhases (x,y) (PhaseSplit.split (Align.align P))). {
      eexists.
      eauto.
    }
    apply PhaseSplit.in_2 in Hp'.
    - apply Align.in_1; auto.
      + admit.
      + admit.
    - admit.
    - admit.
  Admitted.
End Defs.