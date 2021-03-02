Require Import Coq.Lists.List.

Require Import Tasks.
Require Import AExp.
Require Import Tictac.
Require ULang.
Require Align.
Require Sequentialize.
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
    | PhaseSplit.Phase c => Sequentialize.sequentialize c
    | PhaseSplit.Decl x r p => TLang.Decl x r (ph_to_hist p)
    end.

  Definition aligned_to_sym_hist P :=
    List.map ph_to_hist (PhaseSplit.split P).

  Definition w_to_s P :=
    aligned_to_sym_hist (Align.align P).

  Notation history := (list access_val).

  Inductive SRun : list TLang.inst -> list history -> Prop :=
  | s_run_nil:
    SRun [] []
  | s_run_cons:
    forall l ms h m,
    SRun l ms ->
    TLang.Run h m ->
    SRun (h::l) (m ++ ms).

  Lemma s_run_inv_in:
    forall hs m,
    SRun hs m ->
    forall p,
    PairInUtil.MPairIn p m ->
    exists h m',
    List.In h hs /\ TLang.Run h m' /\ PairInUtil.MPairIn p m'.
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
    TLang.Run x h /\incl h m.
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

  Lemma ph_to_hist_phase:
    forall u,
    ph_to_hist (PhaseSplit.Phase u) = Sequentialize.sequentialize u.
  Proof.
    intros.
    reflexivity.
  Qed.
  Opaque Sequentialize.sequentialize.

  Lemma ph_to_hist_subst:
    forall x v ph,
    x <> T1 ->
    x <> T2 ->
    x <> TID ->
    NExp.NClosed v ->
    ~ PhaseSplit.Var x ph ->
    TLang.i_subst x v (ph_to_hist ph) =
    ph_to_hist (PhaseSplit.ph_subst x v ph). 
  Proof.
    induction ph; intros ht1 ht2 htid hc hv; simpl; simpl in hv.
    - rewrite Sequentialize.sequentialize_subst_rw; auto.
    - rename v0 into y.
      destruct (Var.VAR.eq_dec x y). {
        reflexivity.
      }
      rewrite IHph; auto.
  Qed.

  Transparent Sequentialize.sequentialize.

  Lemma in_1: (* TODO: EASY *)
    forall p ph,
    TLang.IPairIn p (ph_to_hist ph) ->
    ~ PhaseSplit.Var TID ph ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    T1 <> T2 ->
    PhaseSplit.Distinct ph ->
    PhaseSplit.PPairIn p ph.
  Proof.
    intros p ph hp.
    remember (ph_to_hist ph) as P.
    generalize dependent ph.
    induction hp; intros ph heq htid ht1 ht2 htneq hd; destruct ph; invc heq.
    - constructor.
      apply Sequentialize.i_pair_in_1; auto.
      unfold Sequentialize.sequentialize.
      eapply TLang.i_pair_in_decl; eauto.
   - simpl in *.
    rewrite ph_to_hist_subst in hp; auto using NExp.n_closed_num. 2: { intuition. }
    assert (hq: PhaseSplit.PPairIn p (PhaseSplit.ph_subst v (NExp.NNum n) ph)). {
      apply IHhp; auto using PhaseSplit.not_var_subst.
      - simpl in *.
        rewrite ph_to_hist_subst; auto using NExp.n_closed_num.
        intuition.
      - auto using PhaseSplit.not_var_subst.
      - admit.
      - admit.
      - admit.
    }
    simpl in *.
    econstructor; eauto using RExp.r_pick_def.
  Admitted.

  Lemma in_2: (* TODO: MEDIUM *)
    forall x y ph,
    PhaseSplit.PPairIn (x, y) ph ->
    access_tid x <> access_tid y ->
    ~ PhaseSplit.Var TID ph ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    T1 <> T2 ->
    PhaseSplit.Distinct ph ->
    TLang.IPairIn (x,y) (ph_to_hist ph).
  Proof.
    intros x y ph H.
    remember (x, y) as p.
    generalize dependent x.
    generalize dependent y.
    induction H; simpl; intros a1 a2 heq hneq hv ht1 ht2 ht1t2 hvv.
    - subst.
      auto using Sequentialize.i_pair_in_2.
    - destruct r as (e1, e2).
      invc H.
      eapply TLang.i_pair_in_decl; eauto.
      rewrite ph_to_hist_subst; auto using NExp.n_closed_num.
      
       2: { intuition. } 
      eapply IHPPairIn; eauto.
      + admit.
      + admit.
      + admit.
      + admit.
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
    eapply TLang.run_m_pair_in_to_i_pair_in in Hp; eauto.
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
    - assert (ALang.PDistinct (Align.align P)). {
        eauto using Align.distinct_w_to_a.
      }
      destruct (Align.align P) as (Px, cx).
      simpl in *.
      intuition.
    - assumption.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

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
    apply PhaseSplit.in_1 in hp. 2: {
      assert (ALang.PDistinct (Align.align P)) by auto using Align.distinct_w_to_a.
      destruct (Align.align P) as (Px,cx).
      simpl in *.
      intuition. 
    }
    (* From PH to S.T. *)
    destruct hp as (ph, (Hi, Hp)).
    apply in_2 in Hp; auto using t1_neq_t2.
    + (* symb trace to h2 *)
      unfold w_to_s in *.
      unfold aligned_to_sym_hist in *.
      rename_hyp (SRun _ _) as hs.
      apply s_run_inv with (x:=ph_to_hist ph) in hs; auto. 2: {
        rewrite in_map_iff.
        eauto.
      }
      destruct hs as (h, (Hsr, hi)).
      eapply TLang.run_i_pair_in_to_m_pair_in with (h0:=h) in Hp; eauto.
      eauto using PairInUtil.m_pair_in_incl.
    + admit.
    + admit.
    + admit.
    + admit.
  Admitted.

  Theorem drf:
    forall P h1 h2,
    (* Things run *)
    WLang.WRun P h1 ->
    SRun (w_to_s P) h2 ->
    PhaseSplit.CanRun (fst (Align.align P)) ->
    (* Loops have distinct *)
    WLang.Distinct P ->
    (* TID is not redeclared in a loop *)
    ~ WLang.WVar TID P ->
    (* Main result: *)
    Hist.MSafeStrong h2 <-> VHist.Safe h1.
  Proof.
    intros.
    split; eauto using drf_1, drf_2.
  Qed.
End Defs.