Require Import Coq.Lists.List.

Require Import Tictac.
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
Require ALang.
Require Import Lia.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context `{A:Access}.

  (*
    ~~~~~ Function split ~~~~~~~

    -> PhaseSplit.split.

      Takes a protocol and breaks it into a list of sub-protocol, each
      sub-protocol is called a phase. For instance,

      PhaseSplit.split(for^s x in n..m { P; Q}) =
        [ for^s x in n..m { P }; for^s x in n..m {Q} ]

    -> ph_to_hist: takes a single phase (sub-protocol) and handles the cases of
       synchronized loops or unsynchronized protocols, delegating the latter
       to Sequentialize.sequentialize.

    -> Sequentialize.sequentialize: takes an unsynchronized protocol and does
       what is in Figure 4.

    *)

  Fixpoint ph_to_hist (p:PhaseSplit.phase) :=
    match p with
      (* case: u;sync *)
    | PhaseSplit.Phase c => Sequentialize.sequentialize c
      (* case: for^s x in n .. m {q} *)
    | PhaseSplit.Decl x r p => TLang.Decl x r (ph_to_hist p)
    end.

  Fixpoint split_a (a:ALang.n_inst) : list TLang.inst :=
  match a with
  | ALang.NSync u => [ Sequentialize.sequentialize u ]
  | ALang.NSeq p q => split_a p ++ split_a q
  | ALang.NFor p x r q => split_a p ++ List.map (fun p => TLang.Decl x r p) (split_a q)
  end.

  Definition split_a_u (a_u: ALang.p_inst) :=
    let (a, u) := a_u in
    split_a (ALang.NSeq a (ALang.NSync u)).

  Definition split P :=
    List.map ph_to_hist (PhaseSplit.split P).

  Lemma map_ph_to_hist:
    forall v r l,
    map ph_to_hist (map (PhaseSplit.Decl v r) l) =
    map (TLang.Decl v r) (map ph_to_hist l).
  Proof.
    induction l. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma ph_to_hist_eq_split_a:
    forall a,
    List.map ph_to_hist (PhaseSplit.a_split a) = split_a a.
  Proof.
    induction a.
    - simpl.
      reflexivity.
    - simpl.
      repeat rewrite map_app.
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
    - simpl.
      repeat rewrite map_app.
      rewrite IHa1.
      f_equal.
      rewrite <- IHa2.
      rewrite map_ph_to_hist.
      reflexivity.
  Qed.

  Lemma split_a_u_eq_split:
    forall i,
    split i = split_a_u i.
  Proof.
    intros (a, u).
    generalize dependent u.
    unfold split.
    induction a; intros u.
    - simpl.
      reflexivity.
    - simpl in *.
      rewrite map_app.
      assert (IHa1 := IHa1 u).
      assert (IHa2 := IHa2 u).
      repeat rewrite map_app in *.
      f_equal.
      rewrite app_inv_tail_iff in *.
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
    - simpl in *.
      f_equal.
      assert (IHa1 := IHa1 u).
      assert (IHa2 := IHa2 u).
      repeat rewrite map_app in *.
      repeat rewrite app_inv_tail_iff in *.
      rewrite map_ph_to_hist.
      rewrite IHa2.
      rewrite IHa1.
      reflexivity.
  Qed.

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

  Lemma in_1:
    forall p ph,
    TLang.IPairIn p (ph_to_hist ph) ->
    ~ PhaseSplit.Var TID ph ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    PhaseSplit.Distinct ph ->
    PhaseSplit.PPairIn p ph.
  Proof.
    intros p ph hp.
    remember (ph_to_hist ph) as P.
    generalize dependent ph.
    induction hp; intros ph heq htid ht1 ht2 hd; destruct ph; invc heq.
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
      - apply PhaseSplit.not_occurs_subst; eauto using NExp.n_step_to_not_free.
      - apply PhaseSplit.not_occurs_subst; eauto using NExp.n_step_to_not_free.
      - destruct hd as (_, Hd).
        auto using PhaseSplit.distinct_subst.
    }
    simpl in *.
    econstructor; eauto using RExp.r_pick_def.
  Qed.

  Lemma in_2:
    forall x y ph,
    PhaseSplit.PPairIn (x, y) ph ->
    access_tid x <> access_tid y ->
    ~ PhaseSplit.Var TID ph ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    PhaseSplit.Distinct ph ->
    TLang.IPairIn (x,y) (ph_to_hist ph).
  Proof.
    intros x y ph H.
    remember (x, y) as p.
    generalize dependent x.
    generalize dependent y.
    induction H; simpl; intros a1 a2 heq hneq hv ht1 ht2 hvv.
    - subst.
      auto using Sequentialize.i_pair_in_2.
    - destruct r as (e1, e2).
      invc H.
      eapply TLang.i_pair_in_decl; eauto.
      rewrite ph_to_hist_subst; auto using NExp.n_closed_num.
      2: { intuition. } 
      eapply IHPPairIn; eauto using PhaseSplit.not_var_subst.
      + apply PhaseSplit.not_occurs_subst; eauto using NExp.n_step_to_not_free.
      + apply PhaseSplit.not_occurs_subst; eauto using NExp.n_step_to_not_free.
      + apply PhaseSplit.distinct_subst.
        intuition.
  Qed.

  Lemma a_split_occurs:
    forall x a ph,
    PhaseSplit.Occurs x ph ->
    In ph (PhaseSplit.a_split a) ->
    ALang.Occurs x a.
  Proof.
    induction a; simpl; intros ph he hi; intuition.
    - subst.
      simpl in *.
      assumption.
    - apply in_app_or in hi.
      destruct hi as [hi|hi]; eauto.
    - apply in_app_or in hi.
      destruct hi as [hi|hi]; eauto.
      apply in_map_iff in hi.
      destruct hi as (ph', (he', hi)).
      subst.
      simpl in *.
      intuition.
      eauto.
  Qed.

  Lemma a_split_var:
    forall x a ph,
    PhaseSplit.Var x ph ->
    In ph (PhaseSplit.a_split a) ->
    ALang.Var x a.
  Proof.
    induction a; intros ph hv hi; simpl in *; intuition.
    - subst.
      simpl in *.
      assumption.
    - apply in_app_or in hi.
      destruct hi as [hi|hi]; eauto.
    - apply in_app_or in hi.
      destruct hi as [hi|hi]; eauto.
      apply in_map_iff in hi.
      destruct hi as (ph', (he, hi)).
      subst.
      simpl in *.
      intuition.
      right.
      eauto.
  Qed.

  Lemma a_split_distinct:
    forall a ph,
    ALang.Distinct a ->
    In ph (PhaseSplit.a_split a) ->
    PhaseSplit.Distinct ph.
  Proof.
    induction a; simpl; intros ph hd hi; auto.
    - intuition.
      subst.
      simpl.
      assumption.
    - apply in_app_or in hi.
      intuition.
    - apply in_app_or in hi.
      destruct hi as [hi|hi]; simpl in hi; intuition.
      apply in_map_iff in hi.
      destruct hi as (ph', (he, hi)).
      subst.
      simpl in *.
      intuition.
      eauto using a_split_var.
  Qed.

  Lemma split_var:
    forall x P ph,
    PhaseSplit.Var x ph ->
    In ph (PhaseSplit.split P) ->
    ALang.PVar x P.
  Proof.
    induction P; simpl; intros ph hv he.
    rewrite in_app_iff in *.
    destruct he as [he|he]. {
      left.
      eauto using a_split_var.
    }
    simpl in *.
    intuition.
    subst.
    simpl in *.
    auto.
  Qed.

  Lemma split_occurs:
    forall x P ph,
    PhaseSplit.Occurs x ph ->
    In ph (PhaseSplit.split P) ->
    ALang.POccurs x P.
  Proof.
    induction P; simpl; intros ph hv he.
    rewrite in_app_iff in *.
    destruct he as [he|he]. {
      left.
      eapply a_split_occurs; eauto.
    }
    simpl in *.
    intuition.
    subst.
    simpl in *.
    auto.
  Qed.

  Lemma split_distinct:
    forall P ph,
    ALang.PDistinct P ->
    In ph (PhaseSplit.split P) ->
    PhaseSplit.Distinct ph.
  Proof.
    intros.
    destruct P as (px, cx).
    simpl in *.
    rewrite in_app_iff in *.
    intuition.
    - eauto using a_split_distinct.
    - simpl in *.
      intuition.
      subst.
      simpl.
      auto.
  Qed.

  Lemma align_var:
    forall x P,
    ALang.PVar x (Align.align P) ->
    WLang.WVar x P.
  Proof.
    induction P; simpl; intros; intuition.
    - destruct (Align.align P1) as (Px1, cx1) eqn:r1.
      destruct (Align.align P2) as (Px2, cx2) eqn:r2.
      simpl in *.
      intuition.
      rename_hyp (ALang.Var _ (ALang.n_seq _ _)) as hc.
      apply Align.var_inv_seq in hc.
      intuition.
    - destruct r as (e1, e2).
      destruct (Align.align P) as (Px1, cx1) eqn:r1.
      simpl in *.
      intuition.
      + rename_hyp (ALang.Var _ (ALang.n_seq _ _)) as hc.
        apply Align.var_inv_seq in hc.
        intuition.
        rename_hyp (ALang.Var _ (ALang.subst _ _ _)) as hc.
        apply ALang.var_inv_subst in hc.
        auto.
      + rename_hyp (ALang.Var _ (ALang.n_seq _ _)) as hc.
        apply Align.var_inv_seq in hc.
        intuition. {
          rename_hyp (ULang.Var _ (ULang.i_subst _ _ _)) as hc.
          apply ULang.var_inv_subst in hc.
          auto.
        }
        rename_hyp (ALang.Var _ (ALang.n_seq _ _)) as hc.
        apply Align.var_inv_seq in hc.
        intuition.
        rename_hyp (ULang.Var _ (ULang.i_subst _ _ _)) as hc.
        apply ULang.var_inv_subst in hc.
        auto.
      + rename_hyp (ULang.Var _ (ULang.c_seq _ _)) as hc.
        apply ULang.var_inv_c_seq in hc.
        intuition. {
          rename_hyp (ULang.Var _ (ULang.i_subst _ _ _)) as hc.
          apply ULang.var_inv_subst in hc.
          auto.
        }
        rename_hyp (ULang.Var _ (ULang.i_subst _ _ _)) as hc.
        apply ULang.var_inv_subst in hc.
        auto.
  Qed.

  Lemma align_occurs:
    forall x P,
    ALang.POccurs x (Align.align P) ->
    WLang.Occurs x P.
  Proof.
    induction P; simpl; intros; intuition.
    - destruct (Align.align P1) as (Px1, cx1) eqn:r1.
      destruct (Align.align P2) as (Px2, cx2) eqn:r2.
      simpl in *.
      intuition.
      rename_hyp (ALang.Occurs _ (ALang.n_seq _ _)) as hc.
      apply Align.occurs_inv_seq in hc.
      intuition.
    - destruct r as (e1, e2).
      destruct (Align.align P) as (Px1, cx1) eqn:r1.
      simpl in *.
      intuition.
      + rename_hyp (ALang.Occurs _ (ALang.n_seq _ _)) as hc.
        apply Align.occurs_inv_seq in hc.
        intuition.
        rename_hyp (ALang.Occurs _ (ALang.subst _ _ _)) as hc.
        apply ALang.occurs_inv_subst in hc.
        intuition.
      + rename_hyp (ALang.Occurs _ (ALang.n_seq _ _)) as hc.
        apply Align.occurs_inv_seq in hc.
        destruct hc as [hc|hc]. {
          apply ULang.occurs_inv_subst in hc.
          destruct hc as [hc|hc]; simpl in hc; intuition.
        }
        apply Align.occurs_inv_seq in hc.
        destruct hc as [hc|hc]; intuition.
        simpl in hc.
        apply ULang.occurs_inv_subst in hc.
        simpl in hc.
        intuition.
      + rename_hyp (ULang.Occurs _ (ULang.c_seq _ _)) as hc.
        apply ULang.occurs_inv_c_seq in hc.
        destruct hc as [hc|hc]; simpl in hc. {
          apply ULang.occurs_inv_subst in hc.
          simpl in hc.
          intuition.
        }
        apply ULang.occurs_inv_subst in hc.
        simpl in hc.
        intuition.
  Qed.

  Lemma align_distinct:
    forall P,
    WLang.Distinct P ->
    ALang.PDistinct (Align.align P).
  Proof.
    induction P; simpl; intros; auto.
    - destruct H as (Ha, Hb).
      destruct (Align.align P1) as (Px1, cx1) eqn:r1.
      destruct (Align.align P2) as (Px2, cx2) eqn:r2.
      simpl.
      repeat split; simpl in *; intuition.
      apply Align.distinct_seq; auto.
    - destruct r as (e1, e2).
      destruct (Align.align P) as (Px1, cx1) eqn:r1.
      simpl in *.
      destruct H as (ha, (hb, (hc, (hd, he)))).
      repeat split.
      + apply Align.distinct_seq; auto.
        apply ALang.distinct_subst.
        intuition.
      + intros N.
        apply ALang.var_inv_n_seq in N.
        destruct N as [N|N]. {
          apply ULang.var_inv_subst in N.
          contradict hb.
          apply align_var.
          rewrite r1.
          simpl.
          auto.
        }
        apply ALang.var_inv_n_seq in N.
        destruct N as [N|N]. {
          apply ULang.var_inv_subst in N.
          auto.
        }
        contradict hb.
        apply align_var.
        rewrite r1.
        simpl.
        auto.
      + apply Align.distinct_seq. {
          apply Align.distinct_seq. {
            intuition.
          }
          apply ULang.distinct_subst.
          auto.
        }
        apply ULang.distinct_subst.
       intuition.
    + apply ULang.distinct_c_seq. {
        apply ULang.distinct_subst.
        intuition.
      }
      apply ULang.distinct_subst.
      auto.
  Qed.

  Lemma split_align_var:
    forall x P ph,
    PhaseSplit.Var x ph ->
    In ph (PhaseSplit.split (Align.align P)) ->
    WLang.WVar x P.
  Proof.
    intros.
    eapply split_var in H0; eauto.
    eapply align_var in H0; eauto.
  Qed.

  Lemma split_align_occurs:
    forall x P ph,
    PhaseSplit.Occurs x ph ->
    In ph (PhaseSplit.split (Align.align P)) ->
    WLang.Occurs x P.
  Proof.
    intros.
    eapply split_occurs in H0; eauto.
    eapply align_occurs in H0; eauto.
  Qed.

  Lemma split_align_distinct:
    forall P,
    WLang.Distinct P ->
    forall ph,
    In ph (PhaseSplit.split (Align.align P)) ->
    PhaseSplit.Distinct ph.
  Proof.
    intros.
    apply align_distinct in H.
    eauto using split_distinct.
  Qed.

  Lemma w_run_to_a_can_run:
    forall P h,
    WLang.Distinct P ->
    WLang.WRun P h ->
    PhaseSplit.CanRun (fst (Align.align P)).
  Proof.
    intros P h Hd H.
    generalize dependent Hd.
    induction H; simpl; intros Hd.
    - constructor.
    - destruct (Align.align i) as (a1, u1) eqn:eq_1.
      destruct (Align.align j) as (a2, u2) eqn:eq_2.
      simpl in *.
      destruct Hd as (Hd1, Hd2).
      constructor; auto.
      rewrite PhaseSplit.can_run_n_seq_iff.
      auto.
    - destruct r as (e1, e2).
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct (Align.align P) as (a1, u1) eqn:eq_1.
      simpl in *.
      destruct r' as (e1', e2').
      rewrite eq_1 in *.
      simpl in *.
      constructor; auto. {
        rewrite PhaseSplit.can_run_n_seq_iff.
        simpl in *.
        erewrite Align.align_to_subst in IHWRun1; eauto using NExp.n_closed_num.
        simpl in *.
        rename_hyp (RExp.RStep _ _ _) as hr.
        inversion_clear hr.
        assert (PhaseSplit.CanRun (ALang.subst x (NExp.NNum n) a1)). {
          apply IHWRun1.
          auto using WLang.distinct_subst.
        }
        eauto using PhaseSplit.can_run_subst, NExp.n_step_num.
      }
      clear IHWRun1.
      intros m hr1.
      repeat rewrite ALang.n_seq_subst.
      repeat rewrite PhaseSplit.can_run_n_seq_iff.
      simpl in *.
      assert (IH: PhaseSplit.CanRun
          (ALang.NFor (ALang.n_seq ULang.Skip (ALang.subst x e1' a1)) x
             (NExp.NBin NExp.NPlus (NExp.NNum 1) e1', e2')
             (ALang.n_seq
                (ULang.i_subst x
                   (NExp.NBin NExp.NMinus (NExp.NVar x) (NExp.NNum 1)) u1)
                (ALang.n_seq
                   (ULang.i_subst x
                      (NExp.NBin NExp.NMinus (NExp.NVar x) (NExp.NNum 1)) c2)
                   a1)))). {
        apply IHWRun2.
        intuition.
      }
      clear IHWRun2.
      inversion_clear IH.
      rewrite PhaseSplit.can_run_n_seq_iff in H5.
      assert (NExp.NStep e1' (S n)). {
        invc H.
        auto.
      }
      assert (e1'_e2': m = S n \/ RExp.RPick (NExp.NBin NExp.NPlus (NExp.NNum 1) e1', e2') m). {
        invc hr1.
        invc H.
        assert (n3 = n2) by eauto using NExp.n_step_fun.
        subst.
        rename_hyp (NExp.NStep (NExp.NBin _ _ _) _) as hn1.
        invc hn1.
        simpl in *.
        assert (n3 = n) by eauto using NExp.n_step_fun.
        subst.
        assert (n0 = 1) by eauto using NExp.n_step_fun, NExp.n_step_num.
        subst.
        assert (m = S n \/ m > S n) by lia.
        intuition.
        right.
        eapply RExp.r_pick_def; eauto.
        eapply NExp.n_step_add_eq; eauto.
      }
      destruct e1'_e2' as [?|e1'_e2']. {
        subst.
        eauto using PhaseSplit.can_run_subst, NExp.n_step_num.
      }
      rename_hyp (PhaseSplit.CanRun _) as rm.
      clear rm.
      rename_hyp (forall n, RExp.RPick _ _ -> _) as IH.
      apply IH in e1'_e2'.
      repeat rewrite ALang.n_seq_subst in e1'_e2'.
      repeat rewrite PhaseSplit.can_run_n_seq_iff in e1'_e2'.
      eauto using PhaseSplit.can_run_subst, NExp.n_step_num.
    - destruct r as (e1, e2).
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct (Align.align P) as (a1, u1) eqn:eq_1.
      simpl in *.
      constructor. {
        rewrite PhaseSplit.can_run_n_seq_iff.
        erewrite Align.align_to_subst in IHWRun; eauto using NExp.n_closed_num.
        simpl in *.
        eapply PhaseSplit.can_run_subst with (e1:=(NExp.NNum n)); eauto using NExp.n_step_num.
        - inversion_clear H; eauto.
        - apply IHWRun.
          auto using WLang.distinct_subst.
      }
      intros o r_o.
      invc r_o.
      assert (o = n). {
        rename_hyp (NExp.NStep (NExp.NBin  _ _ _) _) as s_n1.
        invc s_n1.
        rename_hyp (NExp.NStep (NExp.NNum _) _) as hn.
        inversion_clear hn.
        simpl in *.
        invc H.
        assert (n2 = S n) by eauto using NExp.n_step_fun.
        subst.
        assert (n3 = n) by eauto using NExp.n_step_fun.
        subst.
        lia.
      }
      subst.
      simpl in *.
      repeat rewrite ALang.n_seq_subst.
      repeat rewrite PhaseSplit.can_run_n_seq_iff.
      erewrite Align.align_to_subst in IHWRun; eauto using NExp.n_closed_num.
      simpl in *.
      apply IHWRun.
      auto using WLang.distinct_subst.
  Qed.


  Theorem drf_1:
    forall P h1 h2,
    ~ WLang.WVar TID P ->
    ~ WLang.Occurs T1 P ->
    ~ WLang.Occurs T2 P ->
    WLang.WRun P h1 ->
    SRun (split (Align.align P)) h2 ->
    WLang.Distinct P ->
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
    unfold split in Hi.
    apply in_map_iff in Hi.
    destruct Hi as (ph, (?, Hi)).
    subst.
    apply in_1 in Hp.
    assert (Hp': PhaseSplit.InPhases (x,y) (PhaseSplit.split (Align.align P))). {
      eexists.
      eauto.
    }
    assert (PhaseSplit.CanRun (fst (Align.align P))). {
      eauto using w_run_to_a_can_run.
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
    - intros N.
      rename_hyp (~WLang.WVar TID P) as hv.
      contradict hv.
      eauto using split_align_var.
    - intros N.
      rename_hyp (~ WLang.Occurs T1 P) as ht1.
      contradict ht1.
      eauto using split_align_occurs.
    - intros N.
      rename_hyp (~ WLang.Occurs T2 P) as ht1.
      contradict ht1.
      eauto using split_align_occurs.
    - eauto using split_align_distinct.
  Qed.

  Theorem drf_2:
    forall P h1 h2,
    ~ WLang.WVar TID P ->
    ~ WLang.Occurs T1 P ->
    ~ WLang.Occurs T2 P ->
    WLang.WRun P h1 ->
    SRun (split (Align.align P)) h2 ->
    WLang.Distinct P ->
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
      unfold split in *.
      rename_hyp (SRun _ _) as hs.
      apply s_run_inv with (x:=ph_to_hist ph) in hs; auto. 2: {
        rewrite in_map_iff.
        eauto.
      }
      destruct hs as (h, (Hsr, hi)).
      eapply TLang.run_i_pair_in_to_m_pair_in with (h:=h) in Hp; eauto.
      eauto using PairInUtil.m_pair_in_incl.
    + intros N.
      rename_hyp (~WLang.WVar TID P) as hv.
      contradict hv.
      eauto using split_align_var.
    + intros N.
      rename_hyp (~ WLang.Occurs T1 P) as ht1.
      contradict ht1.
      eauto using split_align_occurs.
    + intros N.
      rename_hyp (~ WLang.Occurs T2 P) as ht1.
      contradict ht1.
      eauto using split_align_occurs.
    + eauto using split_align_distinct.
  Qed.

  (*
  ~~~~~ Theorem 1 and Theorem 3 ~~~~~~~

  Theorem `drf` subsumes the following two theorems that appear in the paper,
  by combining both steps into one theorem.

    Theorem 1: let align(p) = (q, u) and p \in mathcal W.
    If p \downarrow H_1 and q;u \downarrow H_2, then
    safe(H_1) iff safe(H_2).

    Theorem 2: let p \in \mathcal A such that p \downarrow H_1,
    and H_2 = [H | h \in split(p) /\ h \Downarrow H],
    then safe(H_1) iff safe(H_2)

  Understanding the notation below:

  1. `WLang.Run P h1` corresponds to:
    - P \downarrow h1
    - P is a well-formed protocol
  2. `SRun (split (Align.align P)) h2` corresponds to:
     - align(p) = (q, u)
     - q;u \downarrow H_2
     - [H | h \in split(q,u) /\ h \Downarrow H]
  
    Note that in the Coq formalism `split` is extended to take a
    pair (q,u) rather than just a protocol. 
  
  -------------- More definitions -----------------
  - Print Hist.MSafeStrong:

  *)
  Theorem drf:
    forall P h1 h2,
    (* P runs and yields h1: *)
    WLang.WRun P h1 ->                      (* p \in mathcal W and p \downarrow h1 *)
    (* split(align(P)) runs and yields h2: *)
    SRun (split (Align.align P)) h2 ->      (* split(align(p)) \Downarrow h_2 *)
    (* All loop variables in c must be distinct: *)
    WLang.Distinct P ->
    (* TID is not declared in a loop *)
    ~ WLang.WVar TID P ->
    (* T1 (used in sequentialization) cannot appear anywhere in P: *)
    ~ WLang.Occurs T1 P ->
    (* T2 (used in sequentialization) cannot appear anywhere in P: *)
    ~ WLang.Occurs T2 P ->
    (* Main result: *)
    Hist.MSafeStrong h2 <-> Hist.MSafeStrong (VHist.vhist_to_list h1). (* safe(h2) <-> safe(h1) *)
  Proof.
    intros.
    rewrite <- VHist.v_safe_spec.
    split; eauto using drf_1, drf_2.
  Qed.

End Defs.

(*
    ~~~~~ Example ~~~~~~~
*)
Require AccExpImpl.
Require Coq.Strings.String.
Module Example.
  Section Defs.
  Context `{T:Tasks}.
  Import Coq.Strings.String.
  Import AccExpImpl.
  Import NExp.
  Import Var.
  Import WLang.WLangNotations.
  Import ULang.
  Import WLang.
  Local Open Scope string_scope.
  (*
    skip;
    for x in 0..10 {
      wr[x];
      sync;
      wr[x];
    }
    *)
  Definition Prog1 :=
    let x : var := variable "x" in 
    WFor
      Skip
      x
      (NNum 0, NNum 10)
      (WSync (MemAcc (NVar x)))
      (MemAcc (NVar x)).
  Definition AProg1 := Align.align Prog1.
  (*
    ------- phase 0 ----
    skip;
    wr[0];
    sync;
    ------- phase 1 ----
    for x in 1+0..10 {
      skip;
      wr[x - 1];
      wr[x];
      sync
    };
    ------- phase 2 ----
    skip;
    w[10 - 1];
    *)
  Compute AProg1.

  Definition SProg1 := split AProg1.
  Goal SProg1 = [
    (* seq(skip; wr[0]) *)
Sequentialize.sequentialize (Seq Skip (MemAcc (NNum 0)));
    (* var x in 1 + 0..10; seq(skip; wr[x - 1]; wr[x]) *)
TLang.Decl (variable "x") (NBin NPlus (NNum 1) (NNum 0), NNum 10)
  (Sequentialize.sequentialize
     (Seq Skip
        (Seq (MemAcc (NBin NMinus (NVar (variable "x")) (NNum 1)))
           (MemAcc (NVar (variable "x"))))));
    (* seq(skip; wr[10 - 1]) *)
  Sequentialize.sequentialize
   (Seq Skip (MemAcc (NBin NMinus (NNum 10) (NNum 1))))

   ]
           .
  Proof.
    unfold SProg1, AProg1, Prog1, split.
    simpl.
    auto.
  Qed.
End Defs.
End Example.
