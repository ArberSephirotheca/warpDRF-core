Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Tictac.
Require Import Tasks.

Require Pure.NExp.
Require ULang.
Require Align.
Require Sequentialize.
Require PhaseSplit.
Require WLang.
Require Hist.
Require VHist.
Require ALang.
Require Import AVal.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.

  Fixpoint seq (p:PhaseSplit.phase) :=
    match p with
      (* case: u;sync *)
    | PhaseSplit.Phase c => Sequentialize.sequentialize c
      (* case: for^s x in n .. m {q} *)
    | PhaseSplit.Decl x r p => TLang.Decl x r (seq p)
    end.

  Definition seq_l l :=
    List.map seq l.

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
    seq (PhaseSplit.Phase u) = Sequentialize.sequentialize u.
  Proof.
    intros.
    reflexivity.
  Qed.
  Opaque Sequentialize.sequentialize.

  Lemma ph_to_hist_subst:
    forall x v ph,
    x <> T1 ->
    x <> T2 ->
    Pure.NExp.NClosed v ->
    ~ PhaseSplit.Var x ph ->
    TLang.i_subst x v (seq ph) =
    seq (PhaseSplit.ph_subst x v ph). 
  Proof.
    induction ph; intros ht1 ht2 htid hc; simpl.
    - rewrite Sequentialize.sequentialize_subst_rw; auto.
    - rename v0 into y.
      destruct (Var.VAR.eq_dec x y). {
        reflexivity.
      }
      rewrite IHph; auto.
      simpl in *.
      intuition.
  Qed.

  Transparent Sequentialize.sequentialize.

  Lemma in_1:
    forall p ph,
    TLang.IPairIn p (seq ph) ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    PhaseSplit.Distinct ph ->
    PhaseSplit.PPairIn p ph.
  Proof.
    intros p ph hp.
    remember (seq ph) as P.
    generalize dependent ph.
    induction hp; intros ph heq ht1 ht2 hd; destruct ph; invc heq.
    - constructor.
      apply Sequentialize.i_pair_in_1; auto.
      unfold Sequentialize.sequentialize.
      eapply TLang.i_pair_in_decl; eauto.
   - simpl in *.
    rewrite ph_to_hist_subst in hp; auto using Pure.NExp.n_closed_num. 2: { intuition. }
    assert (hq: PhaseSplit.PPairIn p (PhaseSplit.ph_subst v (Pure.NExp.NNum n) ph)). {
      apply IHhp; auto using PhaseSplit.not_var_subst.
      - simpl in *.
        rewrite ph_to_hist_subst; auto using Pure.NExp.n_closed_num.
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
    av_owner x <> av_owner y ->
    ~ PhaseSplit.Occurs T1 ph ->
    ~ PhaseSplit.Occurs T2 ph ->
    PhaseSplit.Distinct ph ->
    TLang.IPairIn (x,y) (seq ph).
  Proof.
    intros x y ph H.
    remember (x, y) as p.
    generalize dependent x.
    generalize dependent y.
    induction H; simpl; intros a1 a2 heq hneq ht1 ht2 hvv.
    - subst.
      auto using Sequentialize.i_pair_in_2.
    - eapply TLang.i_pair_in_decl; eauto.
      rewrite ph_to_hist_subst; auto using Pure.NExp.n_closed_num.
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
          rewrite <- NExp.n_free_from_pure in *.
          intuition.
        }
        apply ULang.occurs_inv_subst in hc.
        simpl in hc.
        rewrite <- NExp.n_free_from_pure in *.
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
        erewrite Align.align_to_subst in IHWRun1; eauto using Pure.NExp.n_closed_num.
        simpl in *.
        rename_hyp (Pure.RExp.RStep _ _ _) as hr.
        assert (PhaseSplit.CanRun (ALang.subst x (Pure.NExp.NNum n) a1)). {
          apply IHWRun1.
          auto using WLang.distinct_subst.
        }
        eapply PhaseSplit.can_run_subst; eauto using Pure.NExp.n_step_num.
        invc hr.
        assumption.
      }
      clear IHWRun1.
      intros m hr1.
      repeat rewrite ALang.n_seq_subst.
      repeat rewrite PhaseSplit.can_run_n_seq_iff.
      simpl in *.
      assert (IH: PhaseSplit.CanRun
          (ALang.NFor (ALang.n_seq ULang.Skip (ALang.subst x e1' a1)) x
             (Pure.NExp.NBin NExp.NPlus (Pure.NExp.NNum 1) e1', e2')
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
      invc IH.
      rename_hyp (PhaseSplit.CanRun (ALang.n_seq _ _)) as hr.
      rewrite PhaseSplit.can_run_n_seq_iff in hr.
      assert (Pure.NExp.NStep e1' (S n)). {
        invc H.
        auto.
      }
      assert (e1'_e2': m = S n \/ Pure.RExp.RPick (Pure.NExp.NBin Pure.NExp.NPlus (Pure.NExp.NNum 1) e1', e2') m). {
        invc hr1.
        invc H.
        assert (n3 = n2) by eauto using Pure.NExp.n_step_fun.
        subst.
        rename_hyp (Pure.NExp.NStep (Pure.NExp.NBin _ _ _) _) as hn1.
        invc hn1.
        simpl in *.
        assert (n3 = n) by eauto using Pure.NExp.n_step_fun.
        subst.
        assert (n0 = 1) by eauto using Pure.NExp.n_step_fun, Pure.NExp.n_step_num.
        subst.
        assert (m = S n \/ m > S n) by lia.
        intuition.
        right.
        eapply Pure.RExp.r_pick_def; eauto.
        eapply Pure.NExp.n_step_add_eq; eauto.
      }
      destruct e1'_e2' as [?|e1'_e2']. {
        subst.
        eauto using PhaseSplit.can_run_subst, Pure.NExp.n_step_num.
      }
      rename_hyp (PhaseSplit.CanRun _) as rm.
      clear rm.
      rename_hyp (forall n, Pure.RExp.RPick _ _ -> _) as IH.
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
        invc H.
        eapply PhaseSplit.can_run_subst with (e1:=(Pure.NExp.NNum n)).
        all: eauto using Pure.NExp.n_step_num, Pure.NExp.n_closed_num.
        apply IHWRun.
        auto using WLang.distinct_subst.
      }
      intros o r_o.
      invc r_o.
      assert (o = n). {
        rename_hyp (Pure.NExp.NStep (Pure.NExp.NBin  _ _ _) _) as s_n1.
        invc s_n1.
        rename_hyp (Pure.NExp.NStep (Pure.NExp.NNum _) _) as hn.
        inversion_clear hn.
        simpl in *.
        invc H.
        assert (n2 = S n) by eauto using Pure.NExp.n_step_fun.
        subst.
        assert (n3 = n) by eauto using Pure.NExp.n_step_fun.
        subst.
        lia.
      }
      subst.
      simpl in *.
      repeat rewrite ALang.n_seq_subst.
      repeat rewrite PhaseSplit.can_run_n_seq_iff.
      erewrite Align.align_to_subst in IHWRun; eauto using Pure.NExp.n_closed_num.
      simpl in *.
      apply IHWRun.
      auto using WLang.distinct_subst.
  Qed.


  Theorem drf_1:
    forall P h1 h2,
    ~ WLang.Occurs T1 P ->
    ~ WLang.Occurs T2 P ->
    WLang.WRun P h1 ->
    SRun (seq_l (PhaseSplit.split (Align.align P))) h2 ->
    WLang.Distinct P ->
    VHist.Safe h1 ->
    Hist.MSafeStrong h2.
  Proof.
    intros.
    (* We first simplify our goal. *)
    unfold Hist.MSafeStrong, VHist.Safe in *.
    intros.
    rename_hyp (forall x y, _) as Hi.
    apply Hi; auto; clear Hi.
    apply WLang.i_pair_in_2 with (i:=P); auto.
    (* We now simplify an assumption. *)
    assert (ALang.PPairIn (x, y) (Align.align P)). {
      assert (Hp':
        PhaseSplit.InPhases (x,y) (PhaseSplit.split (Align.align P)) /\
        ALang.Distinct (fst (Align.align P)) /\
        PhaseSplit.CanRun (fst (Align.align P))
      ). {
        assert (Hphs: exists s,
          In s (PhaseSplit.split (Align.align P)) /\
          ~ PhaseSplit.Occurs T1 s /\
          ~ PhaseSplit.Occurs T2 s /\
          PhaseSplit.Distinct s /\
          TLang.IPairIn (x, y) (seq s)
        ). {
          assert (Hip: exists hs,
            In hs (seq_l (PhaseSplit.split (Align.align P))) /\
            TLang.IPairIn (x, y) hs
          ). {
            rename_hyp (PairInUtil.MPairIn _ _) as Hi.
            eapply s_run_inv_in in Hi; eauto.
            destruct Hi as (hs, (m1, (Hi, (Hr, Hp)))).
            eapply TLang.run_m_pair_in_to_i_pair_in in Hp; eauto.
          }
          destruct Hip as (e, (Hi, Hp)).
          apply in_map_iff in Hi.
          destruct Hi as (ph, (?, Hi)).
          subst.
          exists ph.
          repeat split; auto.
          - intros N.
            rename_hyp (~ WLang.Occurs T1 P) as ht1.
            contradict ht1.
            eauto using split_align_occurs.
          - intros N.
            rename_hyp (~ WLang.Occurs T2 P) as ht1.
            contradict ht1.
            eauto using split_align_occurs.
          - eapply split_align_distinct; eauto.
        }
        destruct Hphs as (s, Hi).
        intuition.
        rename_hyp (TLang.IPairIn _ _) as hi.
        apply in_1 in hi; auto.
        eexists.
        eauto.
        - rename_hyp (WLang.Distinct P) as hd.
          apply Align.distinct_w_to_a in hd.
          destruct (Align.align P).
          simpl in *.
          intuition.
        - eauto using w_run_to_a_can_run.
      }
      intuition.
      apply PhaseSplit.in_2; auto.
    }
    apply Align.in_1; eauto using WLang.run_to_can_run.
  Qed.

  Theorem drf_2:
    forall P h1 h2,
    ~ WLang.Occurs T1 P ->
    ~ WLang.Occurs T2 P ->
    WLang.WRun P h1 ->
    SRun (seq_l (PhaseSplit.split (Align.align P))) h2 ->
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
    - (* symb trace to h2 *)
      unfold split in *.
      rename_hyp (SRun _ _) as hs.
      apply s_run_inv with (x:=seq ph) in hs; auto. 2: {
        unfold seq_l.
        rewrite in_map_iff.
        eauto.
      }
      destruct hs as (h, (Hsr, hi)).
      eapply TLang.run_i_pair_in_to_m_pair_in with (h:=h) in Hp; eauto.
      eauto using PairInUtil.m_pair_in_incl.
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

  (* ~~~~~ Theorem 1 ~~~~~~~ *)
  Theorem drf:
    forall P h1 h2,
    (* P runs and yields h1: *)
    WLang.WRun P h1 -> (* p \in mathcal W and p \downarrow h1 *)
    (* seq(split(align(P))) runs and yields h2: *)
    SRun (seq_l (PhaseSplit.split (Align.align P))) h2 -> (* seq(split(align(p))) \Downarrow h_2 *)
    (* All loop variables in c must be distinct: *)
    WLang.Distinct P ->
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
Require Coq.Strings.String.
Module Example.
  Section Defs.
  Context `{T:Tasks}.
  Import Coq.Strings.String.
  Import Pure.NExp.
  Import Pure.RExp.
  Import SIMT.AExp.
  Import Var.
  Import WLang.WLangNotations.
  Import ULang.CLangNotations.
  Import ULang.
  Import WLang.
  Local Open Scope string_scope.
  Local Open Scope lang_scope.

  (* Example 1: Protocols containing empty loops do not evaluate *)
  Example empty_loop:
    forall x p u1 u2 h,
    ~ WRun (WFor
      u1
      x
      (NNum 0, NNum 0)
      p u2) h.
  Proof.
    intros x p u1 u2 h N.
    assert (he: REmpty (NNum 0, NNum 0)) by auto using r_empty_eq.
    contradict he.
    apply r_has_next_to_empty.
    inversion_clear N. {
      eauto using r_step_to_has_next.
    }
    eauto using r_one_to_has_next.
  Qed.

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
      (WSync (MemAcc (ae_write (SIMT.NExp.NVar x))))
      (MemAcc (ae_write (SIMT.NExp.NVar x))).
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

  Definition SProg1 := seq_l (PhaseSplit.split AProg1).
  Goal SProg1 = [
    (* seq(skip; wr[0]) *)
Sequentialize.sequentialize (Seq Skip (MemAcc (ae_write (SIMT.NExp.NNum 0))));
    (* var x in 1 + 0..10; seq(skip; wr[x - 1]; wr[x]) *)
TLang.Decl (variable "x") (NBin NPlus (NNum 1) (NNum 0), NNum 10)
  (Sequentialize.sequentialize
     (Seq Skip
        (Seq (MemAcc (ae_write (NExp.NBin NMinus (NExp.NVar (variable "x")) (NExp.NNum 1))))
           (MemAcc (ae_write (NExp.NVar (variable "x")))))));
    (* seq(skip; wr[10 - 1]) *)
  Sequentialize.sequentialize
   (Seq Skip (MemAcc (ae_write (NExp.NBin NMinus (NExp.NNum 10) (NExp.NNum 1)))))

   ]
           .
  Proof.
    unfold SProg1, AProg1, Prog1, split.
    simpl.
    auto.
  Qed.
  
End Defs.
End Example.
