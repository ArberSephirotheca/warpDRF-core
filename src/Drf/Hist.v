From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Arith.PeanoNat.

Require Import AVal.
From Faial.Core Require Import InUtil.
From Faial.Core Require Import PairInUtil.
From Faial.Core Require Import Util.

Import ListNotations.

Section Defs.

  Notation history := (list access_val).

  Definition Safe2 (h1 h2:history) := forall x y, List.In x h1 -> List.In y h2 -> AVal.Safe x y.

  Notation access_safe := AVal.Safe.

  Definition Safe (h:history) := forall x y, List.In x h -> List.In y h -> access_safe x y.

  Definition MSafe (m:list history) := forall h1 h2, List.In h1 m -> List.In h2 m -> Safe2 h1 h2.

  (* Strong safety holds when every history is safe independently of the others. *)
  Definition MSafeStrong (m:list history) :=
    forall x y,
    av_owner x <> av_owner y ->
    MPairIn (x,y) m ->
    access_safe x y.

  Definition MSafe2 (m1 m2:list history) := forall h1 h2, List.In h1 m1 -> List.In h2 m2 -> Safe2 h1 h2.

  Definition APairIncl hs hss :=
    forall x y,
    av_owner x <> av_owner y ->
    MIn x hs ->
    MIn y hs ->
    MPairIn (x, y) hss.

  Lemma safe_in:
    forall h,
    Safe h ->
    forall x y,
    List.In x h ->
    List.In y h ->
    access_safe x y.
  Proof.
    auto.
  Qed.

  Lemma safe_nil:
    Safe (@nil access_val).
  Proof.
    unfold Safe.
    intros.
    contradiction.
  Qed.

  Definition Proj tid h1 h2 :=
    (forall a,
      List.In a h1 ->
      av_owner a = tid ->
      List.In a h2) /\ incl h2 h1.

  Definition Proj2 h1 tid1 tid2 h2 :=
    (forall a,
      List.In a h1 ->
      (av_owner a = tid1 \/ av_owner a = tid2) ->
      List.In a h2) /\ incl h2 h1.

  Lemma proj_to_incl:
    forall tid h1 h2,
    Proj tid h1 h2 ->
    incl h2 h1.
  Proof.
    intros.
    destruct H.
    intuition.
  Qed.

  Lemma proj2_to_incl:
    forall h1 tid1 tid2 h2,
    Proj2 h1 tid1 tid2 h2 ->
    incl h2 h1.
  Proof.
    intros.
    destruct H.
    intuition.
  Qed.

  Lemma proj_in:
    forall tid h1 h2,
    Proj tid h1 h2 ->
    forall a,
    List.In a h1 ->
    av_owner a = tid ->
    List.In a h2.
  Proof.
    intros.
    destruct H as (H,_).
    auto.
  Qed.

  Lemma proj2_in_l:
    forall h1 tid1 tid2 h2,
    Proj2 h1 tid1 tid2 h2 ->
    forall a,
    List.In a h1 ->
    av_owner a = tid1 ->
    List.In a h2.
  Proof.
    intros.
    destruct H as (H,_).
    apply H; intuition.
  Qed.

  Lemma proj2_in_r:
    forall h1 tid1 tid2 h2,
    Proj2 h1 tid1 tid2 h2 ->
    forall a,
    List.In a h1 ->
    av_owner a = tid2 ->
    List.In a h2.
  Proof.
    intros.
    destruct H as (H,_).
    apply H; intuition.
  Qed.

  Lemma proj2_to_safe:
    forall f h,
    (forall tid1 tid2, Proj2 h tid1 tid2 (f tid1 tid2 h) /\
    Safe (f tid1 tid2 h)) ->
    Safe h.
  Proof.
    intros.
    unfold Safe.
    intros.
    assert (H := H (av_owner x) (av_owner y)).
    destruct H as (Hp, Hs).
    assert (List.In x (f (av_owner x) (av_owner y) h)) by eauto using proj2_in_l.
    assert (List.In y (f (av_owner x) (av_owner y) h)) by eauto using proj2_in_r.
    eauto using safe_in.
  Qed.

  Lemma proj_to_safe:
    forall f h,
    (forall tid1 tid2,
      Proj tid1 h (f tid1 h) /\
      Proj tid2 h (f tid2 h) /\
    Safe (f tid1 h ++ f tid2 h)) ->
    Safe h.
  Proof.
    intros.
    unfold Safe.
    intros.
    assert (H := H (av_owner x) (av_owner y)).
    destruct H as (Hp1, (Hp2, Hs)).
    assert (List.In x (f (av_owner x) h)) by eauto using proj_in.
    assert (List.In y (f (av_owner y) h)) by eauto using proj_in.
    apply safe_in with (h:=f (av_owner x) h ++ f (av_owner y) h); auto;
      apply in_or_app; auto.
  Qed.

  Definition proj task : history -> history :=
    List.filter (fun a => (Nat.eqb (av_owner a) task)).

  Definition m_proj task : list history -> list history :=
    List.map (proj task).

  Definition proj2 t1 t2 := List.filter
    (fun a => orb
      (Nat.eqb (av_owner a) t1)
      (Nat.eqb (av_owner a) t2)).

  Definition proj2_seq t1 t2 h := proj t1 h ++ proj t2 h.

  Lemma or_to_orb:
    forall a b,
    a = true \/ b = true ->
    (a || b)%bool = true.
  Proof.
    intros.
    destruct H as [H|H]; rewrite H.
    - reflexivity.
    - apply Bool.orb_true_r.
  Qed.

  Lemma in_proj:
    forall a h tid,
    List.In a h ->
    av_owner a = tid ->
    List.In a (proj tid h).
  Proof.
    intros.
    unfold proj.
    apply List.filter_true_to_in; auto.
    apply PeanoNat.Nat.eqb_eq; auto.
  Qed.

  Lemma in_proj2_seq_or:
    forall tid1 tid2 h a,
    List.In a h ->
    (av_owner a = tid1 \/ av_owner a = tid2) ->
    List.In a (proj2_seq tid1 tid2 h).
  Proof.
    intros.
    unfold proj2_seq.
    apply in_or_app.
    destruct H0. {
      left.
      auto using in_proj.
    }
    right; auto using in_proj.
  Qed.

  Lemma in_proj2_seq_inv:
    forall a tid1 tid2 h,
    List.In a (proj2_seq tid1 tid2 h) ->
    List.In a (proj tid1 h) \/ List.In a (proj tid2 h).
  Proof.
    unfold proj2.
    intros.
    apply in_app_or in H.
    assumption.
  Qed.

  Lemma in_proj_inv:
    forall a tid h,
    List.In a (proj tid h) ->
    List.In a h /\ av_owner a = tid.
  Proof.
    unfold proj. intros.
    apply filter_In in H.
    destruct H as (Hl, Hr).
    apply Nat.eqb_eq in Hr.
    split; auto.
  Qed.

  Lemma in_proj_inv_in:
    forall a tid h,
    List.In a (proj tid h) ->
    List.In a h.
  Proof.
    intros.
    apply in_proj_inv in H; auto.
    destruct H; auto.
  Qed.

  Lemma in_proj_inv_tid:
    forall a tid h,
    List.In a (proj tid h) ->
    av_owner a = tid.
  Proof.
    intros.
    apply in_proj_inv in H; auto.
    destruct H; auto.
  Qed.

  Lemma in_proj2_seq_inv_in:
    forall a tid1 tid2 h,
    List.In a (proj2_seq tid1 tid2 h) ->
    List.In a h.
  Proof.
    intros.
    apply in_proj2_seq_inv in H.
    destruct H; eauto using in_proj_inv_in.
  Qed.

  Lemma in_proj2_seq_inv_tid:
    forall a tid1 tid2 h,
    List.In a (proj2_seq tid1 tid2 h) ->
    av_owner a = tid1 \/ av_owner a = tid2.
  Proof.
    intros.
    apply in_proj2_seq_inv in H.
    destruct H as [H|H];
      apply in_proj_inv_tid in H;
      intuition.
  Qed.

  Lemma proj2_proj2:
    forall h tid1 tid2,
    Proj2 h tid1 tid2 (proj2 tid1 tid2 h).
  Proof.
    unfold Proj2, proj2; intros.
    split.
    - intros.
      apply filter_In.
      split; auto.
      apply or_to_orb; destruct H0 as [H0|H0];
        apply PeanoNat.Nat.eqb_eq in H0; intuition.
    - auto using List.filter_incl.
  Qed.

  Lemma proj_spec:
    forall h tid,
    Proj tid h (proj tid h).
  Proof.
    unfold Proj, proj; intros.
    split.
    - intros.
      apply filter_In.
      split; auto.
      apply PeanoNat.Nat.eqb_eq in H0; intuition.
    - auto using List.filter_incl.
  Qed.

  Lemma safe_proj2_to_safe:
    forall h,
    (forall tid1 tid2, Safe (proj2 tid1 tid2 h)) ->
    Safe h.
  Proof.
    intros.
    apply proj2_to_safe with (f:=proj2); intros.
    split; auto using proj2_proj2.
  Qed.

  Lemma in_proj2_inv_tid:
    forall x y a h,
    List.In a (proj2 x y h) ->
    av_owner a = x \/ av_owner a = y.
  Proof.
    intros.
    unfold proj2 in *.
    apply filter_In in H; auto.
    destruct H as (_, Hx).
    apply Bool.orb_prop in Hx.
    destruct Hx as [Hx|Hx]; apply Nat.eqb_eq in Hx; intuition.
  Qed.

  Lemma in_proj2_inv_tid_eq:
    forall x a h,
    List.In a (proj2 x x h) ->
    av_owner a = x.
  Proof.
    intros.
    apply in_proj2_inv_tid in H.
    intuition.
  Qed.

  Lemma safe_proj2_eq:
    forall x h,
    Safe (proj2 x x h).
  Proof.
    intros.
    unfold Safe.
    intros a b Hi Hj.
    apply safe_owner.
    apply in_proj2_inv_tid in Hi.
    apply in_proj2_inv_tid in Hj.
    destruct Hi as [Hi|Hi]; destruct Hj as [Hj|Hj]; subst; rewrite Hj; reflexivity.
  Qed.

  Lemma proj2_symm:
    forall t1 t2 l,
    proj2 t1 t2 l = proj2 t2 t1 l.
  Proof.
    unfold proj2; induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    destruct (Nat.eqb _ t1). {
      simpl.
      rewrite Bool.orb_true_r.
      reflexivity.
    }
    simpl.
    destruct (Nat.eqb _ t2); reflexivity.
  Qed.

  Lemma proj2_in:
    forall a tid1 tid2 h,
    List.In a (proj2 tid1 tid2 h) ->
    List.In a h.
  Proof.
    unfold proj2; intros.
    eauto using List.filter_in.
  Qed.

  Lemma proj2_incl:
    forall tid1 tid2 h,
    incl (proj2 tid1 tid2 h) h.
  Proof.
    unfold proj2; auto using List.filter_incl.
  Qed.

  Lemma safe_to_safe_proj2:
    forall h tid1 tid2,
    Safe h ->
    Safe (proj2 tid1 tid2 h).
  Proof.
    unfold Safe; intros.
    apply proj2_in in H0.
    apply proj2_in in H1.
    auto.
  Qed.

  Corollary proj2_iff_safe:
    forall h,
    (forall tid1 tid2, tid1 < tid2 -> Safe (proj2 tid1 tid2 h)) <-> Safe h.
  Proof.
    split; intros. {
      assert (forall tid1 tid2, Safe (proj2 tid1 tid2 h)). {
        intros.
        assert (Hx: tid1 = tid2 \/ tid1 < tid2 \/ tid1 > tid2) by lia.
        destruct Hx as [Hx|[Hx|Hx]].
        - subst.
          apply safe_proj2_eq.
        - auto.
        - rewrite proj2_symm.
          auto.
      }
      apply safe_proj2_to_safe; auto.
    }
    auto using safe_to_safe_proj2.
  Qed.

  Lemma proj2_app:
    forall tid1 tid2 h1 h2,
    proj2 tid1 tid2 (h1 ++ h2) = proj2 tid1 tid2 h1 ++ proj2 tid1 tid2 h2.
  Proof.
    intros.
    unfold proj2.
    rewrite filter_app.
    reflexivity.
  Qed.

  Lemma proj_app:
    forall t h1 h2,
    proj t (h1 ++ h2) = proj t h1 ++ proj t h2.
  Proof.
    intros.
    unfold proj.
    rewrite filter_app.
    reflexivity.
  Qed.

  Lemma m_proj_app:
    forall t h1 h2,
    m_proj t (h1 ++ h2) = m_proj t h1 ++ m_proj t h2.
  Proof.
    unfold m_proj.
    intros.
    rewrite map_app.
    reflexivity.
  Qed.

  Lemma in_m_proj:
    forall x t hs,
    MIn x hs ->
    av_owner x = t ->
    MIn x (m_proj t hs).
  Proof.
    induction hs; intros. {
      apply m_in_nil in H.
      contradiction.
    }
    apply m_in_inv in H.
    destruct H. {
      simpl.
      apply m_in_eq.
      auto using in_proj.
    }
    simpl.
    apply m_in_cons.
    auto.
  Qed.

  Lemma forall_tid_proj_id:
    forall n l,
    Forall (fun a => av_owner a = n) l ->
    proj n l = l.
  Proof.
    intros.
    rewrite Forall_forall in H.
    unfold proj.
    apply List.filter_forallb.
    apply forallb_forall.
    intros.
    apply H in H0.
    apply PeanoNat.Nat.eqb_eq.
    assumption.
  Qed.

  Lemma safe_to_safe2:
    forall h,
    Safe h ->
    forall t1 t2,
    Safe2 (proj t1 h) (proj t2 h).
  Proof.
    unfold Safe, Safe2; intros.
    apply in_proj_inv in H0.
    apply in_proj_inv in H1.
    destruct H0, H1.
    auto.
  Qed.

  Lemma safe2_to_safe:
    forall h,
    (forall t1 t2,
    Safe2 (proj t1 h) (proj t2 h)) ->
    Safe h.
  Proof.
    unfold Safe, Safe2; intros.
    assert (Hx := H (av_owner x) (av_owner y) x y).
    apply Hx; apply in_proj; auto.
  Qed.

  Lemma safe2_sym:
    forall h1 h2,
    Safe2 h1 h2 <-> Safe2 h2 h1.
  Proof.
    unfold Safe2; split; intros.
    - auto using a_safe_sym.
    - auto using a_safe_sym.
  Qed.

  Lemma safe2_app:
    forall h1 h2,
    Safe h1 /\ Safe h2 /\ Safe2 h1 h2 <-> Safe (h1 ++ h2).
  Proof.
    unfold Safe, Safe2; split; intros.
    - destruct H as (Ha, (Hb, Hc)).
      apply in_app_or in H0.
      apply in_app_or in H1.
      destruct H0, H1; auto using a_safe_sym.
    - repeat split; intros; apply H; apply in_app_iff; auto.
  Qed.

  Lemma safe_app_to_safe2:
    forall h1 h2,
    Safe (h1 ++ h2) ->
    Safe2 h1 h2.
  Proof.
    intros.
    apply safe2_app in H.
    destruct H as (_, (_, ?)).
    assumption.
  Qed.

  Lemma safe_inv_app:
    forall h1 h2,
    Safe (h1 ++ h2) ->
    Safe h1 /\ Safe h2.
  Proof.
    intros.
    apply safe2_app in H.
    destruct H as [H1 [H2 H3]].
    intuition.
  Qed.

  Lemma safe_inv_app_l:
    forall h1 h2,
    Safe (h1 ++ h2) ->
    Safe h1.
  Proof.
    intros.
    apply safe_inv_app in H.
    destruct H; assumption.
  Qed.

  Lemma safe_inv_app_r:
    forall h1 h2,
    Safe (h1 ++ h2) ->
    Safe h2.
  Proof.
    intros.
    apply safe_inv_app in H.
    destruct H; assumption.
  Qed.

  Lemma msafe_prepend:
    forall h1 h2 hs,
    AllIncl (prepend h1 hs) (h1 ++ h2) ->
    Safe (h1 ++ h2) ->
    MSafe (prepend h1 hs).
  Proof.
    intros ? ? ?.
    intros Hp.
    intros Hs.
    apply safe2_app in Hs.
    destruct Hs as [Sh1 [Sh2 Sh1h2]].
    unfold MSafe.
    intros l1 l2 Hl1 Hl2.
    destruct (in_prepend_inv _ _ _ _ Hl1) as (la, ?); subst.
    destruct (in_prepend_inv _ _ _ _ Hl2) as (lb, ?); subst.
    eapply all_incl_to_incl in Hl1; eauto.
    eapply all_incl_to_incl in Hl2; eauto.
    unfold Safe2 in *.
    intros.
    assert (Hi: List.In x (h1 ++ h2)). {
      eauto using List.in_incl.
    }
    assert (Hj: List.In y (h1 ++ h2)). {
      eauto using List.in_incl.
    }
    apply in_app_iff in Hi.
    apply in_app_iff in Hj.
    destruct Hi, Hj; auto using a_safe_sym.
  Qed.

  Lemma safe_to_msafe:
    forall h hs,
    Safe h ->
    AllIncl hs h ->
    MSafe hs.
  Proof.
    unfold Safe, AllIncl, MSafe, Safe2.
    intros.
    rewrite Forall_forall in *.
    apply H0 in H1.
    apply H0 in H2.
    auto.
  Qed.

  Lemma pair_in_safe2:
    forall x y h,
    PairIn (x, y) h ->
    Safe2 h h ->
    access_safe x y.
  Proof.
    unfold Safe2; intros.
    inversion H; subst; clear H.
    auto.
  Qed.

  Lemma msafe_pair_in_to_safe:
    forall h hs x y,
    MSafe hs ->
    List.In h hs ->
    PairIn (x, y) h ->
    access_safe x y.
  Proof.
    intros.
    unfold MSafe in *.
    assert (Safe2 h h) by auto.
    eauto using pair_in_safe2.
  Qed.

  Lemma msafe_mpair_in_to_safe:
    forall hs x y,
    MSafe hs ->
    MPairIn (x, y) hs ->
    access_safe x y.
  Proof.
    unfold MPairIn.
    intros.
    rewrite Exists_exists in *.
    destruct H0 as (h, (Hi, Hp)).
    eauto using msafe_pair_in_to_safe.
  Qed.

  Lemma map_proj_prepend:
    forall hs vs n v,
    proj n (List.concat vs) = v ->
    map (proj n) (prepend (List.concat vs) hs) = prepend v (map (proj n) hs).
  Proof.
    induction hs; simpl; intros. {
      reflexivity.
    }
    rewrite proj_app in *.
    rewrite H.
    apply IHhs in H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma m_safe_to_safe:
    forall h hs,
    MSafe hs ->
    InclAll h hs ->
    Safe h.
  Proof.
    unfold Safe, Safe2.
    intros.
    unfold MSafe,Safe2 in *.
    apply H0 in H1.
    apply H0 in H2.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    eauto.
  Qed.

  Lemma m_safe_eq:
    forall hs x y,
    MSafe hs ->
    MIn x hs ->
    MIn y hs ->
    access_safe x y.
  Proof.
    unfold MSafe, Safe2; intros.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    eauto.
  Qed.

  Lemma m_safe_to_m_safe_strong:
    forall hs1 hs2,
    MSafe hs1 ->
    AllInclAll hs2 hs1 ->
    MSafeStrong hs2.
  Proof.
    unfold MSafeStrong, Safe2.
    intros.
    apply m_pair_in_to_in in H2.
    destruct H2 as (Ha, Hb).
    apply H0 in Ha.
    apply H0 in Hb.
    unfold Ensembles.In in *.
    clear H0.
    eauto using m_safe_eq.
  Qed.

  Lemma m_safe_strong_to_m_safe:
    forall m_l m_h,
    MSafeStrong m_l ->
    APairIncl m_h m_l ->
    MSafe m_h.
  Proof.
    intros.
    unfold MSafeStrong, AllInclAll,Ensembles.Included,Ensembles.In, MPairIncl, MSafe, Safe2; intros.
    destruct (PeanoNat.Nat.eq_dec (av_owner x) (av_owner y)). {
      auto using safe_owner.
    }
    eauto using m_in_def.
  Qed.

  Definition PairInclMPair (h:list access_val) m :=
    forall x y,
    In x h ->
    In y h ->
    MPairIn (x, y) m.

  Lemma m_safe_strong_to_safe:
    forall m h,
    PairInclMPair h m ->
    MSafeStrong m ->
    Safe h.
  Proof.
    unfold MSafeStrong, Safe; intros.
    assert (X: av_owner x = av_owner y \/ av_owner x <> av_owner y) by lia.
    destruct X. {
      auto using safe_owner.
    }
    unfold PairInclMPair in *; auto.
  Qed.

End Defs.
