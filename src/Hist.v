Require Import Coq.Lists.List.

Require Import AccExp.
Require Import NExp.
Require Import BExp.
Require Import InUtil.
Require Import PairInUtil.
Require Import Util.

Import ListNotations.

Section Defs.
  Context {A:Access}.

  Notation history := (list access_val).
  (*Global Transparent history.*)
  Definition Safe2 (h1 h2:history) := forall x y, List.In x h1 -> List.In y h2 -> access_safe x y.

  Definition Safe (h:history) := forall x y, List.In x h -> List.In y h -> access_safe x y.

  Definition MSafe (m:list history) := forall h1 h2, List.In h1 m -> List.In h2 m -> Safe2 h1 h2.

  (* Strong safety holds when every history is safe independently of the others. *)
  Definition MSafeStrong (m:list history) :=
    forall x y,
    access_tid x <> access_tid y ->
    MPairIn (x,y) m ->
    access_safe x y.

  Definition MSafe2 (m1 m2:list history) := forall h1 h2, List.In h1 m1 -> List.In h2 m2 -> Safe2 h1 h2.

  Definition APairIncl hs hss :=
    forall x y,
    access_tid x <> access_tid y ->
    MIn x hs ->
    MIn y hs ->
    MPairIn (x, y) hss.

  Inductive GenAccess x a: nat -> list (list access_val) -> Prop :=
  | gen_access_nil:
    GenAccess x a 0 []
  | gen_access_cons:
    forall n v l,
    GenAccess x a n l ->
    CStep (cond_access_subst x (NNum n) a, NNum  n) v ->
    GenAccess x a (S n) (v::l).

  Import Omega.

  Lemma gen_access_lt:
    forall x e n v,
    GenAccess x e n v ->
    forall m,
    m < n ->
    exists l, CStep (cond_access_subst x (NNum m) e, NNum m) l /\ List.In l v.
  Proof.
    intros x e n v Hg.
    induction Hg; intros. {
      inversion H; subst.
    }
    inversion H0; subst; clear H0. {
      eauto using List.in_eq.
    }
    assert (Hx: m < n) by auto with *.
    apply IHHg in Hx.
    destruct Hx as (l', (Hs, Hi)).
    eauto using List.in_cons.
  Qed.

  Lemma gen_access_in:
    forall x e n v,
    GenAccess x e n v ->
    forall l,
    List.In l v ->
    exists m, CStep (cond_access_subst x (NNum m) e, NNum m) l /\ m < n.
  Proof.
    intros x e n v Hg.
    induction Hg; intros. {
      contradiction.
    }
    destruct H0; subst. {
      eauto.
    }
    apply IHHg in H0.
    destruct H0 as (m, (Hs, Hlt)).
    eauto.
  Qed.

  Lemma gen_access_to_access_step_lt:
    forall x e n v,
    GenAccess x e n v ->
    forall m,
    m < n ->
    exists l, CStep (cond_access_subst x (NNum m) e, NNum m) l.
  Proof.
    induction n; intros. {
      omega.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0; eauto.
  Qed.

  Lemma gen_access_to_in:
    forall x e vs n2,
    GenAccess x e n2 vs ->
    forall n1 v,
    n1 < n2 ->
    CStep (cond_access_subst x (NNum n1) e, NNum n1) v ->
    List.In v vs.
  Proof.
    induction vs; intros. {
      inversion H; subst.
      inversion H0.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      assert (a = v) by eauto using c_step_fun.
      subst.
      auto using in_eq.
    }
    eauto using in_cons.
  Qed.

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
      access_tid a = tid ->
      List.In a h2) /\ incl h2 h1.

  Definition Proj2 h1 tid1 tid2 h2 :=
    (forall a,
      List.In a h1 ->
      (access_tid a = tid1 \/ access_tid a = tid2) ->
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
    access_tid a = tid ->
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
    access_tid a = tid1 ->
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
    access_tid a = tid2 ->
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
    assert (H := H (access_tid x) (access_tid y)).
    destruct H as (Hp, Hs).
    assert (List.In x (f (access_tid x) (access_tid y) h)) by eauto using proj2_in_l.
    assert (List.In y (f (access_tid x) (access_tid y) h)) by eauto using proj2_in_r.
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
    assert (H := H (access_tid x) (access_tid y)).
    destruct H as (Hp1, (Hp2, Hs)).
    assert (List.In x (f (access_tid x) h)) by eauto using proj_in.
    assert (List.In y (f (access_tid y) h)) by eauto using proj_in.
    apply safe_in with (h:=f (access_tid x) h ++ f (access_tid y) h); auto;
      apply in_or_app; auto.
  Qed.

  Definition proj task : history -> history :=
    List.filter (fun a => (Nat.eqb (access_tid a) task)).

  Definition m_proj task : list history -> list history :=
    List.map (proj task).

  Definition proj2 t1 t2 := List.filter
    (fun a => orb
      (Nat.eqb (access_tid a) t1)
      (Nat.eqb (access_tid a) t2)).

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
    access_tid a = tid ->
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
    (access_tid a = tid1 \/ access_tid a = tid2) ->
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
    List.In a h /\ access_tid a = tid.
  Proof.
    unfold proj. intros.
    apply filter_In in H.
    destruct H as (Hl, Hr).
    apply beq_nat_true in Hr.
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
    access_tid a = tid.
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
    access_tid a = tid1 \/ access_tid a = tid2.
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
    access_tid a = x \/ access_tid a = y.
  Proof.
    intros.
    unfold proj2 in *.
    apply filter_In in H; auto.
    destruct H as (_, Hx).
    apply Bool.orb_prop in Hx.
    destruct Hx as [Hx|Hx]; apply beq_nat_true in Hx; intuition.
  Qed.

  Lemma in_proj2_inv_tid_eq:
    forall x a h,
    List.In a (proj2 x x h) ->
    access_tid a = x.
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
    apply access_safe_eq_tid.
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
        assert (Hx: tid1 = tid2 \/ tid1 < tid2 \/ tid1 > tid2) by omega.
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
    access_tid x = t ->
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
    Forall (fun a => access_tid a = n) l ->
    proj n l = l.
  Proof.
    intros.
    rewrite Forall_forall in H.
    unfold proj.
    apply List.filter_forallb.
    apply forallb_forall.
    intros.
    apply H in H0.
    apply Nat.eqb_eq.
    assumption.
  Qed.

  Lemma proj_id:
    forall a n l,
    CStep (a, NNum n) l ->
    proj n l = l.
  Proof.
    intros.
    apply cond_access_step_inv_tid with (n0:=n) in H; auto using n_step_num.
    apply forall_tid_proj_id.
    assumption.
  Qed.

  Lemma proj2_id_l:
    forall x n m a l,
    CStep (cond_access_subst x (NNum n) a, NNum n) l ->
    proj2 n m l = l.
  Proof.
    unfold proj2.
    intros.
    rewrite List.filter_forallb.
    rewrite forallb_forall.
    intros v; intros.
    apply cond_access_step_inv_tid with (n0:=n) in H; auto using n_step_num.
    rewrite Forall_forall in H.
    apply H in H0.
    rewrite H0.
    rewrite PeanoNat.Nat.eqb_refl.
    auto.
  Qed.

  Lemma proj2_id_r:
    forall x n m a l,
    CStep (cond_access_subst x (NNum m) a, NNum m) l ->
    proj2 n m l = l.
  Proof.
    unfold proj2.
    intros.
    rewrite List.filter_forallb.
    rewrite forallb_forall.
    intros v; intros.
    apply cond_access_step_inv_tid with (n0:=m) in H; auto using n_step_num.
    rewrite Forall_forall in H.
    apply H in H0.
    rewrite H0.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite Bool.orb_true_r.
    reflexivity.
  Qed.

  Lemma proj2_neq:
    forall x n m p a l,
    CStep (cond_access_subst x (NNum p) a, NNum p) l ->
    p <> n ->
    p <> m ->
    proj2 n m l = [].
  Proof.
    intros.
    unfold proj2.
    rewrite List.filter_forallb_false.
    rewrite forallb_forall.
    intros v Hi.
    rewrite Bool.negb_orb.
    assert (R: access_tid v = p). {
      apply cond_access_step_inv_tid with (n0 := p) in H; auto using n_step_num.
      rewrite Forall_forall in *.
      apply H in Hi.
      assumption.
    }
    rewrite R.
    apply PeanoNat.Nat.eqb_neq in H0.
    apply PeanoNat.Nat.eqb_neq in H1.
    rewrite H0.
    rewrite H1.
    reflexivity.
  Qed.

  Fixpoint gen_access x a n :=
    let a_step n := cond_access_eval1 (cond_access_subst x (NNum n) a, NNum n) in 
    match n with
    | 0 => Some []
    | S n =>
      match a_step n, gen_access x a n with
      | Some v, Some l => Some (v :: l)
      | _, _ => None
      end
    end.


  Lemma gen_access_inv_succ:
    forall x a n l,
    gen_access x a (S n) = Some l ->
    exists v l',
    l = v :: l' /\
    cond_access_eval1 (cond_access_subst x (NNum n) a, NNum n) = Some v
    /\
    gen_access x a n = Some l'.
  Proof.
    intros.
    simpl in *.
    destruct (cond_access_eval1 _) as [v'|] eqn:Hc; try (inversion H; fail).
    destruct (gen_access _ _ _) as [l'|] eqn:Hg; inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma gen_access_succ:
    forall x a n v l,
    gen_access x a n = Some l ->
    cond_access_eval1 (cond_access_subst x (NNum n) a, NNum n) = Some v ->
    gen_access x a (S n) = Some (v :: l).
  Proof.
    intros.
    simpl.
    rewrite H0.
    rewrite H.
    reflexivity.
  Qed.

  Lemma gen_access_to_prop:
    forall x a n l,
    gen_access x a n = Some l ->
    GenAccess x a n l.
  Proof.
    induction n; intros. {
      simpl.
      inversion H; subst; clear H.
      apply gen_access_nil.
    }
    apply gen_access_inv_succ in H.
    destruct H as (v, (l', (?, (Ha, Hg)))).
    subst.
    eauto using gen_access_cons, cond_access_eval1_to_step.
  Qed.

  Lemma prop_to_gen_access:
    forall x a n l,
    GenAccess x a n l ->
    gen_access x a n = Some l.
  Proof.
    induction n; intros; inversion H; subst; clear H. {
      reflexivity.
    }
    eauto using gen_access_succ, cond_access_step_to_eval1.
  Qed.

  Definition gen_access_item x a n :=
    match cond_access_eval1 (cond_access_subst x (NNum n) a, NNum n) with
    | Some v => v
    | None => []
    end.

  Definition gen_access_iter x a n := List.flat_map (gen_access_item x a) (count n).

  Lemma gen_access_iter_rw:
    forall x a n l,
    GenAccess x a n l ->
    gen_access_iter x a n = List.concat l.
  Proof.
    intros x a n l Hg.
    unfold gen_access_iter, gen_access_item; induction Hg. {
      reflexivity.
    }
    apply cond_access_step_to_eval1 in H.
    simpl.
    rewrite IHHg.
    rewrite H.
    reflexivity.
  Qed.

  Lemma step_proj_neq:
    forall n p a l,
    CStep (a, NNum p) l ->
    p <> n ->
    proj n l = [].
  Proof.
    intros.
    unfold proj.
    apply List.filter_forallb_false.
    apply forallb_forall.
    intros v Hi.
    assert (R: access_tid v = p). {
      apply cond_access_step_inv_tid with (n0 := p) in H; auto using n_step_num.
      rewrite Forall_forall in *.
      apply H in Hi.
      assumption.
    }
    rewrite R.
    apply PeanoNat.Nat.eqb_neq in H0.
    rewrite H0.
    reflexivity.
  Qed.

  Lemma gen_access_proj_ge:
    forall x n a v t1,
    GenAccess x a n v ->
    t1 >= n ->
    proj t1 (List.concat v) = [].
  Proof.
    induction n; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite proj_app.
    assert (R: proj t1 v0 = []). {
      eapply step_proj_neq; eauto with *.
    }
    rewrite R; clear R.
    simpl.
    eapply IHn; eauto with *.
  Qed.

  Lemma gen_access_proj_lt:
    forall x n a v,
    GenAccess x a n v ->
    forall t1,
    t1 < n ->
    proj t1 (List.concat v) = gen_access_item x a t1.
  Proof.
    induction n; intros. {
      omega.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite proj_app.
    inversion H0; subst; clear H0. {
      clear IHn.
      erewrite gen_access_proj_ge; eauto.
      unfold gen_access_item.
      assert (Hx := H3).
      apply cond_access_step_to_eval1 in Hx.
      rewrite Hx.
      apply proj_id in H3.
      unfold id.
      rewrite H3.
      apply app_nil_r.
    }
    assert (R: proj t1 v0 = []). {
      eapply step_proj_neq; eauto with *.
    }
    rewrite R.
    simpl.
    eauto.
  Qed.

  Lemma gen_access_proj_rw:
    forall x n a v l t1,
    GenAccess x a n v ->
    t1 < n ->
    CStep (cond_access_subst x (NNum t1) a, NNum t1) l ->
    proj t1 (List.concat v) = l.
  Proof.
    intros.
    erewrite gen_access_proj_lt; eauto.
    unfold gen_access_item.
    apply cond_access_step_to_eval1 in H1.
    rewrite H1.
    reflexivity.
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
    assert (Hx := H (access_tid x) (access_tid y) x y).
    apply Hx; apply in_proj; auto.
  Qed.

  Lemma gen_access_proj2_1:
    forall x n a v n1 n2,
    GenAccess x a n v ->
    n1 >= n ->
    n2 >= n ->
    proj2 n1 n2 (List.concat v) = [].
  Proof.
    induction n; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite proj2_app.
    assert (R: proj2 n1 n2 v0 = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R; clear R.
    simpl.
    eapply IHn; eauto with *.
  Qed.

  Lemma gen_access_proj2_2:
    forall x n a v,
    GenAccess x a n v ->
    forall t1 t2,
    t1 < n ->
    t2 >= n ->
    proj2 t1 t2 (List.concat v) = gen_access_item x a t1.
  Proof.
    induction n; intros. {
      omega.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite proj2_app.
    inversion H0; subst; clear H0. {
      (* t1 = 0 /\ n = 1 *)
      erewrite proj2_id_l; eauto.
      assert (R: proj2 n t2 (List.concat l) = []). {
        erewrite gen_access_proj2_1; eauto.
        omega.
      }
      rewrite R.
      unfold gen_access_item.
      apply cond_access_step_to_eval1 in H4.
      rewrite H4.
      rewrite app_nil_r.
      reflexivity.
    }
    apply IHn with (t1:=t1) (t2:= t2) in H3; auto with *.
    rewrite H3.
    assert (R: proj2 t1 t2 v0 = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R.
    auto.
  Qed.

  Lemma gen_access_proj_3:
    forall x n a v,
    GenAccess x a n v ->
    forall t1 t2,
    t1 < n ->
    t2 < n ->
    t1 < t2 ->
    proj2 t1 t2 (List.concat v) = gen_access_item x a t2 ++ gen_access_item x a t1.
  Proof.
    induction n; intros; inversion H; subst; clear H. {
      inversion H0.
    }
    simpl.
    rewrite proj2_app.
    inversion H0; subst; clear H0. {
      (* t1 = n *)
      inversion H1; subst; clear H1. {
        (* t2 = n *)
        omega.
      }
      (* t2 < n *)
      omega.
    }
    assert (t1 < n) by auto.
    inversion H1; subst; clear H1. {
      (* t2 = n *)
      assert (R: proj2 t1 n (List.concat l) = gen_access_item x a t1). {
        eapply gen_access_proj2_2; eauto.
      }
      rewrite R; clear R.
      erewrite proj2_id_r; eauto.
      assert (R: gen_access_item x a n = v0). { 
        unfold gen_access_item.
        apply cond_access_step_to_eval1 in H5.
        rewrite H5.
        reflexivity.
      }
      rewrite R.
      reflexivity.
    }
    assert (R: proj2 t1 t2 v0 = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R.
    simpl.
    eauto.
  Qed.

  Lemma gen_access_proj2:
    forall x n a v,
    GenAccess x a n v ->
    forall t1 t2,
    t1 < n ->
    t2 < n ->
    t1 <> t2 ->
    (t1 < t2 /\ proj2 t1 t2 (List.concat v) = gen_access_item x a t2 ++ gen_access_item x a t1)
    \/
    (t2 < t1 /\ proj2 t1 t2 (List.concat v) = gen_access_item x a t1 ++ gen_access_item x a t2)
    .
  Proof.
    intros.
    apply nat_total_order in H2.
    destruct H2. {
      left; intuition.
      eauto using gen_access_proj_3.
    }
    right; intuition.
    rewrite proj2_symm.
    eapply gen_access_proj_3; eauto.
  Qed.

  Lemma cond_access_step_to_gen_access:
    forall x m n a v,
    n < m ->
    CStep (cond_access_subst x (NNum n) a, NNum n) v ->
    exists l, List.In v l /\ GenAccess x a m l.
  Proof.
    induction m; intros. {
      omega.
    }
    inversion H; subst; clear H. {
      destruct m. {
        exists [v].
        auto using gen_access_cons, gen_access_nil, in_eq.
      }
      assert (Hx := cond_access_step_next _ _ _ _ H0 m).
      destruct Hx as (v2, Hs).
      apply IHm in Hs; auto.
      destruct Hs as (l, (Hi, Hg)).
      exists (v::l).
      split; auto using in_eq.
      apply gen_access_cons; auto.
    }
    destruct m. {
      omega.
    }
    assert (Hy := cond_access_step_next _ _ _ _ H0 (S m)).
    destruct Hy as (v', Hi).
    apply IHm in H0; auto.
    destruct H0 as (l, (Hj, Hg)).
    eauto using gen_access_cons, in_cons.
  Qed.

  Lemma m_in_gen_access_inv:
    forall x a m v vs,
    GenAccess x a m vs ->
    MIn v vs ->
    exists n l,
    n < m /\
    CStep (cond_access_subst x (NNum n) a, NNum n) l /\
    List.In l vs /\
    List.In v l.
  Proof.
    induction m; intros. {
      inversion H; subst; clear H.
      apply m_in_nil in H0.
      contradiction.
    }
    inversion H; subst; clear H.
    apply m_in_inv in H0.
    destruct H0. {
      exists m.
      exists v0.
      repeat split; auto using in_eq.
    }
    eapply IHm in H2; eauto.
    destruct H2 as (n, (l2, (?, (?, (?, ?))))).
    exists n.
    exists l2.
    repeat split; auto using in_cons with *.
  Qed.

  Lemma safe2_sym:
    forall h1 h2,
    Safe2 h1 h2 <-> Safe2 h2 h1.
  Proof.
    unfold Safe2; split; intros.
    - auto using access_safe_sym.
    - auto using access_safe_sym.
  Qed.

  Lemma safe2_app:
    forall h1 h2,
    Safe h1 /\ Safe h2 /\ Safe2 h1 h2 <-> Safe (h1 ++ h2).
  Proof.
    unfold Safe, Safe2; split; intros.
    - destruct H as (Ha, (Hb, Hc)).
      apply in_app_or in H0.
      apply in_app_or in H1.
      destruct H0, H1; auto using access_safe_sym.
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

  Lemma gen_access_fun:
    forall x e n v1 v2,
    GenAccess x e n v1 ->
    GenAccess x e n v2 ->
    v1 = v2.
  Proof.
    intros.
    apply prop_to_gen_access in H.
    apply prop_to_gen_access in H0.
    rewrite H in *.
    inversion H0.
    auto.
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
    destruct Hi, Hj; auto using access_safe_sym.
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
  Lemma m_proj_prepend:
    forall hs x m e n vs v,
    n < m ->
    GenAccess x e m vs ->
    CStep (cond_access_subst x (NNum n) e, NNum n) v ->
    m_proj n (prepend (List.concat vs) hs) = prepend v (m_proj n hs).
  Proof.
    induction hs. {
      intros.
      reflexivity.
    }
    intros.
    assert (Hx := gen_access_proj_rw x m e vs v n H0 H H1).
    simpl.
    rewrite proj_app.
    rewrite Hx.
    unfold m_proj.
    erewrite map_proj_prepend; eauto.
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
    destruct (Nat.eq_dec (access_tid x) (access_tid y)). {
      auto using access_safe_eq_tid.
    }
    eauto using m_in_def.
  Qed.

  Definition PairInclMPair (h:list access_val) m :=
    forall x y,
    In x h ->
    In y h ->
    (*access_tid x <> access_tid y ->*)
    MPairIn (x, y) m.

  Lemma m_safe_strong_to_safe:
    forall m h,
    PairInclMPair h m ->
    MSafeStrong m ->
    Safe h.
  Proof.
    unfold MSafeStrong, Safe; intros.
    assert (X: access_tid x = access_tid y \/ access_tid x <> access_tid y) by omega.
    destruct X. {
      auto using access_safe_eq_tid.
    }
    unfold PairInclMPair in *; auto.
  Qed.

  Lemma access_in_inv_neq:
    forall x y z a,
    x <> y ->
    x <> z ->
    access_in x (access_subst z (NVar y) a) ->
    access_in x a.
  Proof.
    intros.
    apply access_in_subst_neq in H1; auto.
    intros N.
    inversion N.
    contradiction.
  Qed.
End Defs.
