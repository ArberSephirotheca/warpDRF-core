From Faial.Core Require Import Var.
From Faial.Core Require Import InUtil.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Lists.List.

From Faial.Expr Require SIMT.N.Exp.
From Faial.Expr Require SIMT.A.WellTyped.

Require U.Lang.
Require U.LRun.
Require U.Subst.
Require U.MultiSubst.

Import ListNotations.

Section WellTyped.
  Import U.Lang.
  Import N.Exp.
  Inductive t : list var -> Lang.t -> Prop :=
  | acc:
    forall env a,
    N.WellTyped.t env (A.Exp.ae_index a) ->
    t env (MemAcc a)
  | decl:
    forall env x u,
    t env u ->
    t env (Decl x u)
  | seq:
    forall env u1 u2,
    t env u1 ->
    t env u2 ->
    t env (Seq u1 u2)
  | cond:
    forall env c u1 u2,
    t env u1 ->
    t env u2 ->
    t env (If c u1 u2)
  | loop_dep:
    forall env r s x,
    t env s ->
    t env (For x r s)
  | loop_indep:
    forall env r s x,
    R.WellTyped.t env r ->
    t (x::env) s ->
    t env (For x r s)
  | skip:
    forall env,
    t env Skip
  .


  Lemma subst:
    forall env u,
    t env u ->
    forall x n,
    t env (Subst.f x (NNum n) u).
  Proof.
    intros env u H.
    induction H.
    all: intros y n.
    all: simpl.
    - constructor.
      { destruct a.
        simpl in *.
        eauto using N.WellTyped.subst. }
    - constructor.
      destruct (Set_VAR.MF.eq_dec y x).
      all: subst.
      all: eauto.
    - constructor.
      all: eauto.
    - constructor.
      all: eauto.
    - apply loop_dep.
      destruct (Set_VAR.MF.eq_dec y x).
      all: subst.
      all: eauto.
    - apply loop_indep.
      { eauto using R.WellTyped.subst. }
      destruct (Set_VAR.MF.eq_dec y x).
      all: subst.
      all: eauto.
    - constructor.
  Qed.

  Lemma reorder:
    forall u env1 env2,
    SetEq.t env1 env2 ->
    t env1 u ->
    t env2 u.
  Proof.
    induction u.
    all: intros env1 env2 eq1 wt.
    all: invc wt.
    all: try (constructor; eauto; fail).
    - constructor.
      all: eauto using N.WellTyped.reorder.
    - apply loop_indep.
      + eauto using R.WellTyped.reorder.
      + eauto using SetEq.cons.
  Qed.

  Lemma strengthen:
    forall u x env,
    t (x :: env) u ->
    ~ Free.t x u ->
    ~ Bound.t x u ->
    t env u.
  Proof.
    induction u.
    all: intros x env wt nf nb.
    all: simpl in nf, nb.
    all: invc wt.
    - constructor.
    - constructor.
      + eapply IHu1; eauto.
      + eapply IHu2; eauto.
    - constructor.
      + eapply IHu1; eauto.
      + eapply IHu2; eauto.
    - constructor.
      destruct a.
      simpl in *.
      eauto using N.WellTyped.strengthen.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assert (~ Free.t v u) by auto.
        apply loop_dep; auto.
        eapply IHu; eauto.
      }
      apply loop_dep.
      eapply IHu; eauto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assert (~ Free.t v u) by auto.
        apply loop_dep.
        eapply IHu; eauto.
      }
      apply loop_indep.
      { eauto using R.WellTyped.strengthen. }
      {
        eapply IHu; eauto.
        eapply reorder; eauto.
        unfold SetEq.t.
        intros.
        simpl.
        split.
        all: intros [Hx|[Hx|Hx]].
        all: auto.
      }
    - constructor.
      eapply IHu; eauto.
      intuition.
  Qed.

  Lemma subst_strengthen:
    forall s x env,
    t (x :: env) s ->
    ~ Bound.t x s ->
    forall n,
    t env (Subst.f x (NNum n) s).
  Proof.
    intros.
    apply strengthen with (x:=x).
    - apply subst.
      assumption.
    - apply Free.not_free_after_subst.
      apply n_free_num.
    - auto using Bound.not_free_after_subst.
  Qed.

  Lemma multi_subst_change tid:
    forall u m1 P1 l,
    LRun.t tid (MultiSubst.f m1 u) P1 l ->
    forall env,
    t env u ->
    forall dom,
    incl env dom ->
    WF.t dom u ->
    forall P2 m2,
    LRun.t tid (MultiSubst.f m2 u) P2 l ->
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    LRun.t tid (MultiSubst.f m1 u) P2 l.
  Proof.
    intros u m1 P1 l H.
    remember (MultiSubst.f _ _) as u1.
    generalize dependent u.
    generalize dependent m1.
    induction H.
    all: intros m1 u_orig heq env wt dom Hinc wf P2 m2 hr S1.
    all: destruct u_orig.
    all: simpl in *.
    all: invc heq.
    - assumption.
    - invc hr.
      invc wt.
      constructor.
      assert (eq1: A.Equal.t tid (A.MultiSubst.f m1 a) (A.MultiSubst.f m2 a)). {
        eapply A.WellTyped.multi_subst_to_equal; eauto.
      }
      rewrite eq1.
      assumption.
    - (* sequence *)
      invc hr.
      invc wt.
      invc wf.
      constructor.
      all: eauto.
    - (* conditional *)
      invc hr.
      invc wt.
      invc wf.
      rename_hyp (_ = _) as eq1.
      destruct b1, b.
      all: invc eq1.
      all: eauto using LRun.cond_true, LRun.cond_false.
    - assert (hr1: LRun.t tid
        (For v (R.MultiSubst.f m1 r0) (U.MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) u_orig))
        (h1 ++ h2) (Trace.iter (v, n) l1 l2)). {
        eauto using LRun.for_cons.
      }
      assert (hra: LRun.t tid (For v (R.MultiSubst.f m1 r0) (MultiSubst.f (Map_VAR.remove (elt:=nat) v m2) u_orig))
       P2 (Trace.iter (v, n) l1 l2)). {
        eauto using LRun.loop_range.
      }
      clear hr1 hr.
      invc hra.
      assert (~ Map_VAR.In v (Map_VAR.remove v m1)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      assert (~ Map_VAR.In v (Map_VAR.remove v m2)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      apply LRun.for_cons with (r':=r'0).
      + assumption.
      + (* step *)
        rewrite MultiSubst.subst_to_add in *; auto.
        clear IHt2.
        invc wf.
        assert (IHt1 := IHt1 _ _ eq_refl).
        rename_hyp (LRun.t _ _ h0 l1) as r1.
        rename_hyp (LRun.t _ _ h1 l1) as r2.
        invc wt.
        all: rename_hyp (t _ _) as wt.
        all: rename_hyp (WF.t _ _) as wf.
        * (* loop_dep *)
          assert (Hinc1 : incl env (v :: dom)) by auto using List.incl_tl.
          assert (IHt1 := IHt1 _ wt _ Hinc1 wf _ _ r1).
          apply IHt1.
          intros.
          destruct (VAR.eq_dec x v). {
            subst.
            repeat rewrite rw_add_remove_eq.
            split.
            all: intros ha.
            all: assert (v0 = n) by (eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1).
            all: subst.
            all: auto using Map_VAR.add_1.
          }
          repeat rewrite rw_add_remove_eq.
          split.
          all: intros ha.
          all: apply Map_VAR.add_3 in ha; auto.
          all: apply Map_VAR.add_2; auto.
          all: apply S1; auto.
        * (* loop_indep *)
          assert (Hinc1 : incl (v :: env) (v :: dom)) by auto using List.incl_cons_cons.
          assert (IHt1 := IHt1 _ wt _ Hinc1 wf _ _ r1).
          apply IHt1.
          intros x hi v1.
          destruct hi as [hi|hi]. {
            subst.
            split.
            all: intros ha.
            all: assert (v1 = n) by (eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1).
            all: subst.
            all: auto using Map_VAR.add_1.
          }
          repeat rewrite rw_add_remove_eq.
          destruct (VAR.eq_dec x v). {
            subst.
            split.
            all: intros ha.
            all: assert (v1 = n) by (eapply Map_VAR_Facts.MapsTo_fun; eauto using Map_VAR.add_1).
            all: subst.
            all: auto using Map_VAR.add_1.
          }
          split.
          all: intros ha.
          all: apply Map_VAR.add_3 in ha; auto.
          all: apply Map_VAR.add_2; auto.
          all: apply S1; auto.
      + (* rest of loop *)
        clear IHt1.
        rewrite MultiSubst.subst_to_add in *; auto.
        assert (R.Closed.t r') by eauto using R.Step.to_closed_r.
        assert (R.Closed.t r'0) by eauto using R.Step.to_closed_r.
        assert (rw_r'0:forall m, R.MultiSubst.f m r'0 = r'0). { intros. rewrite R.MultiSubst.rw_closed. all: auto. }
        assert (rw_r':forall m, R.MultiSubst.f m r' = r'). { intros. rewrite R.MultiSubst.rw_closed. all: auto. }
        assert (forall e, R.WellTyped.t e r'). { auto using R.WellTyped.from_closed. }
        assert (eq1:
          For v r' (MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) u_orig) =
          MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) (For v r' u_orig)
        ). {
          simpl.
          rewrite rw_r'.
          f_equal.
          apply MultiSubst.subst_eq.
          intros.
          rewrite Map_VAR_Facts.Equal_mapsto_iff.
          intros k e.
          split.
          all: intros ha.
          all: destruct (VAR.eq_dec k v).
          - subst.
            apply Map_VAR_Extra.mapsto_to_in in ha.
            contradiction.
          - apply Map_VAR.remove_2; auto.
          - subst.
            apply Map_VAR.remove_3 in ha.
            apply Map_VAR_Extra.mapsto_to_in in ha.
            contradiction.
          - apply Map_VAR.remove_3 in ha.
            assumption.
        }
        assert (r2: LRun.t tid (MultiSubst.f m2 (For v r' u_orig)) h3 l2). {
          simpl.
          rewrite rw_r'.
          eauto using LRun.loop_range.
        }
        assert (wt2: t env (For v r' u_orig)). {
          invc wt.
          + auto using loop_dep.
          + apply loop_indep; auto.
        }
        assert (wf2:  WF.t dom (For v r' u_orig)). {
          invc wf.
          constructor.
          all: auto.
        }
        assert (S1' : forall x : var,
          In x env ->
          forall v0,
          Map_VAR.MapsTo x v0 (Map_VAR.remove  v m1) <-> Map_VAR.MapsTo x v0 m2
        ). {
          intros.
            assert (x <> v). {
              intros N.
              subst.
              invc wf2.
              rename_hyp (~ In v dom) as hd.
              contradict hd.
              apply Hinc.
              assumption.
            }
            split.
            all: intros ha. {
              apply S1; auto.
              apply Map_VAR.remove_3 in ha.
              assumption.
            }
            apply Map_VAR.remove_2; auto.
            apply S1; auto.
        }
        assert (IHt2 := IHt2 _ _ eq1 _ wt2 _ Hinc wf2 _ _ r2 S1').
        assert (r2': LRun.t tid (For v r' (MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) u_orig)) h3 l2). {
          apply IHt2.
        }
        clear r2.
        eapply LRun.loop_range; eauto.
    - assert (Hx: LRun.t tid (For v (R.MultiSubst.f m1 r0) (MultiSubst.f (Map_VAR.remove v m1) u_orig))
        [] Trace.skip). {
        apply LRun.for_nil.
        assumption.
      }
      assert (Hr: LRun.t tid (For v (R.MultiSubst.f m1 r0) (MultiSubst.f (Map_VAR.remove v m2) u_orig))
        P2 Trace.skip). {
        eauto using LRun.loop_range.
      }
      clear hr Hx.
      invc Hr.
      constructor.
      assumption.
    - rename_hyp (LRun.t _ _ h l) as r1.
      invc hr.
      rename_hyp (LRun.t _ _ P2 l) as r2.
      apply LRun.decl with (n':=n').
      assert (~ Map_VAR.In v (Map_VAR.remove v m1)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      assert (~ Map_VAR.In v (Map_VAR.remove v m2)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      rewrite MultiSubst.subst_to_add in *; auto.
      invc wt.
      rename_hyp (t _ _) as wt.
      invc wf.
      rename_hyp (WF.t _ _) as wf.
      assert (Hinc1 : incl env (v :: dom)) by auto using List.incl_tl.
      assert (IHt := IHt _ _ eq_refl _ wt _ Hinc1 wf _ _ r2).
      apply IHt.
      intros.
      destruct (VAR.eq_dec x v). {
        subst.
        split.
        all: intros ha.
        all: rename_hyp (~ In _ _) as nin.
        all: contradict nin.
        all: apply Hinc.
        all: assumption.
      }
      repeat rewrite rw_add_remove_eq.
      split.
      all: intros ha.
      all: apply Map_VAR.add_3 in ha; auto.
      all: apply Map_VAR.add_2; auto.
      all: apply S1; auto.
  Qed.

  Lemma i_subst_change tid:
    forall u x n1 P1 l,
    LRun.t tid (Subst.f x (NNum n1) u) P1 l ->
    forall env,
    ~ In x env ->
    t env u ->
    forall dom,
    incl env dom ->
    WF.t dom u ->
    forall P2 n2,
    LRun.t tid (Subst.f x (NNum n2) u) P2 l ->
    LRun.t tid (Subst.f x (NNum n1) u) P2 l.
  Proof.
    intros.
    rewrite U.MultiSubst.from_subst in *.
    eapply multi_subst_change; eauto.
    intros y hi v.
    assert (x <> y). { intros N. subst. contradiction. }
    split.
    all: intros ha.
    all: apply Map_VAR.add_3 in ha; auto.
    all: apply Map_VAR.add_2; auto.
  Qed.

  Lemma func tid:
    forall s h1 l,
    LRun.t tid s h1 l ->
    forall h2,
    LRun.t tid s h2 l ->
    forall env,
    t env s ->
    forall dom,
    incl env dom ->
    WF.t dom s ->
    h1 = h2.
  Proof.
    intros s h1 l H.
    induction H.
    all: intros P hr env wt dom Hinc wf.
    all: invc wt.
    all: invc hr.
    all: f_equal.
    all: eauto.
    - eauto using A.Exp.a_step_fun.
    - invc wf.
      eauto.
    - invc wf.
      eauto.
    - rename_hyp (_ = _) as eq1.
      invc wf.
      destruct b0, b.
      all: invc eq1.
      all: eauto.
    - (* loop step / loop dep *)
      clear IHt2.
      rename_hyp (LRun.t _ _ h0 _) as r1.
      invc wf.
      assert (wt:  t env (Subst.f x (NNum n) i)) by auto using subst.
      assert (hi1: incl env (x::dom)) by auto using List.incl_tl. 
      assert (wf: WF.t (x :: dom) (Subst.f x (NNum n) i) ) by auto using WF.subst.
      assert (IHt1 := IHt1 _ r1 _ wt _ hi1 wf).
      assumption.
    - clear IHt1.
      (* loop rest / loop dep *)
      assert (r1: LRun.t tid (For x r' i) h3 l2). {
        eapply LRun.loop_range; eauto.
      }
      invc wf.
      assert (R.Closed.t r'). { eauto using R.Step.to_closed_r. }
      assert (forall e, R.WellTyped.t e r'). { auto using R.WellTyped.from_closed. } 
      assert (wt2: t env (For x r' i)). { apply loop_dep. assumption. }
      assert (wf2: WF.t dom (For x r' i)). { constructor. all: auto. }
      assert (IHt2 := IHt2 _ r1 _ wt2 _ Hinc wf2).
      assumption.
    - (* loop step / loop dep *)
      clear IHt2.
      rename_hyp (LRun.t _ _ h0 _) as r1.
      invc wf.
      assert (wt:  t env (Subst.f x (NNum n) i)). {
        apply subst_strengthen; auto.
        eapply WF.in_env_not_bound; eauto using in_eq.
      }
      assert (hi1: incl (x::env) (x::dom)) by auto using List.incl_cons_cons. 
      assert (wf: WF.t dom (Subst.f x (NNum n) i) ) by auto using WF.subst_strengthen.
      assert (IHt1 := IHt1 _ r1 _ wt _ Hinc wf).
      assumption.
    - (* loop rest / loop indep *)
      assert (r1: LRun.t tid (For x r' i) h3 l2). {
        eapply LRun.loop_range; eauto.
      }
      invc wf.
      assert (R.Closed.t r'). { eauto using R.Step.to_closed_r. }
      assert (forall e, R.WellTyped.t e r'). { auto using R.WellTyped.from_closed. } 
      assert (wt2: t env (For x r' i)). { apply loop_indep. all: auto. }
      assert (wf2: WF.t dom (For x r' i)). { constructor. all: auto. }
      assert (IHt2 := IHt2 _ r1 _ wt2 _ Hinc wf2).
      assumption.
    - invc wf.
      assert (r1: LRun.t tid (Subst.f x (NNum n') i) P l). {
        eapply i_subst_change with (env:=env) (dom:=x :: dom); eauto using List.incl_tl.
      }
      eapply IHt in r1; eauto using subst, WF.subst_strengthen.
  Qed.
End WellTyped.