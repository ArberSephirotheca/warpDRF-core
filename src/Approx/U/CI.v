From Faial.Core Require Import Tasks.
From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Stdlib Require Import List.
Require Import U.Lang.
Import ListNotations.
From Faial.Core Require Import Tictac.
From Stdlib Require Import Sorting.SetoidList.
From Faial.Core Require Import InUtil.

Require U.WF.
Require U.Bound.
Require U.Free.
Require U.LRun.
Require U.Subst.

From Faial.Expr Require SIMT.N.WellTyped.
From Faial.Expr Require SIMT.B.WellTyped.
From Faial.Expr Require SIMT.R.WellTyped.
Require EqualModIndex.

From Faial.Expr Require Import SIMT.B.Equal.

  Inductive t : list var -> U.Lang.t -> Prop :=
  | acc:
    forall env a,
    t env (MemAcc a)
  | seq:
    forall env s1 s2,
    t env s1 ->
    t env s2 ->
    t env (Seq s1 s2)
  | cond:
    forall env c s1 s2,
    B.WellTyped.t env c ->
    t env s1 ->
    t env s2 ->
    t env (If c s1 s2)
  | loop:
    forall env r s x,
    R.WellTyped.t env r ->
    t (x::env) s ->
    t env (For x r s)
  | skip:
    forall env,
    t env Skip
  | decl:
    forall env x s,
    t env s ->
    t env (Decl x s)
  .

Section Def.
  Context `{T:Tasks}.

  Lemma subst:
    forall env s,
    t env s ->
    forall x n,
    t env (Subst.f x (NNum n) s).
  Proof.
    intros env s H.
    induction H.
    all: intros y n.
    all: simpl.
    all: constructor.
    all: auto using N.WellTyped.subst, B.WellTyped.subst, R.WellTyped.subst.
    all: destruct (Set_VAR.MF.eq_dec y x).
    all: subst.
    all: auto.
  Qed.

  Lemma reorder:
    forall e env1,
    t env1 e ->
    forall env2,
    SetEq.t env1 env2 ->
    t env2 e.
  Proof.
    intros e env1 H.
    induction H.
    all: intros env2 eq1.
    all: constructor.
    all: eauto using N.WellTyped.reorder, R.WellTyped.reorder, B.WellTyped.reorder.
    all: auto using SetEq.cons.
    all: intros N.
    all: rename_hyp (~ _) as M.
    all: contradict M.
    all: apply eq1.
    all: assumption.
  Qed.

  Lemma strengthen:
    forall s x env,
    t (x :: env) s ->
    ~ Free.t x s ->
    ~ Bound.t x s ->
    t env s.
  Proof.
    induction s.
    all: intros x env wt nf nb.
    all: simpl in nf, nb.
    all: invc wt.
    all: constructor.
    all: eauto using
      N.WellTyped.strengthen, B.WellTyped.strengthen, R.WellTyped.strengthen.
    all: intuition.
    all: eauto.
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      eapply reorder; eauto.
      unfold SetEq.t.
      intros a.
      simpl.
      split.
      all: intros [Hx|Hx].
      all: auto.
    }
    assert (t (x :: v :: env) s). {
      eapply reorder; eauto.
      unfold SetEq.t.
      intros.
      simpl.
      split.
      all: intros [Hx|[Hx|Hx]].
      all: auto.
    }
    eauto.
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

  Lemma func_trace_multi_subst tid:
    forall u h1 l1 m1,
    LRun.t tid (MultiSubst.f m1 u) h1 l1 ->
    forall h2 m2 l2,
    LRun.t tid (MultiSubst.f m2 u) h2 l2 ->
    forall env,
    t env u ->
    forall dom,
    incl env dom ->
    WF.t dom u ->
    (forall x, In x env -> forall v, Map_VAR.MapsTo x v m1 <-> Map_VAR.MapsTo x v m2) ->
    l1 = l2.
  Proof.
    intros u h1 l1 m1 H.
    remember (MultiSubst.f _ _) as s.
    generalize dependent m1.
    generalize dependent u.
    induction H.
    all: intros [] m1 eq1 hb m2 lb rb env wt dom hinc wf S.
    all: invc eq1.
    all: simpl in rb.
    all: invc rb.
    all: auto.
    - invc wf.
      invc wt.
      f_equal.
      all: eauto.
    - invc wf.
      invc wt.
      assert (b = b1). {
        assert (eq1: B.Equal.t tid (B.MultiSubst.f m1 b0) (B.MultiSubst.f m2 b0)). {
          eauto using B.WellTyped.multi_subst_to_equal.
        }
        rewrite eq1 in *.
        eauto using b_step_fun.
      }
      subst.
      destruct b1.
      all: f_equal.
      all: eauto.
    - invc wt.
      invc wf.
      assert (n0 = n). {
        assert (r1: R.Equal.t tid (R.MultiSubst.f m1 r0) (R.MultiSubst.f m2 r0)). {
          apply R.WellTyped.multi_subst_to_equal with (env:=env); eauto.
        }
        assert (R.Step.t tid (R.MultiSubst.f m2 r0) n r'). {
          rewrite <- r1.
          assumption.
        }
        eauto using R.Step.func_1.
      }
      subst.
      f_equal.
      + clear IHt2.
        assert (eq1:
          Subst.f v (NNum n) (MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) t0) 
          =
          MultiSubst.f (Map_VAR.add v n (Map_VAR.remove (elt:=nat) v m1)) t0
        ). {
          rewrite MultiSubst.subst_to_add.
          all: auto using not_in_remove.
        }
        rename_hyp (LRun.t _ _ _ l0) as r1.
        rewrite MultiSubst.subst_to_add in r1; auto using not_in_remove.
        rename_hyp (t _ _) as wt.
        assert (hi: incl (v :: env) (v::dom)) by auto using List.incl_cons_cons.
        rename_hyp (WF.t _ _) as wf. 
        assert (IHt1 := IHt1 _ _ eq1 _ _ _ r1 _ wt _ hi wf).
        apply IHt1.
        intros x ha.
        destruct ha as [?|ha]. {
          subst.
          intros.
          split.
          all: intros ha.
          - assert (v = n). {
              assert (Map_VAR.MapsTo x n (Map_VAR.add x n (Map_VAR.remove x m1))). {
                auto using Map_VAR.add_1.
              }
              eauto using Map_VAR_Facts.MapsTo_fun.
            }
            subst.
            auto using Map_VAR.add_1.
          - assert (v = n). {
              assert (Map_VAR.MapsTo x n (Map_VAR.add x n (Map_VAR.remove x m2))). {
                auto using Map_VAR.add_1.
              }
              eauto using Map_VAR_Facts.MapsTo_fun.
            }
            subst.
            auto using Map_VAR.add_1.
        }
        intros e.
        repeat rewrite rw_add_remove_eq.
        destruct (VAR.eq_dec x v). {
          subst.
          split.
          all: intros hb.
          {
            assert (e = n). {
              assert (Map_VAR.MapsTo v n (Map_VAR.add v n m1)). {
                auto using Map_VAR.add_1.
              }
              eauto using Map_VAR_Facts.MapsTo_fun.
            }
            subst.
            auto using Map_VAR.add_1.
          }
          {
            assert (e = n). {
              assert (Map_VAR.MapsTo v n (Map_VAR.add v n m2)). {
                auto using Map_VAR.add_1.
              }
              eauto using Map_VAR_Facts.MapsTo_fun.
            }
            subst.
            auto using Map_VAR.add_1.
          }
        }
        split.
        all: intros hb.
        all: apply Map_VAR.add_3 in hb; auto.
        all: apply Map_VAR.add_2; auto.
        all: apply S; auto.
      + clear IHt1.
        assert (R.Closed.t r'). {
          eauto using R.Step.to_closed_r.
        }
        assert (forall e, WellTyped.t e r') by auto using WellTyped.from_closed.
        assert (eq1:
          For v r' (MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) t0) =
          MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) (For v r' t0)
        ). {
          simpl.
          f_equal.
          + rewrite R.MultiSubst.rw_closed; auto.
          + apply MultiSubst.subst_eq.
            rewrite rw_remove_remove_eq.
            reflexivity.
        }
        assert (r2: LRun.t tid (MultiSubst.f m2 (For v r' t0)) h3 l3). {
          simpl.
          rewrite R.MultiSubst.rw_closed; auto.
          eapply LRun.loop_rw; eauto.
          assert (r1: R.Equal.t tid (R.MultiSubst.f m1 r0) (R.MultiSubst.f m2 r0)). {
            eauto using R.WellTyped.multi_subst_to_equal.
          }
          assert (R.Step.t tid (R.MultiSubst.f m1 r0) n r'0). {
            rewrite r1.
            assumption.
          }
          eauto using R.Equal.from_step.
        }
        assert (wt: t env (For v r' t0)). {
          constructor.
          all: auto.
        }
        assert (wf: WF.t dom (For v r' t0)). {
          constructor.
          all: auto.
        }
        assert (IHt2 := IHt2 _ _ eq1 _ _ _ r2 _ wt _ hinc wf).
        apply IHt2.
        intros x hi e.
        split.
        all: intros hm.
        * apply Map_VAR.remove_3 in hm.
          apply S; auto.
        * destruct (VAR.eq_dec x v). {
            subst.
            rename_hyp (~ In v _) as N.
            contradict N.
            auto.
          }
          apply Map_VAR.remove_2; auto.
          apply S.
          all: auto.
    - invc wf.
      invc wt.
      assert (r1: R.Equal.t tid (R.MultiSubst.f m1 r0) (R.MultiSubst.f m2 r0)). {
        apply R.WellTyped.multi_subst_to_equal with (env:=env); auto.
      }
      rewrite r1 in *.
      rename_hyp (R.Empty.t _ _) as re.
      contradict re.
      eauto using R.Step.to_empty.
    - invc wf.
      invc wt.
      assert (r1: R.Equal.t tid (R.MultiSubst.f m1 r0) (R.MultiSubst.f m2 r0)). {
        apply R.WellTyped.multi_subst_to_equal with (env:=env); auto.
      }
      rewrite r1 in *.
      rename_hyp (R.Empty.t _ _) as re.
      contradict re.
      eauto using R.Step.to_empty.
    - assert (eq1:  Subst.f v (NNum n') (MultiSubst.f (Map_VAR.remove (elt:=nat) v m1) t0) 
        =  MultiSubst.f (Map_VAR.add v n' (Map_VAR.remove v m1)) t0
      ). {
        rewrite MultiSubst.subst_to_add; auto using not_in_remove.
      }
      assert (r1: LRun.t tid (MultiSubst.f (Map_VAR.add v n'0 (Map_VAR.remove (elt:=nat) v m2)) t0) hb lb). {
        rewrite MultiSubst.subst_to_add in *; auto using not_in_remove.
      }
      invc wf.
      rename_hyp (WF.t _ _) as wf.
      invc wt.
      rename_hyp (t _ _) as wt.
      assert (inc1: incl env (v :: dom)) by auto using List.incl_tl.
      assert (IHt := IHt _ _ eq1 _ _ _ r1 _ wt _ inc1 wf).
      apply IHt.
      intros.
      split.
      all: intros hm.
      + destruct (VAR.eq_dec x v). {
          subst.
          rename_hyp (~ In _ _) as N.
          contradict N.
          apply hinc.
          assumption.
        }
        apply Map_VAR.add_2; auto.
        apply Map_VAR.add_3 in hm; auto.
        apply Map_VAR.remove_3 in hm.
        apply Map_VAR.remove_2; auto.
        apply S; auto.
      + destruct (VAR.eq_dec x v). {
          subst.
          rename_hyp (~ In _ _) as N.
          contradict N.
          apply hinc.
          assumption.
        }
        apply Map_VAR.add_2; auto.
        apply Map_VAR.add_3 in hm; auto.
        apply Map_VAR.remove_3 in hm.
        apply Map_VAR.remove_2; auto.
        apply S; auto.
  Qed.


  Lemma func_trace_subst tid:
    forall u h1 l1 x n1,
    LRun.t tid (Subst.f x (NNum n1) u) h1 l1 ->
    forall h2 n2 l2,
    LRun.t tid (Subst.f x (NNum n2) u) h2 l2 ->
    forall env,
    ~ List.In x env ->
    t env u ->
    forall dom,
    incl env dom ->
    WF.t dom u ->
    l1 = l2.
  Proof.
    intros.
    rewrite MultiSubst.from_subst in *.
    eapply func_trace_multi_subst; eauto.
    intros y hi v.
    destruct (VAR.eq_dec y x). 2: {
      split.
      all: intros hm.
      all: apply Map_VAR.add_3 in hm; auto.
      all: rewrite Map_VAR_Facts.empty_mapsto_iff in *.
      all: contradiction.
    }
    subst.
    contradiction.
  Qed.

  Lemma func tid:
    forall s h1 l1,
    LRun.t tid s h1 l1 ->
    forall h2 l2,
    LRun.t tid s h2 l2 ->
    forall env,
    t env s ->
    forall dom,
    incl env dom ->
    WF.t dom s ->
    l1 = l2.
  Proof.
    intros s ha la H.
    induction H.
    all: intros hb lb rb env wt dom Hinc wf.
    all: invc rb.
    all: auto.
    - invc wf.
      invc wt.
      f_equal.
      all: eauto.
    - invc wf.
      invc wt.
      assert (b0 = b) by eauto using b_step_fun.
      subst.
      destruct b.
      all: f_equal.
      all: eauto.
    - assert (n0 = n) by eauto using R.Step.func_1.
      subst.
      assert (R.Closed.t r') by eauto using R.Step.to_closed_r.
      assert (forall e, R.WellTyped.t e r') by auto using R.WellTyped.from_closed.
      f_equal.
      + clear IHt2.
        rename_hyp (LRun.t _ _ _ l0) as r1.
        invc wt.
        assert (wt: t env (Subst.f x (NNum n) i)). {
          invc wf.
          apply subst_strengthen; auto.
          eapply WF.in_env_not_bound; eauto using in_eq.
        }
        rename_hyp (t _ _) as wt.
        assert (wf1: WF.t dom (Subst.f x (NNum n) i)). {
          invc wf.
          auto using WF.subst_strengthen.
        }
        assert (IHt1 := IHt1 _ _ r1 _ wt _ Hinc wf1).
        assumption.
      + clear IHt1.
        assert (r2: LRun.t tid (For x r' i) h3 l3). {
          eapply LRun.loop_rw; eauto using R.Equal.from_step.
        }
        assert (wt2: t env (For x r' i)). {
          invc wt.
          constructor.
          all: auto.
        }
        assert (wf2: WF.t dom (For x r' i) ). {
          invc wf.
          constructor.
          all: auto.
        }
        assert (IHt2 := IHt2 _ _ r2 _ wt2 _ Hinc wf2).
        assumption.
      - rename_hyp (R.Empty.t _ _) as re.
        contradict re.
        eauto using R.Step.to_empty.
      - rename_hyp (R.Empty.t _ _) as re.
        contradict re.
        eauto using R.Step.to_empty.
      - invc wt.
        invc wf.
        eapply func_trace_subst with (dom:=x:: dom) (env:=env); eauto using List.incl_tl.
  Qed.

End Def.
