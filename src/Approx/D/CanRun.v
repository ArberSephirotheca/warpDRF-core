Require Import D.WF.
Require Import D.Lang.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Faial.Approx Require Import Tictac.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import Var.
Require R.Iter.
Require D.Subst.

Inductive t : D.Lang.t -> Prop :=
| read:
  forall x e s,
  N.WellTyped.t [] e ->
  (forall n, t (Subst.f x (NNum n) s)) ->
  t (Read x e s)
| decl:
  forall x s,
  (forall n, t (Subst.f x (NNum n) s)) ->
  t (Decl x s)
| loop:
  forall x r s,
  R.WellTyped.t [] r ->
  (forall n, t (Subst.f x (NNum n) s)) ->
  t (Loop x r s)
| write:
  forall idx e,
  N.WellTyped.t [] idx ->
  N.WellTyped.t [] e ->
  t (Write idx e)
| skip:
  t Skip
| seq:
  forall s1 s2,
  t s1 ->
  t s2 ->
  t (Seq s1 s2)
| cond:
  forall e s1 s2,
  B.WellTyped.t [] e ->
  t s1 ->
  t s2 ->
  t (Cond e s1 s2).

Lemma from_loop:
  forall tid r l lo hi l',
  Iter.t tid r l lo hi l' ->
  forall x s base M,
  (forall n M,
     exists h l M',
       LRun.t tid base M (Subst.f x (NNum n) s) h M' l) ->
  exists h l' M2, LRun.t tid base M (Loop x r s) h M2 l'.
Proof.
  intros tid r l1 lo hi l2 H.
  induction H.
  all: intros x s base M Ha.
  - assert (He: R.Empty.t tid r) by eauto using Empty.from_start_end.
    eexists.
    eexists.
    eexists.
    apply LRun.loop_nil.
    assumption.
  - specialize (IHt x s base).
    assert (Hb := Ha).
    specialize (Ha lo M).
    destruct Ha as (h1, (l1', (M1, r1))).
    specialize (IHt M1 Hb).
    destruct IHt as (h_loop, (l_loop, (M_loop, r_loop))).
    eexists.
    eexists.
    eexists.
    eapply LRun.loop_cons; eauto.
Qed.

Lemma can_run:
  forall s,
  t s ->
  forall tid base M, exists h l M2, D.LRun.t tid base M s h M2 l.
Proof.
  intros s H.
  induction H.
  all: intros tid base M.
  - destruct (N.WellTyped.progress e) with (tid:=tid) as (idx, He); auto.
    destruct (Mem.MapsTo.read idx M base) as (n_val, Hm).
    rename_hyp (forall n tid, _) as he.
    specialize (he n_val tid base M).
    destruct he as (h, (l, (m', Hr))).
    eexists.
    eexists.
    exists m'.
    econstructor.
    all: eauto.
  - rename_hyp (forall n tid, _) as he.
    specialize (he 0 tid base M).
    destruct he as (h, (l, (m', Hr))).
    exists h.
    exists l.
    exists m'.
    eauto using LRun.decl.
  - rename_hyp (R.WellTyped.t _ _) as wt.
    assert (Hc: R.Closed.t r) by auto using R.WellTyped.to_closed.
    apply R.Iter.from_closed with (tid:=tid) in Hc.
    destruct Hc as (l, (lo, (hi, Hi))).
    eauto using from_loop.
  - destruct (N.WellTyped.progress e) with (tid:=tid) as (e_n, He); auto.
    destruct (N.WellTyped.progress idx) with (tid:=tid) as (e_idx, Hidx); auto.
    eexists.
    eexists.
    eexists.
    constructor.
    all: eauto.
  - eexists.
    eexists.
    eexists.
    constructor.
  - specialize (IHt1 tid base M).
    destruct IHt1 as (h1, (l1, (M2, r1))).
    specialize (IHt2 tid base M2).
    destruct IHt2 as (h2, (l2, (M3, r2))).
    eexists.
    eexists.
    eexists.
    econstructor; eauto.
  - destruct (B.WellTyped.progress e) with (tid:=tid) as (b, Hb); auto. 
    specialize (IHt1 tid base M).
    specialize (IHt2 tid base M).
    destruct IHt1 as (h1, (l1, (M1, r1))).
    destruct IHt2 as (h2, (l2, (M2, r2))).
    eexists.
    eexists.
    eexists.
    constructor.
    all: eauto.
Qed.

Lemma from_wf_ex:
  forall s env,
  WF.t env s ->
  forall m,
  (forall x, List.In x env <-> Map_VAR.In x m) ->
  t (D.MultiSubst.f m s).
Proof.
  induction s.
  all: intros env wf m spec.
  all: invc wf.
  all: simpl.
  - rename_hyp (WF.t _ _) as wf.
    constructor. { eapply N.WellTyped.multisubst; eauto. }
    intros n_val.
    assert (Hx: forall x, In x (v :: env) <-> Map_VAR.In (elt:=nat) x (Map_VAR.add v n_val m)). {
      split.
      all: intros Hi.
      + destruct Hi as [Hi|Hi]. {
          subst.
          apply Var.in_add_1.
        }
        apply spec in Hi.
        auto using Var.in_add_2.
      + destruct (VAR.eq_dec x v). {
          subst.
          intuition.
        }
        right.
        apply spec.
        eauto using Var.in_add_3.
    }
    specialize (IHs _ wf (Map_VAR.add v n_val m) Hx).
    rewrite D.MultiSubst.rw_add_not_in. 2:{ intros N. apply Map_VAR.remove_1 in N. all: auto. }
    assert (r1: MultiSubst.f (Map_VAR.add v n_val m) s = (MultiSubst.f (Map_VAR.add v n_val (Map_VAR.remove (elt:=nat) v m)) s)). {
      apply MultiSubst.subst_eq.
      rewrite rw_add_remove_eq.
      reflexivity.
    }
    rewrite <- r1.
    assumption.
  - constructor.
    all: eauto using N.WellTyped.multisubst.
  - constructor.
    all: eauto.
  - constructor.
    all: eauto using B.WellTyped.multisubst.
  - constructor. { eauto using R.WellTyped.multisubst. }
    intros n_val.
    rename_hyp (WF.t _ _) as wf.
    rewrite D.MultiSubst.rw_add_not_in. 2:{ auto using Map_VAR.remove_1. }
    assert (spec2:  (forall x, In x (v :: env) <-> Map_VAR.In x (Map_VAR.add v n_val (Map_VAR.remove (elt:=nat) v m)))). {
      simpl.
      split.
      all: intros Hi.
      + destruct Hi as [Hi|Hi]. {
          subst.
          auto using in_add_1.
        }
        assert (x <> v). {
          intros N.
          subst.
          contradiction.
        }
        apply in_add_2.
        apply in_remove_2. { auto. }
        apply spec.
        assumption.
      + destruct (VAR.eq_dec v x). { intuition. }
        right. 
        apply in_add_3 in Hi. 2:{ auto. }
        apply spec.
        eauto using in_remove_3.
    }
    specialize (IHs _ wf _ spec2).
    assumption.
  - constructor.
  - constructor.
    intros n_val.
    rewrite D.MultiSubst.rw_add_not_in. 2:{ auto using Map_VAR.remove_1. }
    eapply IHs; eauto.
    simpl.
    split.
    all: intros Hi.
    + destruct Hi as [Hi|Hi]. {
        subst.
        auto using in_add_1.
      }
      apply spec in Hi.
      destruct (VAR.eq_dec x v). {
        subst.
        auto using in_add_1.
      }
      auto using in_add_2, in_remove_2.
    + destruct (VAR.eq_dec x v). {
        subst.
        intuition.
      }
      right.
      apply in_add_3 in Hi; auto.
      apply in_remove_3 in Hi.
      apply spec.
      assumption.
Qed.

Lemma from_wf:
  forall s,
  WF.t [] s ->
  t s.
Proof.
  intros.
  assert (Hy: (forall x, In x [] <-> Map_VAR.In x (Map_VAR.empty nat))). {
    intros.
    simpl.
    rewrite Map_VAR_Facts.empty_in_iff.
    reflexivity.
  }
  assert (Hx := from_wf_ex _ _ H _ Hy).
  rewrite MultiSubst.rw_is_empty in Hx; auto using Map_VAR.empty_1.
Qed.

Lemma wf:
  forall s,
  WF.t [] s ->
  forall tid base M,
  exists h l M2, D.LRun.t tid base M s h M2 l.
Proof.
  intros.
  apply CanRun.from_wf in H.
  apply CanRun.can_run.
  assumption.
Qed.