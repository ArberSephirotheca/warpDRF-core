Require U.Lang.
From Faial.Core Require Import Var.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.SetoidList.
From Faial.Approx Require NExp.
From Faial.Approx Require BExp.
From Faial.Approx Require AExp.
From Faial.Approx Require RExp.
From Faial.Core Require Import Tictac.
Require Import NatUtil.
Import ListNotations.
From Faial.Core Require Import InUtil.

Require Trace.
Require N.WellTyped.
Require B.WellTyped.

Require R.WellTyped.
Require R.Step.
Require R.Empty.

Require U.Subst.
Require U.MultiSubst.
Require U.Free.
Require U.Bound.
Require U.WF.

Require EqualModIndex.
Require Import R.Equal.

Section Run.
  Section Defs.
  Import NExp.
  Import AExp.
  Import BExp.
  Import RExp.
  Import U.Lang.
  Import Trace.
  Variable tid : nat.
  Notation history := (list access_val).

  Inductive t : Lang.t -> history -> Trace.t -> Prop :=
  | skip:
    t Skip [] skip
  | access:
    forall e v,
    AStep tid e v ->
    t (MemAcc e) [v] skip
  | seq:
    forall i j h1 h2 l1 l2,
    t i h1 l1 ->
    t j h2 l2 ->
    t (Seq i j) (h1 ++ h2) (seq l1 l2)
  | cond:
    forall i j e b hi hj l1 l2,
    BStep tid e b ->
    t i hi l1 ->
    t j hj l2 ->
    t (If e i j) (if b then hi else hj)
      (if b then (then_branch l1) else (else_branch l2))
  | for_cons:
    forall r r' n i x h1 h2 l1 l2,
    R.Step.t tid r n r' ->
    t (Subst.f x (NNum n) i) h1 l1 ->
    t (For x r' i) h2 l2 ->
    t (For x r i) (h1 ++ h2) (iter (x, n) l1 l2)
  | for_nil:
    forall x i r,
    R.Empty.t tid r ->
    t (For x r i) [] skip
  | decl:
    forall n' i x h l,
    t (Subst.f x (NNum n') i) h l ->
    t (Decl x i) h l
  .

  Lemma seq_eq:
    forall i j h1 h2 h3 l1 l2,
    t i h1 l1 ->
    t j h2 l2 ->
    h3 = h1 ++ h2 ->
    t (Seq i j) h3 (Trace.seq l1 l2).
  Proof.
    intros.
    subst.
    constructor.
    all: assumption.
  Qed.

  Lemma cond_true:
    forall i j e hi hj l1 l2,
    BStep tid e true ->
    t i hi l1 ->
    t j hj l2 ->
    t (If e i j) hi (then_branch l1).
  Proof.
    intros.
    assert (Hx := cond i j e true hi hj l1 l2) .
    simpl in Hx.
    auto.
  Qed.

  Lemma cond_false:
    forall i j e hi hj l1 l2,
    BStep tid e false ->
    t i hi l1 ->
    t j hj l2 ->
    t (If e i j) hj (else_branch l2).
  Proof.
    intros.
    assert (Hx := cond i j e false hi hj l1 l2) .
    simpl in Hx.
    auto.
  Qed.

  Lemma to_loop:
    forall x r u P l,
    t (For x r u) P l ->
    R.Empty.t tid r \/ exists lo hi, Trace.Loop.t l x lo (S hi) /\ R.First.t tid r lo /\ R.Last.t tid r hi.
  Proof.
    intros x r u P l H.
    remember (For _ _ _) as p.
    generalize dependent x.
    generalize dependent r.
    generalize dependent u.
    induction H.
    all: intros u rng loop_v eq1.
    all: invc eq1.
    - clear IHt1.
      rename_hyp (t (For _ _ _) _ _) as hr.
      right.
      exists n.
      assert (IHt2 := IHt2 _ _ _ eq_refl).
      destruct IHt2 as [empty1 | (lo1, (hi, (Hl, (Hf1, Hf2)))) ]. {
        exists n.
        invc hr. {
          contradict empty1.
          eauto using R.Step.to_empty.
        }
        split. {
          apply Loop.skip.
        }
        split. { eauto using R.Step.to_first. }
        eauto using R.Step.to_last.
      }
      exists hi.
      assert (Hx: lo1 = S n /\ l2 <> Trace.skip). {
        rename_hyp (t (For _ _ _) _ _) as hr.
        invc hr.
        2: { invc Hl. }
        invc Hl. {
          rename_hyp (R.Step.t _ rng _ _) as r1.
          rename_hyp (R.Step.t _ r' _ _) as r2.
          apply R.Step.unfold_2 in r1.
          destruct r1 as [r1|r1]. {
            contradict r1.
            eauto using R.Step.to_empty.
          }
          apply R.Step.to_first in r2.
          split. {
            eauto using R.First.func.
          }
          intros N; invc N.
        }
        rename_hyp (t _ _ Trace.skip) as r1.
        invc r1.
        split. {
          eauto using R.Step.inv_step.
        }
        intros N; invc N.
      }
      destruct Hx as (?, ?).
      subst.
      split. {
        apply Loop.next.
        all: auto.
      }
      split. {
        eauto using R.Step.to_first.
      }
      eapply R.Step.to_last_1; eauto.
    - left. assumption.
  Qed.

  Lemma loop_rw:
    forall x r u P l,
    t (For x r u) P l ->
    forall r',
    R.Equal.t tid r r' ->
    t (For x r' u) P l.
  Proof.
    intros.
    invc H.
    - eapply for_cons; eauto.
      eapply R.Equal.step; eauto.
      reflexivity.
    - constructor.
      eauto using Equal.empty.
  Qed.

  Lemma inv_empty:
    forall x r u P l,
    t (For x r u) P l ->
    R.Empty.t tid r ->
    l = Trace.skip.
  Proof.
    intros.
    invc H. {
      contradict H0.
      eauto using R.Step.to_empty.
    }
    reflexivity.
  Qed.

  Lemma loop_inv_eq:
    forall x r1 u1 P1 l,
    t (For x r1 u1) P1 l ->
    forall r2 u2 P2,
    t (For x r2 u2) P2 l ->
    (R.Empty.t tid r1 /\ R.Empty.t tid r2) \/ R.Equal.t tid r1 r2.
  Proof.
    intros.
    rename H into ra.
    rename H0 into rb.
    assert (Ha := ra).
    assert (Hb := rb).
    apply to_loop in Ha.
    apply to_loop in Hb.
    destruct Ha as [Ha|(lo_a, (hi_a, (Ha,(Hfa,Hla))))]. {
      destruct Hb as [Hb|(lo_b, (hi_b, (Hb,(Hfb, Hlb))))]. {
        intuition.
      }
      assert (l = Trace.skip). { eauto using inv_empty. }
      subst.
      invc Hb.
    }
    destruct Hb as [Hb|(lo_b, (hi_b, (Hb,(Hfb, Hlb))))]. {
      assert (l = Trace.skip). { eauto using inv_empty. }
      subst.
      invc Ha.
    }
    right.
    eapply Loop.func in Ha; eauto.
    destruct Ha as (_, (?, eqx)).
    invc eqx.
    eauto using R.Equal.from_first_last.
  Qed.

  Lemma loop_range:
    forall x r1 r2 u1 u2 P1 P2 l,
    t (For x r1 u1) P1 l ->
    t (For x r2 u2) P2 l ->
    t (For x r2 u1) P1 l.
  Proof.
    intros.
    assert (Hx: (R.Empty.t tid r1 /\ R.Empty.t tid r2) \/ R.Equal.t tid r1 r2). {
      eauto using loop_inv_eq.
    }
    destruct Hx as [(Ha,Hb)|Hx]. {
      invc H. {
        contradict Ha.
        eauto using R.Step.to_empty.
      }
      constructor.
      assumption.
    }
    eauto using loop_rw.
  Qed.

  Lemma multi_subst_change:
    forall u m1 P1 l,
    t (MultiSubst.f m1 u) P1 l ->
    forall P2 m2,
    t (MultiSubst.f m2 u) P2 l ->
    eqlistA EqualModIndex.t P1 P2.
  Proof.
    intros u m1 P1 l H.
    remember (MultiSubst.f _ _) as u1.
    generalize dependent u.
    generalize dependent m1.
    induction H.
    all: intros m1 [] eq1 P2 m2 r1.
    all: invc eq1.
    all: simpl in r1.
    all: invc r1.
    - constructor.
    - constructor.
      + apply EqualModIndex.from_step 
        with (tid:=tid) (a1:=A.MultiSubst.f m1 a) (a2:=A.MultiSubst.f m2 a).
        all: auto using A.MultiSubst.eq_mode.
      + constructor.
    - eauto using eqlistA_app, EqualModIndex.Equiv.
    - rename_hyp (_ = _) as e1.
      destruct b, b1.
      all: invc e1.
      all: eauto using eqlistA_app, EqualModIndex.Equiv.
    - assert (R.Closed.t r') by eauto using R.Step.to_closed_r.
      assert (R.Closed.t r'0) by eauto using R.Step.to_closed_r.
      assert (forall e, R.WellTyped.t e r'). { auto using R.WellTyped.from_closed. }
      apply eqlistA_app; eauto using EqualModIndex.Equiv.
      + clear IHt2.
        assert (~ Map_VAR.In v (Map_VAR.remove v m1)). {
          intros N.
          apply Map_VAR.remove_1 in N; auto.
        }
        assert (~ Map_VAR.In v (Map_VAR.remove v m2)). {
          intros N.
          apply Map_VAR.remove_1 in N; auto.
        }
        assert (e1:
          Subst.f v (NNum n) (MultiSubst.f (Map_VAR.remove v m1) t0) =
          MultiSubst.f (Map_VAR.add v n (Map_VAR.remove v m1)) t0
        ). {
          rewrite MultiSubst.subst_to_add; auto.
        }
        rewrite MultiSubst.subst_to_add in *; auto.
        rename_hyp (t _ h0 _) as r1.
        assert (IHt1 := IHt1 _ _ e1 _ _ r1).
        assumption.
      + clear IHt1.
        assert (e1:
          For v r' (MultiSubst.f (Map_VAR.remove v m1) t0) =
          MultiSubst.f (Map_VAR.remove v m1) (For v r' t0)
        ). {
          simpl.
          rewrite R.MultiSubst.rw_closed; auto.
          f_equal.
          apply MultiSubst.subst_eq.
          rewrite rw_remove_remove_eq.
          reflexivity.
        }
        assert (r2: t (MultiSubst.f m2 (For v r' t0)) h3 l2). {
          simpl.
          rewrite R.MultiSubst.rw_closed; auto.
          eauto using loop_range.
        }
        assert (IHt2 := IHt2 _ _ e1 _ _ r2).
        assumption.
    - constructor.
    - assert (n1: ~ Map_VAR.In v (Map_VAR.remove (elt:=nat) v m1)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      assert (n2: ~ Map_VAR.In v (Map_VAR.remove (elt:=nat) v m2)). {
        intros N.
        apply Map_VAR.remove_1 in N; auto.
      }
      rewrite MultiSubst.subst_to_add in *; auto.
      clear n1 n2.
      eapply IHt; eauto.
  Qed.

  Lemma subst_mod_index:
    forall s x n1 P1 l,
    t (Subst.f x (NNum n1) s) P1 l ->
    forall n2 P2,
    t (Subst.f x (NNum n2) s) P2 l ->
    eqlistA EqualModIndex.t P1 P2.
  Proof.
    intros.
    rewrite U.MultiSubst.from_subst in *.
    eauto using multi_subst_change.
  Qed.

  Lemma func_mod_index:
    forall s P1 l,
    t s P1 l ->
    forall P2,
    t s P2 l ->
    eqlistA EqualModIndex.t P1 P2.
  Proof.
    intros s P1 l H.
    induction H.
    all: intros P2 hr.
    all: invc hr.
    - constructor.
    - constructor. 2: { constructor. }
      assert (v0 = v) by eauto using a_step_fun.
      subst.
      reflexivity.
    - apply eqlistA_app; auto.
      apply EqualModIndex.Equiv.
    - rename_hyp (_ = _) as h1.
      destruct b0, b.
      all: invc h1.
      all: eauto.
    - apply eqlistA_app; auto.
      apply EqualModIndex.Equiv.
      apply IHt2.
      eauto using loop_range.
    - constructor.
    - eauto using subst_mod_index.
  Qed.

  Lemma inv_av_owner:
    forall p h l,
    t p h l ->
    forall a,
    List.In a h ->
    tid = av_owner a.
  Proof.
    intros p h l H.
    induction H.
    all: intros a is_in.
    all: simpl in is_in.
    all: intuition.
    - subst.
      symmetry.
      eauto using a_step_inv_tid.
    - apply in_app_or in is_in.
      intuition.
    - destruct b.
      all: eauto.
    - apply in_app_or in is_in.
      intuition.
  Qed.
  End Defs.
End Run.


