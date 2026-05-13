Require D.Lang.
From Faial.Core Require Import Var.
From Stdlib Require Import Lists.List.
From Faial.Approx Require NExp.
From Faial.Approx Require BExp.
From Faial.Approx Require AExp.
From Faial.Approx Require RExp.
Require Import NatUtil.
Require Trace.
Import ListNotations.
From Faial.Core Require Import Tictac.
Require Import R.Equal.
Require R.Empty.
Require R.Step.
Require R.Closed.
Require D.Subst.

Section Run.
  Section Defs.
  Import NExp.
  Import AExp.
  Import BExp.
  Import RExp.
  Import D.Lang.
  Import Trace.
  
  Variable tid: nat.
  Variable base: nat -> nat.
  Notation history := (list access_val).
  Inductive t : Mem.t -> Lang.t -> history -> Mem.t -> Trace.t -> Prop:=
  | read:
    forall x e_idx n_idx n_val s P M1 M2 l,
    NStep tid e_idx n_idx ->
    Mem.MapsTo.t n_idx n_val M1 base ->
    t M1 (Subst.f x (NNum n_val) s) P M2 l ->
    t M1 (Read x e_idx s) (av_read tid n_idx::P) M2 (seq skip l)
  | write: 
    forall e_idx n_idx e_val n_val M,
    NStep tid e_idx n_idx ->
    NStep tid e_val n_val ->
    t M (Write e_idx e_val) [av_write tid n_idx] (Map_NAT.add n_idx n_val M) skip
  | seq:
    forall s1 s2 P Q M1 M2 M3 l1 l2,
    t M1 s1 P M2 l1 ->
    t M2 s2 Q M3 l2 ->
    t M1 (Seq s1 s2) (P++Q) M3 (seq l1 l2)
  | cond:
    forall e b s1 s2 P1 P2 M M1 M2 l1 l2,
    BStep tid e b ->
    t M s1 P1 M1 l1 ->
    t M s2 P2 M2 l2 ->
    t M (Cond e s1 s2) (if b then P1 else P2) (if b then M1 else M2)
      (if b then (then_branch l1) else (else_branch l2))
  | loop_nil:
    forall x r s M,
    R.Empty.t tid r ->
    t M (Loop x r s) [] M skip
  | loop_cons:
    forall x r n r' s P Q M1 M2 M3 l1 l2,
    R.Step.t tid r n r'->
    t M1 (Subst.f x (NNum n) s) P M2 l1 ->
    t M2 (Loop x r' s) Q M3 l2 ->
    t M1 (Loop x r s) (P++Q) M3 (iter (x, n) l1 l2)
  | skip:
    forall M,
    t M Skip [] M skip
  | decl:
    forall x n s P M1 M2 l,
    t M1 (Subst.f x (NNum n) s) P M2 l ->
    t M1 (Decl x s) P M2 l
  .

  Lemma loop_rw:
    forall m1 x r1 s h m2 l,
    t m1 (Loop x r1 s) h m2 l ->
    forall r2,
    R.Equal.t tid r1 r2 ->
    t m1 (Loop x r2 s) h m2 l.
  Proof.
    intros.
    invc H.
    - constructor.
      eauto using Equal.empty.
    - apply loop_cons with (r':=r') (M2:=M2).
      all: auto.
      eapply Equal.step; eauto.
      apply Equal.refl.
  Qed.

  Lemma subst:
    forall m s h m' l,
    t m s h m' l ->
    forall x n,
    t m (Subst.f x (NNum n) s) h m' l.
  Proof.
    intros m s h m' l H.
    induction H.
    all: intros x_orig n_orig.
    all: simpl.
    - assert (NClosed e_idx). {
        eauto using n_step_to_closed.
      }
      rewrite n_subst_not_free. 2:{ auto. }
      destruct (VAR.eq_dec x_orig x). {
        subst.
        eapply read; eauto using n_step_subst_num.
      }
      specialize (IHt x_orig n_orig).
      apply read with (n_val := n_val); auto.
      rewrite Subst.subst_subst_neq.
      all: auto.
    - constructor.
      all: auto using n_step_subst_num.
    - eapply seq; eauto.
    - constructor.
      all: eauto using b_step_subst_num.
    - assert (rc: R.Closed.t r). {
        eauto using Empty.to_closed.
      }
      rewrite R.Closed.subst. 2:{ assumption. }
      constructor.
      assumption.
    - assert (rc: R.Closed.t r). {
        eauto using R.Step.to_closed_l.
      }
      rewrite R.Closed.subst. 2:{ assumption. }
      destruct (VAR.eq_dec x_orig x). {
        subst.
        econstructor.
        all: eauto.
      }
      specialize (IHt1 x_orig n_orig).
      specialize (IHt2 x_orig n_orig).
      rewrite Subst.subst_subst_neq in IHt1. 2:{ assumption. }
      simpl in IHt2.
      destruct (VAR.eq_dec x_orig x). { contradiction. }
      econstructor.
      all: eauto.
      assert (R.Closed.t r') by eauto using R.Step.to_closed_r.
      rewrite R.Closed.subst in IHt2; auto.
    - constructor.
    - destruct (VAR.eq_dec x_orig x). { econstructor. eauto. }
      specialize (IHt x_orig n_orig).
      rewrite Subst.subst_subst_neq in IHt. 2:{ assumption. }
      econstructor; eauto.
  Qed.
End Defs.

End Run.
