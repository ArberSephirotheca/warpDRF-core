From Faial.Approx.D Require Import Lang.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Core Require Import Var.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Tictac.
From Faial.Approx.D Require LRun.
From Faial.Approx.U Require LRun.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Faial.Approx.D Require WF.
From Faial.Approx.U Require WF.
From Faial.Approx.U Require Lang.
From Faial.Approx.U Require Subst.
From Faial.Approx.D Require Subst.

Section Infer.
  Fixpoint f (d:D.Lang.t) : U.Lang.t :=
    match d with
    | D.Lang.Write n m => 
      U.Lang.MemAcc (ae_write n)
    | D.Lang.Read x n d => 
      U.Lang.Seq
        (U.Lang.MemAcc (ae_read n))
        (U.Lang.Decl x (f d))
    | D.Lang.Seq d1 d2 =>
      U.Lang.Seq (f d1) (f d2)
    | D.Lang.Cond b d1 d2 =>
      U.Lang.If b (f d1) (f d2)
    | D.Lang.Loop x r d =>
      U.Lang.For x r (f d)
    | D.Lang.Skip =>
      U.Lang.Skip
    | D.Lang.Decl x d => U.Lang.Decl x (f d)
  end.

  Lemma subst_commute:
    forall x k d,
    f (D.Subst.f x (NNum k) d)
    = U.Subst.f x (NNum k) (f d).
  Proof.
    induction d; simpl in *; intros.
    - destruct (Set_VAR.MF.eq_dec x v).
      + subst.
        rewrite ae_read_subst_commute.
        f_equal.
      + f_equal.
        rewrite IHd.
        reflexivity.
    - unfold ae_write, a_subst.
      reflexivity.
    - rewrite IHd1.
      rewrite IHd2.
      reflexivity.
    - rewrite IHd1.
      rewrite IHd2.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v).
      + reflexivity.
      + rewrite <- IHd.
        reflexivity.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        reflexivity.
      }
      rewrite IHd.
      reflexivity.
  Qed.

Section Soudness.
  Lemma to_run tid base:
    forall M d P M' l,
    D.LRun.t tid base M d P M' l ->
    U.LRun.t tid (f d) P l.
  Proof.
    intros.
    induction H.
    all: simpl in *.
    - apply U.LRun.seq_eq with (h1:=[av_read tid n_idx]) (h2:=P).
      {
        constructor.
        auto using a_step_read.
      }
      {
        rewrite subst_commute in *.
        econstructor.
        eauto.
      }
      { reflexivity. }
    - repeat constructor.
      assumption.
    - eapply LRun.seq_eq; eauto.
    - eapply LRun.cond; auto.
    - apply LRun.for_nil.
      assumption.
    - eapply LRun.for_cons.
      + apply H.
      + rewrite subst_commute in IHt1.
        assumption.
      + assumption.
    - constructor.
    - apply LRun.decl with (n':=n); auto.
      rewrite subst_commute in IHt.
      assumption.
  Qed.

End Soudness.

  Lemma to_wf:
    forall dom s,
    D.WF.t dom s ->
    U.WF.t dom (f s).
  Proof.
    intros dom s H.
    induction H.
    all: simpl.
    all: constructor.
    all: auto.
    - constructor.
      unfold ae_index, ae_read.
      assumption.
    - constructor.
      all: auto.
  Qed.

End Infer.