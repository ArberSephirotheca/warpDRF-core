Require D.CI.
Require D.DI.
Require D.WF.
From Faial.Core Require Import Var.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.SetoidList.
From Faial.Expr Require SIMT.A.EqualModIndex.
Require D.LRun.
Require D.Lang.
Require D.Infer.
Require U.Main.
From Faial.Expr Require Import SIMT.A.Exp.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Faial.Core Require Import Tictac.
Require D.Feasible.
Require D.Spurious.
Require D.Report.
Require U.Report.
Require D.CanRun.
Require Mem.

Import EqualModIndex.

Section Defs.
  Variable s: D.Lang.t.
  Variable dom: list var.
  Variable wf: D.WF.t dom s.


(*  Definition Buggy (s: DLang.t) := exists l1 l2, Bug s l1 l2. *)

  (*
   If two runs use the same trace, then their phases are equal up to index.
   *)
  Lemma cd_dd base tid:
    forall M1 M2 h1 h2 l,
    D.LRun.t tid base M1 s h1 M2 l ->
    U.LRun.t tid (Infer.f s) h2 l ->
    eqlistA EqualModIndex.t h1 h2.
  Proof.
    intros M1 M2 h1 h2 l r1 r2.
    apply Infer.to_run in r1.
    eapply U.Main.cd_dd; eauto.
  Qed.

  (* If we can prove CI, then the traces are deterministic so any
     2 runs will have phases equal up to index, regardless of the trace. *)
  Lemma ci base tid:
    forall env,
    List.incl env dom ->
    CI.t env s ->
    forall M1 M2 h1 l1,
    D.LRun.t tid base M1 s h1 M2 l1 ->
    forall h2 l2,
    U.LRun.t tid (Infer.f s) h2 l2 ->
    eqlistA EqualModIndex.t h1 h2.
  Proof.
    intros.
    assert (l1 = l2) by eauto using CI.func.
    subst.
    eapply cd_dd; eauto.
  Qed.

  (* If we can prove DI, then the phases are deterministic for the same trace.
   *)
  Lemma di base tid:
    forall env M1 M2 h1 h2 l,
    List.incl env dom ->
    DI.t env s ->
    D.LRun.t tid base M1 s h1 M2 l ->
    U.LRun.t tid (Infer.f s) h2 l ->
    h1 = h2.
  Proof.
    intros.
    eapply DI.func in H1; eauto.
  Qed.

  (* Finally, if we can prove DI and CI, both the phases and the traces
     are deterministic. *)
  Theorem ci_di base tid:
    forall env M1 M2 h1 h2 l1 l2,
    List.incl env dom ->
    DI.t env s ->
    CI.t env s ->
    D.LRun.t tid base M1 s h1 M2 l1 ->
    U.LRun.t tid (Infer.f s) h2 l2 ->
    h1 = h2 /\ l1 = l2.
  Proof.
    intros.
    assert (l1 = l2) by eauto using CI.func.
    subst.
    assert (h1 = h2). { eapply DI.func in H2; eauto. }
    subst.
    auto.
  Qed.

  Theorem soundness:
    forall r,
    D.Report.t s r ->
    U.Report.t (Infer.f s) r.
  Proof.
    intros.
    invc H.
    apply Report.def with (tid:=tid) (h:=h).
    all: eauto using Infer.to_run.
  Qed.
End Defs.
Section Props.
  Variable s: D.Lang.t.
  Variable is_wf: D.WF.t [] s.
  Let Hinc:
    List.incl (A:=var) [] [].
  Proof.
    apply List.incl_nil_any.
  Qed.

  Definition EqMod (r1 r2: access_val * Trace.t) : Prop :=
    match r1, r2 with
    | (a1, t1), (a2, t2) => EqualModIndex.t a1 a2 /\ t1 = t2
    end.

  Theorem root_causes:
    forall r,
    D.Spurious.t s r ->
    (~ D.Feasible.t s r) \/ (exists r', D.Report.t s r' /\ EqMod r r').
  Proof.
    intros r spurious.
    invc spurious.
    rename_hyp (U.Report.t _ _) as hr.
    rename_hyp (~ D.Report.t _ _) as hn.
    invc hr.
    rename_hyp (LRun.t _ _ _ _) as hr.
    rename_hyp (In _ _) as hi.
    destruct (D.Feasible.dec s (a, l)) as [Hf | Hf].
    2: { intuition. }
    right.
    invc Hf.
    assert (tid = av_owner a). { eauto using U.LRun.inv_av_owner. }
    subst.
    assert (Hx: exists a', List.In a' h0 /\ EqualModIndex.t a a'). {
      assert (r1: eqlistA EqualModIndex.t h0 h). {
        eapply cd_dd; eauto.
      }
      assert (in1: InA EqualModIndex.t a h0). {
        rewrite r1.
        apply In_InA; auto using EqualModIndex.Equiv.
      }
      apply InA_alt in in1.
      destruct in1 as (a', (?, ?)).
      exists a'.
      intuition.
    }
    destruct Hx as (a', (in1, eq1)).
    exists (a', l).
    split. { econstructor; eauto. }
    unfold EqMod.
    intuition.
  Qed.

  Theorem ci_root_cause:
    D.CI.t [] s ->
    forall r,
    D.Spurious.t s r ->
    exists r', D.Report.t s r' /\ EqMod r r'.
  Proof.
    intros is_ci r hs.
    assert (Hx := hs).
    apply root_causes in hs.
    destruct hs as [hs|hs].
    2:{ assumption. }
    invc Hx.
    rename_hyp (Report.t _ _) as hr.
    invc hr.
    rename_hyp (U.LRun.t _ _ _ _) as hr.
    rename_hyp (In _ _) as in_a.
    destruct (D.CanRun.wf _ is_wf tid (fun x => 0) Mem.empty) as (h', (l', (M1', hr1))).
    assert (e2: eqlistA EqualModIndex.t h' h). {
      eapply ci; eauto.
    }
    assert (l' = l) by eauto using CI.func.
    subst.
    assert (in2: InA EqualModIndex.t a h'). {
      rewrite e2.
      apply In_InA; auto using EqualModIndex.Equiv.
    }
    apply InA_alt in in2.
    destruct in2 as (a', (eq1, in2)).
    exists (a', l).
    split. 2:{ split. all: auto. }
    econstructor; eauto.
  Qed.

  Theorem di_root_cause:
    D.DI.t [] s ->
    forall r,
    D.Spurious.t s r ->
    ~ D.Feasible.t s r.
  Proof.
    intros is_di r hs N.
    invc hs.
    rename_hyp (U.Report.t _ _) as hr.
    invc hr.
    rename_hyp (U.LRun.t _ _ _ _) as hr.
    rename_hyp (~ _ ) as nr.
    rename_hyp (In _ _) as in_a.
    invc N.
    assert (tid = av_owner a) by eauto using U.LRun.inv_av_owner.
    subst.
    assert (h0 = h) by eauto using di.
    subst.
    contradict nr.
    econstructor.
    all: eauto.
  Qed.

  Theorem exactness:
    D.CI.t [] s ->
    D.DI.t [] s ->
    forall r,
    U.Report.t (Infer.f s) r ->
    D.Report.t s r.
  Proof.
    intros is_ci is_di r has_report.
    invc has_report.
    rename_hyp (U.LRun.t _ _ _ _) as hr.
    rename_hyp (In _ _) as in_a.
    destruct (D.CanRun.wf _ is_wf tid (fun x => 0) Mem.empty) as (h', (l', (M1', hr1))).
    assert (Hx: h' = h /\ l' = l). {
      eapply ci_di; eauto.
    }
    destruct Hx as (?,?).
    subst.
    econstructor.
    all: eauto.
  Qed.

  Corollary true_positives:
    D.CI.t [] s ->
    D.DI.t [] s ->
    forall a1 t a2,
    U.Report.t (Infer.f s) (a1, t) ->
    U.Report.t (Infer.f s) (a2, t) ->
    D.Report.t s (a1, t) /\ D.Report.t s (a2, t).
  Proof.
    intros.
    apply exactness in H1; auto.
    apply exactness in H2; auto.
  Qed.
End Props.