Require U.CI.
Require U.DI.
Require U.WF.
From Faial.Approx Require Import Var.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.SetoidList.
Require EqualModIndex.
Require U.LRun.

Section Defs.
  Variable u: U.Lang.t.
  Variable dom: list var.
  Variable wf: U.WF.t dom u.

  (*
   If two runs use the same trace, then their phases are equal up to index.
   *)
  Lemma cd_dd tid:
    forall h1 h2 l,
    LRun.t tid u h1 l ->
    LRun.t tid u h2 l ->
    eqlistA EqualModIndex.t h1 h2.
  Proof.
    intros.
    eapply U.LRun.func_mod_index; eauto.
  Qed.

  (* If we can prove CI, then the traces are deterministic so any
     2 runs will have phases equal up to index, regardless of the trace. *)
  Lemma ci tid:
    forall env,
    List.incl env dom ->
    CI.t env u ->
    forall h1 l1,
    LRun.t tid u h1 l1 ->
    forall h2 l2,
    LRun.t tid u h2 l2 ->
    eqlistA EqualModIndex.t h1 h2.
  Proof.
    intros.
    assert (l1 = l2) by eauto using CI.func.
    subst.
    eapply cd_dd; eauto.
  Qed.

  (* If we can prove DI, then the phases are deterministic for the same trace.
   *)
  Lemma di tid:
    forall env h1 h2 l,
    List.incl env dom ->
    DI.t env u ->
    LRun.t tid u h1 l ->
    LRun.t tid u h2 l ->
    h1 = h2.
  Proof.
    intros.
    eapply DI.func; eauto.
  Qed.

  (* Finally, if we can prove DI and CI, both the phases and the traces
     are deterministic. *)
  Corollary ci_di tid:
    forall env h1 h2 l1 l2,
    List.incl env dom ->
    DI.t env u ->
    CI.t env u ->
    LRun.t tid u h1 l1 ->
    LRun.t tid u h2 l2 ->
    h1 = h2 /\ l1 = l2.
  Proof.
    intros.
    assert (l1 = l2) by eauto using CI.func.
    subst.
    assert (h1 = h2) by eauto using DI.func.
    subst.
    auto.
  Qed.
End Defs.