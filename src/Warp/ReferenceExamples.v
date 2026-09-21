From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal NatUtil.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation Speculation Contract.
From Faial.Warp Require Lang Reference.

Import ListNotations.
Open Scope string_scope.

Example reference_reproduces_single_writer :
  exists last,
  Reference.run zero_input (threads (machine single_writer)) =
    Some (single_writer_reference_trace, last) /\
  finished last /\ participants last = Some [0; 1].
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

(* Running the reference does not itself check memory DRF. *)
Example reference_reproduces_two_writers :
  exists last,
  Reference.run zero_input [program; program] = Some (reference_trace, last) /\
  finished last /\ ~ MemDRF reference_trace.
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|exact litmus_reference_not_memory_drf].
Qed.

Example reference_can_skip_the_collective :
  exists last,
  Reference.run (fun _ => 7) [program; program] =
    Some ([Memory (Observe (av_read 0 0) 7); Memory (Observe (av_read 1 0) 7)], last) /\
  finished last /\ participants last = None /\ load (fun _ => 7) (memory (machine last)) 0 = 7.
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|]. split; reflexivity.
Qed.

Definition partial :=
  Lang.Cond (NRel NEquals NTid (NNum 0)) Lang.AddZero Lang.Skip.

Example reference_resolves_partial_participation :
  exists last,
  Reference.run zero_input [partial; partial; partial] = Some ([Synchronize [0]], last) /\
  finished last /\ participants last = Some [0].
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

Definition all_enter :=
  Lang.Cond (NRel NEquals (NNum 0) (NNum 0)) Lang.AddZero Lang.Skip.

Example reference_handles_a_full_warp :
  exists last,
  Reference.run zero_input (repeat all_enter 32) = Some ([Synchronize (seq 0 32)], last) /\
  finished last /\ participants last = Some (seq 0 32).
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

Example reference_runs_each_thread_to_the_collective :
  let code := Lang.Read (variable "a") NTid
    (Lang.Read (variable "b") NTid all_enter) in
  exists last,
  Reference.run zero_input [code; code] =
    Some ([Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 0 0) 0);
           Memory (Observe (av_read 1 1) 0); Memory (Observe (av_read 1 1) 0);
           Synchronize [0; 1]], last).
Proof. eexists; vm_compute; reflexivity. Qed.

Example reference_agrees_with_another_sso_schedule :
  exists reference_trace reference_last trace last,
  Reference.run zero_input (threads (machine single_writer)) =
    Some (reference_trace, reference_last) /\
  Participation.run SSO zero_input
    [Thread 1; Thread 1; Thread 0; Thread 0; Collective; Thread 0; Thread 0]
    single_writer = Some (trace, last) /\
  finished last /\ same_observations zero_input reference_trace reference_last trace last.
Proof.
  do 4 eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|].
  split; [reflexivity|]. split.
  - intros [|[|tid]]; reflexivity.
  - intros address; reflexivity.
Qed.

Example rejects_empty_programs : Reference.run zero_input [] = None.
Proof. reflexivity. Qed.

Example rejects_missing_branch : Reference.run zero_input [Lang.AddZero] = None.
Proof. reflexivity. Qed.

Example rejects_nested_branches :
  Reference.run zero_input
    [Lang.Cond (NRel NEquals NTid (NNum 0)) all_enter Lang.Skip] = None.
Proof. reflexivity. Qed.

Example rejects_repeated_branches :
  Reference.run zero_input [Lang.Seq all_enter all_enter] = None.
Proof. reflexivity. Qed.

Example rejects_repeated_collectives :
  Reference.run zero_input
    [Lang.Cond (NRel NEquals NTid (NNum 0))
      (Lang.Seq Lang.AddZero Lang.AddZero) Lang.Skip] = None.
Proof. reflexivity. Qed.

Example rejects_collective_in_false_branch :
  Reference.run zero_input
    [Lang.Cond (NRel NEquals NTid (NNum 0)) Lang.AddZero Lang.AddZero] = None.
Proof. reflexivity. Qed.

Example rejects_mixed_barriers :
  Reference.run zero_input [Lang.Seq (Lang.Barrier 0) all_enter] = None.
Proof. reflexivity. Qed.

Example unresolved_expression_is_not_success :
  let programs := [Lang.Cond
    (NRel NEquals (NVar (variable "unbound")) (NNum 0)) Lang.AddZero Lang.Skip] in
  Reference.supported programs = true /\ Reference.run zero_input programs = None.
Proof. split; reflexivity. Qed.

Example read_histories_ignore_cross_thread_order : forall tid,
  read_history tid
    [Memory (Observe (av_read 0 0) 5); Memory (Observe (av_read 1 1) 7)] =
  read_history tid
    [Memory (Observe (av_read 1 1) 7); Memory (Observe (av_read 0 0) 5)].
Proof. intros [|[|tid]]; reflexivity. Qed.

Example equal_final_states_do_not_hide_changed_reads :
  ~ same_observations zero_input
    [Memory (Observe (av_read 0 0) 0)] (initial [Lang.Skip])
    [Memory (Observe (av_read 0 0) 1)] (initial [Lang.Skip]).
Proof.
  intros [_ [Hreads _]]. specialize (Hreads 0). discriminate.
Qed.

Example equal_reads_do_not_hide_changed_groups :
  ~ same_observations zero_input []
    (State (Semantics.initial [Lang.Skip; Lang.Skip]) [Entered; Entered] (Some [0; 1]))
    [] (State (Semantics.initial [Lang.Skip; Lang.Skip]) [Entered; Skipped] (Some [0])).
Proof. intros [Hgroups _]. discriminate. Qed.

Example equal_reads_do_not_hide_changed_memory :
  ~ same_observations zero_input [] (initial [Lang.Skip]) []
    (State (Semantics.State (Map_NAT.add 0 1 Mem.empty) [Lang.Skip]) [Unresolved] None).
Proof.
  intros [_ [_ Hmemory]]. specialize (Hmemory 0). discriminate.
Qed.
