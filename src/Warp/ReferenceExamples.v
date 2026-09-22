From Stdlib Require Import Lists.List Strings.String Lia.
From Faial.Core Require Import Var AVal NatUtil.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation Speculation Contract Agreement.
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

(* The communicated value becomes an address, so read agreement must preserve
   the continuation, not merely the final contents of the original location. *)
Definition indexed_handoff v :=
  [Lang.Seq (Lang.Write (NNum 0) (NNum v)) all_enter;
   Lang.Cond (NRel NEquals (NNum 0) (NNum 0))
     (Lang.Seq Lang.AddZero (Lang.Read (variable "dst") (NNum 0)
       (Lang.Write (NVar (variable "dst")) (NNum 9)))) Lang.Skip].

Definition indexed_handoff_trace v :=
  [Memory (Observe (av_write 0 0) v); Synchronize [0; 1];
   Memory (Observe (av_read 1 0) v); Memory (Observe (av_write 1 v) 9)].

Example indexed_handoff_reference : forall input v,
  exists last, Reference.run input (indexed_handoff v) = Some (indexed_handoff_trace v, last) /\
    load input (memory (machine last)) v = 9.
Proof.
  intros input v. eexists; split; [vm_compute; reflexivity|].
  change (load input (Map_NAT.add v 9 (Map_NAT.add 0 v Mem.empty)) v = 9).
  apply load_after_write.
Qed.

Lemma indexed_handoff_memory_drf : forall v, MemDRF (indexed_handoff_trace v).
Proof.
  intros v i j e f He Hf Hconflict.
  assert (Hi : i < 4).
  { apply (proj1 (nth_error_Some (indexed_handoff_trace v) i)).
    rewrite He; discriminate. }
  assert (Hj : j < 4).
  { apply (proj1 (nth_error_Some (indexed_handoff_trace v) j)).
    rewrite Hf; discriminate. }
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; cbn in *; congruence].
  all: first [left; exists 1, [0; 1]; repeat split; cbn; auto; lia |
              right; exists 1, [0; 1]; repeat split; cbn; auto; lia].
Qed.

Theorem indexed_handoff_all_sso : forall input v trace last,
  execution SSO input (initial (indexed_handoff v)) trace last -> finished last ->
  read_history 1 trace = [Observe (av_read 1 0) v] /\
  load input (memory (machine last)) v = 9 /\ MemDRF trace.
Proof.
  intros input v trace last Hexec Hdone.
  destruct (indexed_handoff_reference input v) as [reference_last [Hrun Hvalue]].
  assert (Hconditions : conditions SSO input (initial (indexed_handoff v))
    (indexed_handoff_trace v) (participants reference_last)).
  { split; [apply indexed_handoff_memory_drf|].
    eapply sso_participation_guaranteed; eauto using indexed_handoff_memory_drf. }
  destruct (sso_agreement _ _ _ _ Hrun Hconditions _ _ Hexec Hdone)
    as [_ [Hreads Hmemory]].
  split; [rewrite <- Hreads; reflexivity|]. split.
  - now rewrite <- Hmemory.
  - eapply sso_memory_drf; eauto using indexed_handoff_memory_drf.
Qed.

Example skipped_thread_can_cross_the_collective :
  let programs := [all_enter; all_enter;
    Lang.Seq (Lang.Cond (NRel NEquals (NNum 0) (NNum 1)) Lang.AddZero Lang.Skip)
      (Lang.Write (NNum 2) (NNum 7))] in
  exists reference_last last,
  Reference.run zero_input programs =
    Some ([Memory (Observe (av_write 2 2) 7); Synchronize [0; 1]], reference_last) /\
  Participation.run SSO zero_input
    [Thread 0; Thread 1; Thread 2; Collective; Thread 2; Thread 2]
    (initial programs) =
    Some ([Synchronize [0; 1]; Memory (Observe (av_write 2 2) 7)], last) /\
  finished last /\
  same_observations zero_input
    [Memory (Observe (av_write 2 2) 7); Synchronize [0; 1]] reference_last
    [Synchronize [0; 1]; Memory (Observe (av_write 2 2) 7)] last.
Proof.
  cbn zeta. do 2 eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [split; repeat constructor|].
  repeat split; intros; reflexivity.
Qed.

Example independent_writes_preserve_values_not_map_shape :
  let programs := repeat (Lang.Seq (Lang.Write NTid NTid) all_enter) 4 in
  exists reference_trace reference_last trace last,
  Reference.run zero_input programs = Some (reference_trace, reference_last) /\
  Participation.run SSO zero_input
    [Thread 3; Thread 3; Thread 3; Thread 2; Thread 2; Thread 2;
     Thread 1; Thread 1; Thread 1; Thread 0; Thread 0; Thread 0; Collective]
    (initial programs) = Some (trace, last) /\
  finished last /\
  memory (machine reference_last) <> memory (machine last) /\
  same_observations zero_input reference_trace reference_last trace last.
Proof.
  cbn zeta. do 4 eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [split; repeat constructor|].
  split; [discriminate|]. split; [reflexivity|]. split.
  - intros [|[|[|[|tid]]]]; reflexivity.
  - intros [|[|[|[|address]]]]; reflexivity.
Qed.

Example sso_contract_does_not_transfer_to_spec :
  exists reference_last last,
  Reference.run zero_input (threads (machine single_writer)) =
    Some (single_writer_reference_trace, reference_last) /\
  conditions SSO zero_input single_writer single_writer_reference_trace
    (participants reference_last) /\
  execution Spec zero_input single_writer speculative_trace last /\ finished last /\
  ~ same_observations zero_input single_writer_reference_trace reference_last
      speculative_trace last.
Proof.
  destruct reference_reproduces_single_writer as [reference_last [Hreference [_ Hgroup]]].
  destruct single_writer_spec_validated as [last [Hrun [Hdone [Hspec _]]]].
  exists reference_last, last. split; [exact Hreference|].
  split; [rewrite Hgroup; exact single_writer_sso_conditions|].
  split; [eapply Participation.run_sound; exact Hrun|]. split; [exact Hdone|].
  intros [Heq _]. rewrite Hgroup, Hspec in Heq. discriminate.
Qed.
