From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal NatUtil.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation Speculation Contract ReferenceExamples Progress.
From Faial.Warp Require Import DelayedAgreement.
From Faial.Warp Require Lang Reference Delayed DelayedExecution.

Import ListNotations.

Definition execute tid := DelayedExecution.Execute (Thread tid).
Definition synchronize := DelayedExecution.Execute Collective.

Example delayed_indexed_handoff : forall input v,
  exists last,
    DelayedExecution.run input
      [execute 0; execute 0; execute 0; execute 1; synchronize;
       execute 1; execute 1; execute 1; DelayedExecution.PublishFinal]
      (DelayedExecution.initial (indexed_handoff v)) =
        Some (indexed_handoff_trace v, last) /\
    DelayedExecution.finished last /\
    load input (memory (machine (DelayedExecution.control last))) v = 9.
Proof.
  intros input v. eexists. split; [vm_compute; reflexivity|].
  split; [split; [split; repeat constructor|reflexivity]|].
  change (load input (Map_NAT.add v 9 (Map_NAT.add 0 v Mem.empty)) v = 9).
  apply load_after_write.
Qed.

Definition buffering_program :=
  [Lang.Seq (Lang.Write (NNum 0) (NNum 1))
     (Lang.Read (variable "r") (NNum 1) all_enter);
   Lang.Seq (Lang.Write (NNum 1) (NNum 1))
     (Lang.Read (variable "r") (NNum 0) all_enter)].

Definition buffering_trace :=
  [Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 0 1) 0);
   Memory (Observe (av_write 1 1) 1); Memory (Observe (av_read 1 0) 0);
   Synchronize [0; 1]].

Example both_buffered_reads_can_see_zero :
  exists last,
  DelayedExecution.run zero_input
    [execute 0; execute 0; execute 0; execute 0;
     execute 1; execute 1; execute 1; execute 1; synchronize]
    (DelayedExecution.initial buffering_program) = Some (buffering_trace, last) /\
  DelayedExecution.finished last.
Proof.
  eexists. split; [vm_compute; reflexivity|]. split; [split; repeat constructor|reflexivity].
Qed.

Example immediate_reference_reads_differ :
  exists last,
  Reference.run zero_input buffering_program = Some
    ([Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 0 1) 0);
      Memory (Observe (av_write 1 1) 1); Memory (Observe (av_read 1 0) 1);
      Synchronize [0; 1]], last).
Proof. eexists; vm_compute; reflexivity. Qed.

Example buffering_is_not_memory_drf : ~ MemDRF buffering_trace.
Proof.
  eapply conflicting_adjacent_accesses_reject_memory_drf
    with (i := 1) (e := Observe (av_read 0 1) 0) (f := Observe (av_write 1 1) 1).
  - reflexivity.
  - reflexivity.
  - apply conflict_r; cbn; congruence.
Qed.

Definition partial_flush_program :=
  [all_enter; Lang.Seq (Lang.Write (NNum 0) (NNum 7))
    (Lang.Cond (BBool false) Lang.AddZero Lang.Skip)].

Example collective_does_not_publish_an_excluded_writer :
  exists last,
  DelayedExecution.run zero_input
    [execute 0; execute 1; execute 1; execute 1; synchronize]
    (DelayedExecution.initial partial_flush_program) =
      Some ([Memory (Observe (av_write 1 0) 7); Synchronize [0]], last) /\
  Participation.finished (DelayedExecution.control last) /\
  load zero_input (memory (machine (DelayedExecution.control last))) 0 = 0 /\
  DelayedExecution.writes last = [Delayed.Write 1 0 7] /\
  ~ DelayedExecution.finished last.
Proof.
  eexists. split; [vm_compute; reflexivity|]. split; [split; repeat constructor|].
  split; [reflexivity|]. split; [reflexivity|]. intros [_ Hempty]. discriminate.
Qed.

Example cannot_publish_final_memory_before_threads_finish :
  exists next,
  DelayedExecution.advance zero_input (execute 1)
    (DelayedExecution.initial partial_flush_program) =
      Some (Some (Memory (Observe (av_write 1 0) 7)), next) /\
  DelayedExecution.advance zero_input DelayedExecution.PublishFinal next = None.
Proof. eexists; split; reflexivity. Qed.

Example completed_kernel_publishes_remaining_writes :
  exists last,
  DelayedExecution.run zero_input
    [execute 0; execute 1; execute 1; execute 1; synchronize; DelayedExecution.PublishFinal]
    (DelayedExecution.initial partial_flush_program) =
      Some ([Memory (Observe (av_write 1 0) 7); Synchronize [0]], last) /\
  DelayedExecution.finished last /\
  load zero_input (memory (machine (DelayedExecution.control last))) 0 = 7.
Proof.
  eexists. split; [vm_compute; reflexivity|].
  split; [split; [split; repeat constructor|reflexivity]|reflexivity].
Qed.

Example indexed_handoff_has_no_stuck_sso_prefix : forall input v trace last,
  execution SSO input (initial (indexed_handoff v)) trace last ->
  (forall a, advance SSO input a last = None) ->
  finished last /\ read_history 1 trace = [Observe (av_read 1 0) v] /\ MemDRF trace.
Proof.
  intros input v trace last Hexec Hstuck.
  destruct (indexed_handoff_reference input v) as [reference_last [Hrun _]].
  destruct (sso_maximal_agreement _ _ _ _ _ _ Hrun (indexed_handoff_memory_drf v) Hexec Hstuck)
    as [Hdone [[_ [Hreads _]] Hdrf]].
  split; [exact Hdone|]. split; [rewrite <- Hreads; reflexivity|exact Hdrf].
Qed.

Theorem indexed_handoff_all_maximal_delayed_runs : forall input v trace last,
  DelayedExecution.execution input (DelayedExecution.initial (indexed_handoff v)) trace last ->
  (forall a, DelayedExecution.advance input a last = None) ->
  DelayedExecution.finished last /\ read_history 1 trace = [Observe (av_read 1 0) v] /\
  load input (memory (machine (DelayedExecution.control last))) v = 9 /\ MemDRF trace.
Proof.
  intros input v trace last Hexec Hstuck.
  destruct (indexed_handoff_reference input v) as [reference_last [Hrun Hvalue]].
  destruct (delayed_maximal_agreement _ _ _ _ _ _ Hrun (indexed_handoff_memory_drf v) Hexec Hstuck)
    as [Hdone [[_ [Hreads Hmemory]] Hdrf]].
  split; [exact Hdone|]. split; [rewrite <- Hreads; reflexivity|].
  split; [now rewrite <- Hmemory|exact Hdrf].
Qed.
