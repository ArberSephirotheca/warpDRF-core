From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Warp Require Lang.
From Faial.Warp Require Import Semantics.

Import ListNotations.
Open Scope string_scope.

Definition zero_input (_ : nat) := 0.
Definition result_var := variable "result".

Definition producer := Lang.Write (NNum 0) (NNum 5).
Definition consumer :=
  Lang.Read result_var (NNum 0) (Lang.Write (NNum 1) (NVar result_var)).
Definition exchange := initial [producer; consumer].

Example exchange_has_conflicting_accesses :
  Conflict (av_write 0 0) (av_read 1 0).
Proof.
  apply conflict_l; simpl; congruence.
Qed.

Definition final_value (width : nat) (input : nat -> nat) schedule s address : option nat :=
  match run width input schedule s with
  | Some (_, last) => Some (load input (memory last) address)
  | None => None
  end.

Example producer_first :
  final_value 2 zero_input [Thread 0; Thread 1; Thread 1] exchange 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example consumer_first :
  final_value 2 zero_input [Thread 1; Thread 0; Thread 1] exchange 1 = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example producer_first_trace :
  option_map (@fst (list observation) state)
    (run 2 zero_input [Thread 0; Thread 1; Thread 1] exchange) =
  Some [Observe (av_write 0 0) 5;
        Observe (av_read 1 0) 5;
        Observe (av_write 1 1) 5].
Proof. vm_compute. reflexivity. Qed.

Example consumer_first_trace :
  option_map (@fst (list observation) state)
    (run 2 zero_input [Thread 1; Thread 0; Thread 1] exchange) =
  Some [Observe (av_read 1 0) 0;
        Observe (av_write 0 0) 5;
        Observe (av_write 1 1) 0].
Proof. vm_compute. reflexivity. Qed.

Example both_schedules_finish :
  (exists trace last,
    run 2 zero_input [Thread 0; Thread 1; Thread 1] exchange = Some (trace, last) /\ finished last) /\
  (exists trace last,
    run 2 zero_input [Thread 1; Thread 0; Thread 1] exchange = Some (trace, last) /\ finished last).
Proof.
  split; eexists; eexists; split; [reflexivity| |reflexivity|];
    repeat constructor.
Qed.

Example schedules_are_permitted_executions :
  (exists trace last,
    execution 2 zero_input exchange trace last /\
    finished last /\ load zero_input (memory last) 1 = 5) /\
  (exists trace last,
    execution 2 zero_input exchange trace last /\
    finished last /\ load zero_input (memory last) 1 = 0).
Proof.
  split; eexists; eexists; split.
  - apply run_sound with (schedule := [Thread 0; Thread 1; Thread 1]). reflexivity.
  - split; [repeat constructor|reflexivity].
  - apply run_sound with (schedule := [Thread 1; Thread 0; Thread 1]). reflexivity.
  - split; [repeat constructor|reflexivity].
Qed.

Example reads_own_write :
  final_value 2 zero_input [Thread 0; Thread 0; Thread 0; Thread 0]
    (initial [Lang.Seq producer consumer]) 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example reads_initial_memory :
  final_value 1 (fun _ => 42) [Thread 0; Thread 0] (initial [consumer]) 1 = Some 42.
Proof. vm_compute. reflexivity. Qed.

Example evaluates_thread_id :
  final_value 2 zero_input [Thread 1]
    (initial [Lang.Skip; Lang.Write NTid (NNum 7)]) 1 = Some 7.
Proof. vm_compute. reflexivity. Qed.

Example disjoint_writes :
  let s := initial [Lang.Write (NNum 0) (NNum 5);
                    Lang.Write (NNum 1) (NNum 7)] in
  (final_value 2 zero_input [Thread 0; Thread 1] s 0,
   final_value 2 zero_input [Thread 0; Thread 1] s 1) =
  (final_value 2 zero_input [Thread 1; Thread 0] s 0,
   final_value 2 zero_input [Thread 1; Thread 0] s 1).
Proof. vm_compute. reflexivity. Qed.

Example invalid_thread_cannot_step :
  advance 2 zero_input (Thread 2) exchange = None.
Proof. reflexivity. Qed.

Example finished_thread_cannot_step :
  advance 1 zero_input (Thread 0) (initial [Lang.Skip]) = None.
Proof. reflexivity. Qed.

Example unbound_value_cannot_step :
  advance 1 zero_input (Thread 0) (initial [Lang.Write (NNum 0) (NVar result_var)]) = None.
Proof. reflexivity. Qed.

Example a_thread_cannot_pass_a_barrier_alone :
  advance 2 zero_input (Thread 0) (initial [Lang.Barrier 0; Lang.Barrier 0]) = None.
Proof. reflexivity. Qed.

Example mismatched_barriers_cannot_release :
  synchronize 2 0 (initial [Lang.Barrier 0; Lang.Barrier 1]) = None.
Proof. reflexivity. Qed.

Example incomplete_warp_cannot_release :
  synchronize 2 0 (initial [Lang.Barrier 0]) = None.
Proof. reflexivity. Qed.

Example exited_thread_prevents_release :
  synchronize 2 0 (initial [Lang.Barrier 0; Lang.Skip]) = None.
Proof. reflexivity. Qed.

Example zero_width_cannot_release :
  synchronize 0 0 (initial [Lang.Barrier 0]) = None.
Proof. reflexivity. Qed.

Example missing_warp_cannot_release :
  synchronize 2 1 (initial [Lang.Barrier 0; Lang.Barrier 0]) = None.
Proof. reflexivity. Qed.

Example other_warp_does_not_wait :
  synchronize 2 1
    (initial [producer; Lang.Barrier 0; Lang.Barrier 1; Lang.Barrier 1]) =
  Some (initial [producer; Lang.Barrier 0; Lang.Skip; Lang.Skip]).
Proof. reflexivity. Qed.

Definition repeated_barriers :=
  Lang.Seq (Lang.Barrier 0) (Lang.Barrier 0).

Example release_consumes_only_one_barrier :
  synchronize 2 0 (initial [repeated_barriers; repeated_barriers]) =
  Some (initial [Lang.Seq Lang.Skip (Lang.Barrier 0);
                 Lang.Seq Lang.Skip (Lang.Barrier 0)]).
Proof. reflexivity. Qed.

Example cannot_skip_the_next_barrier :
  run 2 zero_input [Sync 0; Thread 0; Sync 0]
    (initial [repeated_barriers; repeated_barriers]) = None.
Proof. reflexivity. Qed.

Example repeated_barriers_finish :
  run 2 zero_input [Sync 0; Thread 0; Thread 1; Sync 0]
    (initial [repeated_barriers; repeated_barriers]) =
  Some ([], initial [Lang.Skip; Lang.Skip]).
Proof. reflexivity. Qed.

Example read_binding_survives_a_barrier :
  final_value 2 (fun _ => 5) [Thread 0; Sync 0; Thread 0; Thread 0]
    (initial [Lang.Read result_var (NNum 0)
       (Lang.Seq (Lang.Barrier 0) (Lang.Write (NNum 1) (NVar result_var)));
       Lang.Barrier 0]) 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Definition cross_warp := initial
  [Lang.Seq producer (Lang.Barrier 0); Lang.Barrier 0;
   Lang.Seq (Lang.Barrier 0) consumer; Lang.Barrier 0].

Example cross_warp_can_read_old_value :
  final_value 2 zero_input
    [Sync 1; Thread 2; Thread 2; Thread 2; Thread 0; Thread 0; Sync 0]
    cross_warp 1 = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example cross_warp_can_read_new_value :
  final_value 2 zero_input
    [Thread 0; Thread 0; Sync 0; Sync 1; Thread 2; Thread 2; Thread 2]
    cross_warp 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example both_cross_warp_schedules_finish :
  (exists trace last,
    run 2 zero_input
      [Sync 1; Thread 2; Thread 2; Thread 2; Thread 0; Thread 0; Sync 0]
      cross_warp = Some (trace, last) /\ finished last) /\
  (exists trace last,
    run 2 zero_input
      [Thread 0; Thread 0; Sync 0; Sync 1; Thread 2; Thread 2; Thread 2]
      cross_warp = Some (trace, last) /\ finished last).
Proof.
  split; eexists; eexists; split; [reflexivity| |reflexivity|];
    repeat constructor.
Qed.

Example thirty_two_threads_release_together :
  synchronize 32 0 (initial (repeat (Lang.Barrier 0) 32)) =
  Some (initial (repeat Lang.Skip 32)).
Proof. vm_compute. reflexivity. Qed.
