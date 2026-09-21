From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Approx.D Require Lang.
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

Definition final_value (input : nat -> nat) schedule s address : option nat :=
  match run input schedule s with
  | Some (_, last) => Some (load input (memory last) address)
  | None => None
  end.

Example producer_first :
  final_value zero_input [0; 1; 1] exchange 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example consumer_first :
  final_value zero_input [1; 0; 1] exchange 1 = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example producer_first_trace :
  option_map (@fst (list observation) state)
    (run zero_input [0; 1; 1] exchange) =
  Some [Observe (av_write 0 0) 5;
        Observe (av_read 1 0) 5;
        Observe (av_write 1 1) 5].
Proof. vm_compute. reflexivity. Qed.

Example consumer_first_trace :
  option_map (@fst (list observation) state)
    (run zero_input [1; 0; 1] exchange) =
  Some [Observe (av_read 1 0) 0;
        Observe (av_write 0 0) 5;
        Observe (av_write 1 1) 0].
Proof. vm_compute. reflexivity. Qed.

Example both_schedules_finish :
  (exists trace last,
    run zero_input [0; 1; 1] exchange = Some (trace, last) /\ finished last) /\
  (exists trace last,
    run zero_input [1; 0; 1] exchange = Some (trace, last) /\ finished last).
Proof.
  split; eexists; eexists; split; [reflexivity| |reflexivity|];
    repeat constructor.
Qed.

Example schedules_are_permitted_executions :
  (exists trace last,
    execution zero_input exchange trace last /\
    finished last /\ load zero_input (memory last) 1 = 5) /\
  (exists trace last,
    execution zero_input exchange trace last /\
    finished last /\ load zero_input (memory last) 1 = 0).
Proof.
  split; eexists; eexists; split.
  - apply run_sound with (schedule := [0; 1; 1]). reflexivity.
  - split; [repeat constructor|reflexivity].
  - apply run_sound with (schedule := [1; 0; 1]). reflexivity.
  - split; [repeat constructor|reflexivity].
Qed.

Example reads_own_write :
  final_value zero_input [0; 0; 0; 0]
    (initial [Lang.Seq producer consumer]) 1 = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example reads_initial_memory :
  final_value (fun _ => 42) [0; 0] (initial [consumer]) 1 = Some 42.
Proof. vm_compute. reflexivity. Qed.

Example evaluates_thread_id :
  final_value zero_input [1]
    (initial [Lang.Skip; Lang.Write NTid (NNum 7)]) 1 = Some 7.
Proof. vm_compute. reflexivity. Qed.

Example disjoint_writes :
  let s := initial [Lang.Write (NNum 0) (NNum 5);
                    Lang.Write (NNum 1) (NNum 7)] in
  (final_value zero_input [0; 1] s 0, final_value zero_input [0; 1] s 1) =
  (final_value zero_input [1; 0] s 0, final_value zero_input [1; 0] s 1).
Proof. vm_compute. reflexivity. Qed.

Example invalid_thread_cannot_step :
  advance zero_input 2 exchange = None.
Proof. reflexivity. Qed.

Example finished_thread_cannot_step :
  advance zero_input 0 (initial [Lang.Skip]) = None.
Proof. reflexivity. Qed.

Example unbound_value_cannot_step :
  advance zero_input 0 (initial [Lang.Write (NNum 0) (NVar result_var)]) = None.
Proof. reflexivity. Qed.

Example arbitrary_declarations_are_not_executed :
  advance zero_input 0 (initial [Lang.Decl result_var consumer]) = None.
Proof. reflexivity. Qed.
