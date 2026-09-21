From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation.
From Faial.Warp Require Lang.

Import ListNotations.
Open Scope string_scope.

(* SIMT-Step's speculate.tex: read x; if (x == 0) { subgroupAdd(0); x = 1; }.
   Here the collective orders memory among its participants in both policies.
   These are SC memory steps, not a claim that ordinary accesses are DRF. *)
Definition cond_var := variable "cond".
Definition body := Lang.Seq Lang.AddZero (Lang.Write (NNum 0) (NNum 1)).
Definition program := Lang.Read cond_var (NNum 0)
  (Lang.Cond (NRel NEquals (NVar cond_var) (NNum 0)) body Lang.Skip).
Definition litmus := initial [program; program].
Definition zero_input (_ : nat) := 0.

Definition reads trace :=
  filter (fun event =>
    match av_mode (access event) with m_read => true | m_write => false end)
    (memory_events trace).

Definition sso_result trace last :=
  (reads trace = [Observe (av_read 0 0) 0; Observe (av_read 1 0) 0] \/
   reads trace = [Observe (av_read 1 0) 0; Observe (av_read 0 0) 0]) /\
  participants last = Some [0; 1] /\ load zero_input (memory (machine last)) 0 = 1.

Example sso_finishes :
  exists trace last,
  run SSO zero_input
    [Thread 0; Thread 0; Thread 1; Thread 1; Collective;
     Thread 0; Thread 0; Thread 1; Thread 1] litmus = Some (trace, last) /\
  finished last /\ sso_result trace last.
Proof.
  eexists; eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|].
  split; [left; reflexivity|split; reflexivity].
Qed.

Example sso_waits_for_unknown_thread :
  run SSO zero_input [Thread 0; Thread 0; Collective] litmus = None.
Proof. reflexivity. Qed.

Example sso_allows_decided_partial_group :
  let code := Lang.Cond (NRel NEquals NTid (NNum 0)) Lang.AddZero Lang.Skip in
  exists trace last,
  run SSO zero_input [Thread 0; Thread 1; Collective] (initial [code; code]) =
    Some (trace, last) /\
  finished last /\ participants last = Some [0] /\ decisions last = [Entered; Skipped].
Proof.
  eexists; eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|split; reflexivity].
Qed.

Example spec_also_allows_the_full_group :
  exists trace last,
  run Spec zero_input
    [Thread 0; Thread 0; Thread 1; Thread 1; Collective;
     Thread 0; Thread 0; Thread 1; Thread 1] litmus = Some (trace, last) /\
  finished last /\ sso_result trace last.
Proof.
  eexists; eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|].
  split; [left; reflexivity|split; reflexivity].
Qed.

(* Exhaust all schedules of this finite two-thread program, not just a bound
   on schedule length. Each successful action consumes an instruction. *)
Local Ltac litmus_cases :=
  lazymatch goal with
  | Hrun : run ?p ?input ?schedule ?s = Some (_, _),
    Hdone : finished _ |- _ =>
      destruct schedule as [|a rest];
      [ cbn [run] in Hrun; inversion Hrun; subst; clear Hrun;
        destruct Hdone as [Hcodes Hdecided];
        unfold Semantics.finished in Hcodes; cbn in Hcodes, Hdecided;
        repeat match goal with
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H
        end;
        try discriminate;
        solve [unfold sso_result;
          split; [first [left; reflexivity | right; reflexivity] | split; reflexivity]]
      | destruct a as [tid|]; [destruct tid as [|[|tid]]|];
        cbn in Hrun; rewrite ?nth_error_nil in Hrun; cbn in Hrun;
        try discriminate;
        lazymatch type of Hrun with
        | context [run ?p' ?input' ?rest' ?next] =>
            let tail := fresh "tail" in
            let final := fresh "final" in
            let Htail := fresh "Htail" in
            destruct (run p' input' rest' next) as [[tail final]|] eqn:Htail;
              try discriminate;
            inversion Hrun; subst; clear Hrun;
            rename Htail into Hrun; litmus_cases
        end ]
  end.

Theorem sso_all_schedules : forall schedule trace last,
  run SSO zero_input schedule litmus = Some (trace, last) ->
  finished last -> sso_result trace last.
Proof.
  intros schedule trace last Hrun Hdone. litmus_cases.
Qed.

Theorem sso_all_executions : forall trace last,
  execution SSO zero_input litmus trace last ->
  finished last -> sso_result trace last.
Proof.
  intros trace last Hexec Hdone.
  apply run_complete in Hexec as [schedule Hrun].
  eapply sso_all_schedules; eauto.
Qed.

Definition speculative_schedule :=
  [Thread 0; Thread 0; Collective; Thread 0; Thread 0; Thread 1; Thread 1].
Definition speculative_trace :=
  [Memory (Observe (av_read 0 0) 0); Synchronize [0];
   Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 1 0) 1)].

Example spec_validated_schedule :
  exists last,
  run Spec zero_input speculative_schedule litmus = Some (speculative_trace, last) /\
  finished last /\ participants last = Some [0] /\
  decisions last = [Entered; Skipped] /\ load zero_input (memory (machine last)) 0 = 1.
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|].
  repeat split; reflexivity.
Qed.

Theorem spec_distinguishes_sso :
  exists last,
  execution Spec zero_input litmus speculative_trace last /\ finished last /\
  participants last = Some [0] /\
  ~ (exists other, execution SSO zero_input litmus speculative_trace other /\ finished other).
Proof.
  destruct spec_validated_schedule as [last [Hrun [Hdone [Hgroup _]]]].
  exists last. split; [eapply run_sound; exact Hrun|].
  split; [exact Hdone|]. split; [exact Hgroup|].
  intros [other [Hexec Hfinished]].
  apply sso_all_executions in Hexec; [|exact Hfinished].
  destruct Hexec as [[Hreads|Hreads] _]; discriminate.
Qed.

Example spec_other_thread_can_be_the_only_participant :
  exists trace last,
  run Spec zero_input
    [Thread 1; Thread 1; Collective; Thread 1; Thread 1; Thread 0; Thread 0]
    litmus = Some (trace, last) /\ finished last /\ participants last = Some [1].
Proof.
  eexists; eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

(* Thread 1 already read zero but has not branched. Predicting its exclusion
   is possible, but cannot become a completed, validated execution. *)
Definition wrong_prediction := State
  (Semantics.initial
    [Lang.Seq Lang.Skip (Lang.Write (NNum 0) (NNum 1));
     Lang.Cond (NRel NEquals (NNum 0) (NNum 0)) body Lang.Skip])
  [Entered; Unresolved] (Some [0]).

Example wrong_prediction_reachable :
  run Spec zero_input [Thread 0; Thread 0; Thread 1; Collective] litmus =
  Some ([Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
         Synchronize [0]], wrong_prediction).
Proof. reflexivity. Qed.

Example wrong_prediction_rejects_branch :
  advance Spec zero_input (Thread 1) wrong_prediction = None.
Proof. reflexivity. Qed.

Theorem wrong_prediction_cannot_finish : forall trace last,
  execution Spec zero_input wrong_prediction trace last -> ~ finished last.
Proof.
  intros trace last Hexec Hdone.
  apply run_complete in Hexec as [schedule Hrun].
  litmus_cases.
Qed.

Example collective_is_not_a_full_warp_barrier :
  at_add_zero (Lang.Barrier 0) = None /\ at_barrier Lang.AddZero = None.
Proof. split; reflexivity. Qed.

Example known_participant_must_arrive :
  advance Spec zero_input Collective
    (State (Semantics.initial [Lang.AddZero; Lang.Seq Lang.Skip Lang.AddZero])
      [Entered; Entered] None) = None.
Proof. reflexivity. Qed.

Example collective_needs_a_participant :
  advance Spec zero_input Collective (initial [Lang.AddZero; Lang.AddZero]) = None.
Proof. reflexivity. Qed.

Example collective_cannot_execute_twice :
  advance Spec zero_input Collective wrong_prediction = None.
Proof. reflexivity. Qed.

(* Keep the original litmus above. This variant removes only thread 1's store,
   leaving a read/write conflict that the reference collective can order. *)
Definition single_writer := initial [program;
  Lang.Read cond_var (NNum 0)
    (Lang.Cond (NRel NEquals (NVar cond_var) (NNum 0)) Lang.AddZero Lang.Skip)].

Theorem single_writer_sso_all_executions : forall trace last,
  execution SSO zero_input single_writer trace last ->
  finished last -> sso_result trace last.
Proof.
  intros trace last Hexec Hdone.
  apply run_complete in Hexec as [schedule Hrun].
  litmus_cases.
Qed.

Example single_writer_spec_validated :
  exists last,
  run Spec zero_input speculative_schedule single_writer = Some (speculative_trace, last) /\
  finished last /\ participants last = Some [0] /\
  decisions last = [Entered; Skipped] /\ load zero_input (memory (machine last)) 0 = 1.
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|].
  repeat split; reflexivity.
Qed.
