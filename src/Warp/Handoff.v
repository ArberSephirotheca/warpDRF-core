From Stdlib Require Import Lists.List Strings.String.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Warp Require Import Semantics.
From Faial.Warp Require Lang.

Import ListNotations.
Open Scope string_scope.

(* Thread 0 writes, both threads synchronize, then both read the shared value. *)
Definition after_barrier :=
  Lang.Seq (Lang.Barrier 0) (Lang.Read (variable "result") (NNum 0) Lang.Skip).
Definition handoff := initial
  [Lang.Seq (Lang.Write (NNum 0) (NNum 5)) after_barrier; after_barrier].

Definition expected_trace (trace : list observation) : Prop :=
  trace = [Observe (av_write 0 0) 5;
           Observe (av_read 0 0) 5; Observe (av_read 1 0) 5] \/
  trace = [Observe (av_write 0 0) 5;
           Observe (av_read 1 0) 5; Observe (av_read 0 0) 5].

Example handoff_finishes :
  exists trace last,
  run 2 (fun _ => 0)
    [Thread 0; Thread 0; Sync 0; Thread 0; Thread 0; Thread 1; Thread 1]
    handoff = Some (trace, last) /\ finished last /\ expected_trace trace.
Proof.
  eexists; eexists; split; [reflexivity|].
  split; [repeat constructor|left; reflexivity].
Qed.

(* This straight-line example has only seven successful steps. Splitting the
   schedule explores all their interleavings and rejects longer schedules. *)
Local Ltac handoff_cases :=
  lazymatch goal with
  | Hrun : run 2 ?input ?schedule ?s = Some (_, _),
    Hdone : finished _ |- _ =>
      destruct schedule as [|a rest];
      [ cbn [run] in Hrun; inversion Hrun; subst; clear Hrun;
        unfold finished in Hdone; cbn in Hdone;
        repeat match goal with
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H
        end;
        try discriminate;
        solve [split; [left; reflexivity|reflexivity] |
               split; [right; reflexivity|reflexivity]]
      | destruct a as [tid|warp];
        [destruct tid as [|[|tid]] | destruct warp as [|warp]];
        cbn in Hrun;
        rewrite ?nth_error_nil, ?skipn_nil, ?firstn_nil in Hrun;
        cbn in Hrun; try discriminate;
        lazymatch type of Hrun with
        | context [run 2 ?input' ?rest' ?next] =>
            let tail := fresh "tail" in
            let final := fresh "final" in
            let Htail := fresh "Htail" in
            destruct (run 2 input' rest' next) as [[tail final]|] eqn:Htail;
              try discriminate;
            inversion Hrun; subst; clear Hrun;
            rename Htail into Hrun; handoff_cases
        end ]
  end.

Theorem handoff_all_schedules :
  forall input schedule trace last,
  run 2 input schedule handoff = Some (trace, last) ->
  finished last ->
  expected_trace trace /\ load input (memory last) 0 = 5.
Proof.
  intros input schedule trace last Hrun Hdone.
  handoff_cases.
Qed.

Theorem handoff_all_executions :
  forall input trace last,
  execution 2 input handoff trace last ->
  finished last ->
  expected_trace trace /\ load input (memory last) 0 = 5.
Proof.
  intros input trace last Hexec Hdone.
  apply run_complete in Hexec as [schedule Hrun].
  eapply handoff_all_schedules; eauto.
Qed.
