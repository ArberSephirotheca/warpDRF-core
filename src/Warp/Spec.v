From Stdlib Require Import Lists.List Strings.String Bool.Bool Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Agree Delayed.

Import ListNotations.
Open Scope string_scope.

(* Spec is SIMT-Step's speculative target. SSO fires a collective only when
   no thread may still run it. Spec waits only for the threads known to run
   it, those whose every path reaches it. It does not wait for a thread that
   may still take a branch away from the collective, SIMT-Step's unknown
   threads; it bets that such a thread will not come. SIMT-Step discards a run
   in which an unknown thread joins the collective's dynamic block after the
   firing. We approximate this by letting Spec fire each instance at most
   once: a thread that joins late waits at the collective forever, so the run
   never completes. Thread steps and memory are those of the SSO target with
   delayed visibility (Delayed.v): a write stays pending until its thread
   takes part in a primitive that orders memory, and a race aborts the run.

   Spec conforms to neither configuration: on a kernel that is WarpDRF for
   both, which threads join a collective depends on the schedule, even in
   completed runs. *)

(* A Break or Continue that leaves the innermost loop around the code. *)
Fixpoint has_jump (c : code) : bool :=
  match c with
  | Break | Continue => true
  | Read _ _ body | Prim _ _ _ _ _ _ body | Wait _ _ _ _ _ _ body | Local _ _ _ body =>
      has_jump body
  | Seq first rest | Cond _ first rest => has_jump first || has_jump rest
  | _ => false
  end.

(* A Return anywhere in the code, which ends the thread. *)
Fixpoint can_return (c : code) : bool :=
  match c with
  | Return => true
  | Read _ _ body | Loop body | Prim _ _ _ _ _ _ body | Wait _ _ _ _ _ _ body
  | Local _ _ _ body => can_return body
  | Seq first rest | Cond _ first rest => can_return first || can_return rest
  | Iter _ rest body => can_return rest || can_return body
  | _ => false
  end.

(* A thread must reach an instance when every path of its remaining code runs
   it: a conditional must reach it in both branches, and the code after a part
   is reached only if that part can neither jump out nor return. The threads
   that must reach a collective are the ones SIMT-Step knows to be in its
   dynamic block. *)
Fixpoint must_reach (c : code) (s : site) (v : list nat) : bool :=
  match c with
  | Read _ _ body | Local _ _ _ body => must_reach body s v
  | Seq first rest =>
      must_reach first s v ||
      (negb (has_jump first) && negb (can_return first) && must_reach rest s v)
  | Cond _ yes no => must_reach yes s v && must_reach no s v
  | Loop body => match v with 0 :: v' => must_reach body s v' | _ => false end
  | Iter k rest body =>
      match v with j :: v' => Nat.eqb j k && must_reach rest s v' | [] => false end
  | Prim n sync full _ _ _ body | Wait n sync full _ _ _ body =>
      (site_eqb s (Site n sync full) && is_nil v) || must_reach body s v
  | Write _ _ | Break | Continue | Skip | Return => false
  end.

(* Threads known to run an instance that have not arrived at it. *)
Definition absent (i : instance) (codes : list code) :=
  select (fun c => must_reach c (fst i) (snd i) && negb (waits_at i c)) codes.

Record spec_state := SpecState {
  base : dstate;
  released : list instance;
}.

Definition spec_initial (programs : list code) := SpecState (dinitial programs) [].

Definition spec_advance input (a : action) (s : spec_state)
    : option (option event * spec_state) :=
  match a with
  | Thread _ =>
      match dadvance input a (base s) with
      | Some (e, d') => Some (e, SpecState d' (released s))
      | None => None
      end
  | Release i =>
      if existsb (instance_eqb i) (released s) then None else
      match arrived i (dcodes (base s)), absent i (dcodes (base s)) with
      | (_ :: _) as group, [] =>
          Some (Some (Sync i group), SpecState (drelease i group (base s)) (i :: released s))
      | _, _ => None
      end
  end.

Inductive spec_execution input : spec_state -> list event -> spec_state -> Prop :=
| spec_refl : forall s, spec_execution input s [] s
| spec_step : forall a s e s' trace last,
    spec_advance input a s = Some (e, s') ->
    spec_execution input s' trace last ->
    spec_execution input s (emit_event e trace) last.

(* Run a schedule; fails if an action is not enabled. *)
Fixpoint spec_run input (schedule : list action) (s : spec_state)
    : option (list event * spec_state) :=
  match schedule with
  | [] => Some ([], s)
  | a :: rest =>
      match spec_advance input a s with
      | Some (e, s') =>
          match spec_run input rest s' with
          | Some (trace, last) => Some (emit_event e trace, last)
          | None => None
          end
      | None => None
      end
  end.

Lemma spec_run_sound : forall input schedule s trace last,
  spec_run input schedule s = Some (trace, last) -> spec_execution input s trace last.
Proof.
  intros input schedule. induction schedule as [|a rest IH]; intros s trace last Hrun;
    cbn in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (spec_advance input a s) as [[e s']|] eqn:Hstep; try discriminate.
    destruct (spec_run input rest s') as [[tail final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. econstructor; [exact Hstep|]. now apply IH.
Qed.

(* The Spec target: its runs, each observed with every pending write
   published. As for the delayed target, a run whose trace has a race aborts. *)
Definition spec_final (s : spec_state) := State (logical (base s)) (dcodes (base s)).

Definition spec_target input programs trace last :=
  exists s, spec_execution input (spec_initial programs) trace s /\ last = spec_final s.

(* single_writer: both threads read a flag and, when it is zero, meet at
   AddZero; afterwards thread 0 sets the flag. *)

Definition zero_input (_ : nat) := 0.
Definition flag := variable "flag".

Definition single_writer :=
  Read flag (NNum 0)
    (Cond (NRel NEquals (NVar flag) (NNum 0))
      (Seq (AddZero 0)
        (Cond (NRel NEquals NTid (NNum 0)) (Write (NNum 0) (NNum 1)) Skip))
      Skip).

Definition single_writer_reference_trace :=
  [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
   Sync (AddSite 0, []) [0; 1]; Memory (Observe (av_write 0 0) 1)].

Ltac hb_link t :=
  split; [lia|]; do 2 eexists; exists t;
  split; [reflexivity|]; split; [reflexivity|]; cbn; split; auto.

(* The reference orders thread 1's read before thread 0's write through the
   collective, which both threads join. *)
Theorem single_writer_memory_drf : MemDRF single_writer_reference_trace.
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace i)). rewrite He.
    discriminate. }
  assert (Hj : j < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace j)). rewrite Hf.
    discriminate. }
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; cbn in *; congruence].
  - left. apply t_trans with 2; apply t_step; [hb_link 1|hb_link 0].
  - right. apply t_trans with 2; apply t_step; [hb_link 1|hb_link 0].
Qed.

(* Under Spec thread 1 may arrive in time: both threads wait when the
   collective fires, and the run has the reference's trace and final
   memory. *)
Definition on_time_schedule :=
  [Thread 0; Thread 0; Thread 0; Thread 1; Thread 1; Thread 1; Release (AddSite 0, []);
   Thread 0; Thread 0; Thread 0; Thread 0; Thread 1; Thread 1; Thread 1].

Example single_writer_on_time :
  exists reference_last s,
  run 100 zero_input [single_writer; single_writer] =
    Some (single_writer_reference_trace, reference_last) /\
  spec_run zero_input on_time_schedule (spec_initial [single_writer; single_writer]) =
    Some (single_writer_reference_trace, s) /\
  finished (spec_final s) /\
  forall a, load zero_input (memory reference_last) a =
    load zero_input (memory (spec_final s)) a.
Proof.
  eexists _, _. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [cbn; unfold finished; repeat constructor|].
  intros a. vm_compute. reflexivity.
Qed.

(* Or thread 0 fires the collective alone while thread 1, which has not yet
   taken the branch, is unknown, and then writes 1. The write stays pending,
   so thread 1 reads 0: its read races with the write, and the run aborts, as
   in GPUVerify. The run ends before thread 1 reaches the collective, so the
   bet is never contradicted. *)
Definition early_schedule :=
  [Thread 0; Thread 0; Thread 0; Release (AddSite 0, []);
   Thread 0; Thread 0; Thread 0; Thread 0; Thread 1].

Definition early_trace :=
  [Memory (Observe (av_read 0 0) 0); Sync (AddSite 0, []) [0];
   Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 1 0) 0)].

Example single_writer_early :
  exists s,
  spec_run zero_input early_schedule (spec_initial [single_writer; single_writer]) =
    Some (early_trace, s).
Proof. eexists. vm_compute. reflexivity. Qed.

(* Thread 0's write and thread 1's read are adjacent and unordered. *)
Lemma early_trace_race : ~ MemDRF early_trace.
Proof.
  apply (adjacent_conflict_not_drf early_trace 2
    (Observe (av_write 0 0) 1) (Observe (av_read 1 0) 0)); [reflexivity|reflexivity|].
  apply conflict_l; cbn; [discriminate|reflexivity|reflexivity].
Qed.

(* In the reference both threads join the collective, so single_writer is
   WarpDRF for either configuration. *)
Lemma single_writer_full_warp :
  UnambiguousParticipation FullWarp [single_writer; single_writer]
    single_writer_reference_trace.
Proof.
  intros i group Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|[Heq|[Heq|[]]]]]; inversion Heq; subst.
  split; [discriminate|]. split; [repeat constructor; cbn; intuition discriminate|].
  split; [|reflexivity].
  apply Forall_forall. intros tid [<-|[<-|[]]]; cbn; lia.
Qed.

Lemma single_writer_conditions : forall c fuel reference_last,
  run fuel zero_input [single_writer; single_writer] =
    Some (single_writer_reference_trace, reference_last) ->
  conditions c [single_writer; single_writer] single_writer_reference_trace.
Proof.
  intros c fuel reference_last Hrun. split; [exact single_writer_memory_drf|].
  destruct c; [exact single_writer_full_warp|].
  apply (reference_structured_partial _ _ _ _ _ Hrun).
  intros i group Hin _. apply (single_writer_full_warp i group Hin).
Qed.

(* single_writer is WarpDRF for either configuration, yet under Spec the group
   of its collective is not fixed: the reference and a finished Spec run form
   [0; 1] and agree, while another Spec run forms [0] and races, which aborts
   it. *)
Theorem spec_grouping_depends_on_schedule : forall c,
  exists programs fuel input reference_trace reference_last,
    run fuel input programs = Some (reference_trace, reference_last) /\
    conditions c programs reference_trace /\
    groups_at (AddSite 0, []) reference_trace = [[0; 1]] /\
    (exists trace last, spec_target input programs trace last /\ finished last /\
       groups_at (AddSite 0, []) trace = [[0; 1]] /\
       same_observations input reference_trace reference_last trace last) /\
    (exists trace last, spec_target input programs trace last /\
       groups_at (AddSite 0, []) trace = [[0]] /\ ~ MemDRF trace).
Proof.
  intros c.
  destruct single_writer_on_time
    as [reference_last [s_on [Hrun [Hon_time [Hon_done Hmemory]]]]].
  destruct single_writer_early as [s_early Hearly].
  exists [single_writer; single_writer], 100, zero_input, single_writer_reference_trace,
    reference_last.
  split; [exact Hrun|].
  split; [exact (single_writer_conditions c _ _ Hrun)|].
  split; [reflexivity|].
  split.
  - exists single_writer_reference_trace, (spec_final s_on). split.
    { exists s_on. split; [exact (spec_run_sound _ _ _ _ _ Hon_time)|reflexivity]. }
    split; [exact Hon_done|]. split; [reflexivity|].
    split; [intros; reflexivity|]. split; [intros; reflexivity|exact Hmemory].
  - exists early_trace, (spec_final s_early). split.
    { exists s_early. split; [exact (spec_run_sound _ _ _ _ _ Hearly)|reflexivity]. }
    split; [reflexivity|exact early_trace_race].
Qed.

(* So the guarantee that delayed_agreement proves for SSO with delayed
   visibility does not hold for Spec with the same memory, in either
   configuration. *)
Corollary warpdrf_fails_under_spec : forall c, ~ Guarantee c spec_target.
Proof.
  intros c Hagree.
  destruct (spec_grouping_depends_on_schedule c)
    as [programs [fuel [input [reference_trace [reference_last
      [Hrun [Hconditions [_ [_ [trace [last [Htarget [_ Hrace]]]]]]]]]]]]].
  exact (Hrace (proj1 (Hagree _ _ _ _ _ Hrun Hconditions _ _ Htarget))).
Qed.

(* Spec still waits for a thread known to run the collective. In late, each
   thread writes its own cell and then calls AddZero, with no branch between:
   Spec cannot fire the collective with thread 0 alone. *)
Definition late := Seq (Write NTid (NNum 1)) (AddZero 0).

Example late_waits :
  spec_run zero_input [Thread 0; Thread 0; Thread 0; Release (AddSite 0, [])]
    (spec_initial [late; late]) = None.
Proof. vm_compute. reflexivity. Qed.
