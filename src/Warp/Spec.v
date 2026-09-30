From Stdlib Require Import Lists.List Strings.String Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Agree.

Import ListNotations.
Open Scope string_scope.

(* Spec, SIMT-Step's speculative target, fires a collective as soon as some
   thread waits at it, with whichever threads have arrived, like
   __activemask(). It does not wait for the unknown set to empty. Each
   instance fires at most once, so a thread that arrives after the firing
   waits forever: a run whose speculation fails never completes. Thread steps
   are the SSO thread steps.

   Spec does not conform to the structured partial configuration: on a kernel
   that is WarpDRF for it, which threads join a collective depends on the
   schedule, even in completed runs. Once unfinished runs count, it conforms
   to neither configuration. *)

Record spec_state := SpecState {
  base : state;
  released : list instance;
}.

Definition spec_initial (programs : list code) := SpecState (initial programs) [].

Definition spec_advance input (a : action) (s : spec_state)
    : option (option event * spec_state) :=
  match a with
  | Thread _ =>
      match advance input a (base s) with
      | Some (e, st') => Some (e, SpecState st' (released s))
      | None => None
      end
  | Release i =>
      if existsb (instance_eqb i) (released s) then None else
      match arrived i (threads (base s)) with
      | [] => None
      | group =>
          Some (Some (Sync i group),
            SpecState (State (memory (base s)) (release i (threads (base s))))
              (i :: released s))
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

(* single_writer: both threads read a flag and, when it is zero, meet at
   AddZero; afterwards thread 0 sets the flag. *)

Definition zero_input (_ : nat) := 0.
Definition flag := variable "flag".

Definition single_writer :=
  Read flag (NNum 0)
    (Cond (NRel NEquals (NVar flag) (NNum 0))
      (Seq AddZero
        (Cond (NRel NEquals NTid (NNum 0)) (Write (NNum 0) (NNum 1)) Skip))
      Skip).

Definition single_writer_reference_trace :=
  [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
   Sync (AddSite, []) [0; 1]; Memory (Observe (av_write 0 0) 1)].

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
   collective fires, and the run is the reference run. *)
Definition on_time_schedule :=
  [Thread 0; Thread 0; Thread 1; Thread 1; Release (AddSite, []);
   Thread 0; Thread 0; Thread 0; Thread 1; Thread 1].

Example single_writer_on_time :
  exists last,
  run 100 zero_input [single_writer; single_writer] =
    Some (single_writer_reference_trace, last) /\
  spec_run zero_input on_time_schedule (spec_initial [single_writer; single_writer]) =
    Some (single_writer_reference_trace, SpecState last [(AddSite, [])]) /\
  finished last.
Proof.
  eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|unfold finished; repeat constructor].
Qed.

(* Or thread 0 fires the collective alone and sets the flag; thread 1 then
   reads 1 and skips the collective. *)
Definition early_schedule :=
  [Thread 0; Thread 0; Release (AddSite, []); Thread 0; Thread 0; Thread 0;
   Thread 1; Thread 1].

Definition early_trace :=
  [Memory (Observe (av_read 0 0) 0); Sync (AddSite, []) [0];
   Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 1 0) 1)].

Example single_writer_early :
  exists last,
  spec_run zero_input early_schedule (spec_initial [single_writer; single_writer]) =
    Some (early_trace, last) /\ finished (base last).
Proof. eexists; split; [vm_compute; reflexivity|unfold finished; repeat constructor]. Qed.

(* single_writer is WarpDRF for the structured partial configuration, yet
   under Spec the group of its collective is not fixed: the reference and one
   completed Spec run form [0; 1], and another completed Spec run forms [0]
   and disagrees with the reference. *)
Theorem spec_grouping_depends_on_schedule :
  exists programs fuel input reference_trace reference_last,
    run fuel input programs = Some (reference_trace, reference_last) /\
    conditions StructuredPartial programs reference_trace /\
    groups_at (AddSite, []) reference_trace = [[0; 1]] /\
    (exists trace last,
       spec_execution input (spec_initial programs) trace last /\ finished (base last) /\
       groups_at (AddSite, []) trace = [[0; 1]] /\
       same_observations input reference_trace reference_last trace (base last)) /\
    (exists trace last,
       spec_execution input (spec_initial programs) trace last /\ finished (base last) /\
       groups_at (AddSite, []) trace = [[0]] /\
       ~ same_observations input reference_trace reference_last trace (base last)).
Proof.
  destruct single_writer_on_time as [reference_last [Hrun [Hon_time Hdone]]].
  destruct single_writer_early as [last [Hearly Hearly_done]].
  exists [single_writer; single_writer], 100, zero_input, single_writer_reference_trace,
    reference_last.
  split; [exact Hrun|].
  split; [split; [exact single_writer_memory_drf
                 |exact (reference_structured_partial _ _ _ _ _ Hrun)]|].
  split; [reflexivity|].
  split.
  - exists single_writer_reference_trace, (SpecState reference_last [(AddSite, [])]).
    split; [exact (spec_run_sound _ _ _ _ _ Hon_time)|]. split; [exact Hdone|].
    split; [reflexivity|].
    unfold same_observations. repeat split; intros; reflexivity.
  - exists early_trace, last.
    split; [exact (spec_run_sound _ _ _ _ _ Hearly)|]. split; [exact Hearly_done|].
    split; [reflexivity|].
    intros [Hgroups _]. specialize (Hgroups (AddSite, [])).
    vm_compute in Hgroups. discriminate.
Qed.

(* So WarpDRF's guarantee fails under Spec: sso_agreement for the structured
   partial configuration, with Spec executions in place of SSO executions, is
   false. *)
Corollary warpdrf_fails_under_spec :
  ~ (forall programs fuel input reference_trace reference_last,
       run fuel input programs = Some (reference_trace, reference_last) ->
       conditions StructuredPartial programs reference_trace ->
       forall trace last,
       spec_execution input (spec_initial programs) trace last -> finished (base last) ->
       same_observations input reference_trace reference_last trace (base last)).
Proof.
  intros Hagree.
  destruct spec_grouping_depends_on_schedule
    as [programs [fuel [input [reference_trace [reference_last
      [Hrun [Hconditions [_ [_ [trace [last [Hexec [Hdone [_ Hdiffer]]]]]]]]]]]]]].
  exact (Hdiffer (Hagree _ _ _ _ _ Hrun Hconditions _ _ Hexec Hdone)).
Qed.

(* The guarantee for every run, finished or not, fails under Spec in both
   configurations. In late, each thread writes its own cell and then calls
   AddZero, in uniform code: the kernel is WarpDRF for either configuration.
   Spec can fire the collective with thread 0 alone, so a run forms a group
   the reference never forms. Thread 1 then arrives after the firing, and the
   run never completes. *)
Definition late := Seq (Write NTid (NNum 1)) AddZero.

Definition late_reference_trace :=
  [Memory (Observe (av_write 0 0) 1); Memory (Observe (av_write 1 1) 1);
   Sync (AddSite, []) [0; 1]].

Example late_reference :
  exists last, run 100 zero_input [late; late] = Some (late_reference_trace, last).
Proof. eexists; vm_compute; reflexivity. Qed.

Lemma late_memory_drf : MemDRF late_reference_trace.
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 3).
  { apply (proj1 (nth_error_Some late_reference_trace i)). rewrite He. discriminate. }
  assert (Hj : j < 3).
  { apply (proj1 (nth_error_Some late_reference_trace j)). rewrite Hf. discriminate. }
  destruct i as [|[|[|i]]], j as [|[|[|j]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    inversion Hconflict; cbn in *; congruence.
Qed.

Lemma late_full_warp :
  UnambiguousParticipation FullWarp [late; late] late_reference_trace.
Proof.
  unfold UnambiguousParticipation, PermittedPlacement, warp_uniform. split.
  - exists late. split; [reflexivity|]. split; [reflexivity|repeat constructor].
  - intros i group Hin. cbn in Hin.
    destruct Hin as [Heq|[Heq|[Heq|[]]]]; inversion Heq; subst.
    split; [discriminate|]. split; [repeat constructor; cbn; intuition discriminate|].
    split; [|reflexivity].
    apply Forall_forall. intros tid [<-|[<-|[]]]; cbn; lia.
Qed.

Example late_early :
  exists s,
  spec_run zero_input [Thread 0; Thread 0; Release (AddSite, [])]
    (spec_initial [late; late]) =
    Some ([Memory (Observe (av_write 0 0) 1); Sync (AddSite, []) [0]], s).
Proof. eexists; vm_compute; reflexivity. Qed.

Theorem warpdrf_fails_under_spec_every_run : forall c,
  ~ (forall programs fuel input reference_trace reference_last,
       run fuel input programs = Some (reference_trace, reference_last) ->
       conditions c programs reference_trace ->
       forall trace last,
       spec_execution input (spec_initial programs) trace last ->
       observations_so_far reference_trace trace).
Proof.
  intros c Hagree.
  destruct late_reference as [reference_last Hrun].
  destruct late_early as [s Hspec].
  assert (Hconditions : conditions c [late; late] late_reference_trace).
  { split; [exact late_memory_drf|].
    destruct c; [exact late_full_warp|exact (reference_structured_partial _ _ _ _ _ Hrun)]. }
  destruct (Hagree _ _ _ _ _ Hrun Hconditions _ _ (spec_run_sound _ _ _ _ _ Hspec))
    as [Hgroups _].
  destruct (Hgroups (AddSite, [])) as [more Hmore].
  vm_compute in Hmore. discriminate.
Qed.
