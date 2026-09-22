From Stdlib Require Import Lists.List Bool.Bool Lia.
From Faial.Core Require Import AVal.
From Faial.Core Require Hist.
From Faial.Warp Require Import Semantics Participation Speculation.
From Faial.Warp Require Reference.

Import ListNotations.

(* With at most one collective, cross-thread happens-before requires that
   collective between the accesses and both owners in its participant group.
   Program order alone cannot order a conflicting pair from distinct threads. *)
Definition collective_orders (trace : list event) (i j t u : nat) :=
  exists k group,
  nth_error trace k = Some (Synchronize group) /\
  i < k /\ k < j /\ In t group /\ In u group.

Definition MemDRF (trace : list event) :=
  forall i j e f,
  nth_error trace i = Some (Memory e) ->
  nth_error trace j = Some (Memory f) ->
  Conflict (access e) (access f) ->
  collective_orders trace i j (av_owner (access e)) (av_owner (access f)) \/
  collective_orders trace j i (av_owner (access f)) (av_owner (access e)).

(* One collective at most, with thread identifiers recorded in ascending order.
   The guarantee concerns all completed executions, not one selected schedule. *)
Definition ParticipationGuaranteed p input start expected :=
  forall trace last,
  execution p input start trace last -> finished last ->
  participants last = expected.

(* Apply to observations of a reference execution, established separately.
   This is the bounded, single-collective fragment of the two conditions. *)
Definition conditions p input start reference_trace reference_group :=
  MemDRF reference_trace /\
  ParticipationGuaranteed p input start reference_group.

Definition read_history tid trace :=
  filter (fun e => Nat.eqb (av_owner (access e)) tid &&
    match av_mode (access e) with m_read => true | m_write => false end)
    (memory_events trace).

Definition same_observations input reference_trace reference_last trace last :=
  participants reference_last = participants last /\
  (forall tid, read_history tid reference_trace = read_history tid trace) /\
  (forall address,
    load input (memory (machine reference_last)) address =
    load input (memory (machine last)) address).

(* Agreement.sso_agreement proves this contract for the bounded SSO semantics. *)
Definition SSOAgreement : Prop :=
  forall programs input reference_trace reference_last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  conditions SSO input (initial programs) reference_trace (participants reference_last) ->
  forall trace last,
  execution SSO input (initial programs) trace last -> finished last ->
  same_observations input reference_trace reference_last trace last.

Lemma collective_orders_forward : forall trace i j t u,
  collective_orders trace i j t u -> i < j.
Proof.
  intros trace i j t u [k [group [_ [Hbefore [Hafter _]]]]]. lia.
Qed.

Lemma conflicting_adjacent_accesses_reject_memory_drf : forall trace i e f,
  nth_error trace i = Some (Memory e) ->
  nth_error trace (S i) = Some (Memory f) ->
  Conflict (access e) (access f) -> ~ MemDRF trace.
Proof.
  intros trace i e f He Hf Hconflict Hsafe.
  destruct (Hsafe i (S i) e f He Hf Hconflict) as [Horder|Horder].
  - destruct Horder as [k [group [_ [Hbefore [Hafter _]]]]]. lia.
  - apply collective_orders_forward in Horder. lia.
Qed.

Lemma memory_event_in : forall trace e,
  In (Memory e) trace -> In e (memory_events trace).
Proof.
  induction trace as [|first rest IH]; intros e Hin; [contradiction|].
  destruct first as [f|group]; cbn in *.
  - destruct Hin as [Heq|Hin]; [inversion Heq; subst; auto|auto].
  - destruct Hin as [Heq|Hin]; [discriminate|auto].
Qed.

Lemma safe_history_memory_drf : forall trace,
  Hist.Safe (map access (memory_events trace)) -> MemDRF trace.
Proof.
  intros trace Hsafe i j e f He Hf Hconflict.
  apply nth_error_In, memory_event_in in He, Hf.
  exfalso. eapply safe_conflict_absurd with (a1 := access e) (a2 := access f).
  - apply Hsafe; apply in_map; assumption.
  - exact Hconflict.
Qed.

(* A concrete reference run of this litmus: thread 0 to the collective,
   thread 1 to the collective, then thread 0 and thread 1 to completion.
   This witnesses the paper's scheduling discipline for this example only. *)
Definition reference_trace :=
  [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
   Synchronize [0; 1];
   Memory (Observe (av_write 0 0) 1); Memory (Observe (av_write 1 0) 1)].

Example litmus_reference_runs :
  exists last,
  run SSO zero_input
    [Thread 0; Thread 0; Thread 1; Thread 1; Collective;
     Thread 0; Thread 0; Thread 1; Thread 1] litmus = Some (reference_trace, last) /\
  finished last /\ participants last = Some [0; 1].
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

Theorem litmus_reference_execution :
  exists last, execution SSO zero_input litmus reference_trace last /\
  finished last /\ participants last = Some [0; 1].
Proof.
  destruct litmus_reference_runs as [last [Hrun Hdone]].
  exists last. split; [eapply run_sound; exact Hrun|exact Hdone].
Qed.

Theorem litmus_reference_not_memory_drf : ~ MemDRF reference_trace.
Proof.
  eapply conflicting_adjacent_accesses_reject_memory_drf
    with (i := 3) (e := Observe (av_write 0 0) 1) (f := Observe (av_write 1 0) 1).
  - reflexivity.
  - reflexivity.
  - apply conflict_l; simpl; congruence.
Qed.

Theorem litmus_sso_participation_guaranteed :
  ParticipationGuaranteed SSO zero_input litmus (Some [0; 1]).
Proof.
  intros trace last Hexec Hdone.
  apply sso_all_executions in Hexec; [|exact Hdone].
  exact (proj1 (proj2 Hexec)).
Qed.

Theorem litmus_spec_participation_not_guaranteed :
  ~ ParticipationGuaranteed Spec zero_input litmus (Some [0; 1]).
Proof.
  intros Hguarantee.
  destruct spec_validated_schedule as [last [Hrun [Hdone [Hgroup _]]]].
  apply run_sound in Hrun.
  specialize (Hguarantee _ _ Hrun Hdone).
  rewrite Hgroup in Hguarantee. discriminate.
Qed.

Theorem litmus_condition_results :
  ~ MemDRF reference_trace /\
  ParticipationGuaranteed SSO zero_input litmus (Some [0; 1]) /\
  ~ ParticipationGuaranteed Spec zero_input litmus (Some [0; 1]).
Proof.
  split; [exact litmus_reference_not_memory_drf|].
  split; [exact litmus_sso_participation_guaranteed|
          exact litmus_spec_participation_not_guaranteed].
Qed.

Corollary litmus_does_not_satisfy_both_conditions : forall p,
  ~ conditions p zero_input litmus reference_trace (Some [0; 1]).
Proof.
  intros p [Hmemory _]. exact (litmus_reference_not_memory_drf Hmemory).
Qed.

Example speculative_trace_not_memory_drf : ~ MemDRF speculative_trace.
Proof.
  eapply conflicting_adjacent_accesses_reject_memory_drf
    with (i := 2) (e := Observe (av_write 0 0) 1) (f := Observe (av_read 1 0) 1).
  - reflexivity.
  - reflexivity.
  - apply conflict_l; simpl; congruence.
Qed.

Example private_locations_memory_drf :
  MemDRF [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 1) 0);
          Memory (Observe (av_write 0 0) 1); Memory (Observe (av_write 1 1) 1)].
Proof.
  apply safe_history_memory_drf. unfold Hist.Safe; cbn.
  intros a b [<-|[<-|[<-|[<-|[]]]]] [<-|[<-|[<-|[<-|[]]]]].
  all: first [apply safe_owner; reflexivity | apply safe_index; discriminate].
Qed.

Example shared_reads_memory_drf :
  MemDRF [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0)].
Proof.
  apply safe_history_memory_drf. unfold Hist.Safe; cbn.
  intros a b [<-|[<-|[]]] [<-|[<-|[]]];
    apply safe_mode; reflexivity.
Qed.

Example reference_collective_orders_reads_before_writes :
  collective_orders reference_trace 1 3 1 0.
Proof.
  exists 2, [0; 1]. repeat split; cbn; auto; lia.
Qed.

Example excluded_thread_not_memory_drf :
  ~ MemDRF [Memory (Observe (av_write 0 0) 1); Synchronize [0];
            Memory (Observe (av_read 1 0) 1)].
Proof.
  intros Hsafe.
  assert (Hconflict : Conflict (av_write 0 0) (av_read 1 0))
    by (apply conflict_l; simpl; congruence).
  specialize (Hsafe 0 2 (Observe (av_write 0 0) 1) (Observe (av_read 1 0) 1)
    eq_refl eq_refl Hconflict).
  destruct Hsafe as [[k [group [Hsync [Hbefore [Hafter [_ Hin]]]]]]|Horder].
  - assert (k = 1) by lia. subst k.
    cbn in Hsync. inversion Hsync; subst group. cbn in Hin. intuition congruence.
  - apply collective_orders_forward in Horder. lia.
Qed.

Definition single_writer_reference_trace :=
  [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
   Synchronize [0; 1]; Memory (Observe (av_write 0 0) 1)].

Example single_writer_reference_runs :
  exists last,
  run SSO zero_input
    [Thread 0; Thread 0; Thread 1; Thread 1; Collective; Thread 0; Thread 0]
    single_writer = Some (single_writer_reference_trace, last) /\
  finished last /\ participants last = Some [0; 1].
Proof.
  eexists; split; [vm_compute; reflexivity|].
  split; [split; repeat constructor|reflexivity].
Qed.

Theorem single_writer_reference_memory_drf : MemDRF single_writer_reference_trace.
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace i)).
    rewrite He. discriminate. }
  assert (Hj : j < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace j)).
    rewrite Hf. discriminate. }
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; simpl in *; congruence].
  - left. exists 2, [0; 1]. repeat split; cbn; auto; lia.
  - right. exists 2, [0; 1]. repeat split; cbn; auto; lia.
Qed.

Theorem single_writer_sso_conditions :
  conditions SSO zero_input single_writer single_writer_reference_trace (Some [0; 1]).
Proof.
  split; [exact single_writer_reference_memory_drf|].
  intros trace last Hexec Hdone.
  apply single_writer_sso_all_executions in Hexec; [|exact Hdone].
  exact (proj1 (proj2 Hexec)).
Qed.

Theorem single_writer_spec_not_conditions :
  ~ conditions Spec zero_input single_writer single_writer_reference_trace (Some [0; 1]).
Proof.
  intros [_ Hguarantee].
  destruct single_writer_spec_validated as [last [Hrun [Hdone [Hgroup _]]]].
  apply run_sound in Hrun.
  specialize (Hguarantee _ _ Hrun Hdone).
  rewrite Hgroup in Hguarantee. discriminate.
Qed.
