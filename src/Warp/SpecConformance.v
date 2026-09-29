From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
From Faial.Warp Require Import Semantics Participation Speculation Uniform Contract
  Commutation Agreement ReferenceExamples.
From Faial.Warp Require Lang Reference.

Import ListNotations.

(* Spec releases a collective before every branch decision is known, like
   __activemask(), which reports whichever threads have arrived. In
   warp-uniform control flow that is harmless: a thread left out would later
   have to enter, which Spec rejects, so every completed Spec run waited for
   all decisions and is also an SSO run. *)
Definition uniform_state b s :=
  Forall (fun code => uniform_tests b code = true) (threads (machine s)) /\
  Forall (fun d => d = Unresolved \/ d = if b then Entered else Skipped) (decisions s).

Local Lemma replace_thread_forall : forall (P : Lang.t -> Prop) codes tid code,
  Forall P codes -> P code -> Forall P (replace_thread tid code codes).
Proof.
  intros P codes. induction codes as [|first rest IH]; intros [|tid] code Hall Hcode;
    cbn; try constructor; inversion Hall; subst; auto.
Qed.

Local Lemma forall_replace_decision : forall (P : decision -> Prop) ds tid d,
  Forall P ds -> P d -> Forall P (firstn tid ds ++ [d] ++ skipn (S tid) ds).
Proof.
  intros P ds. induction ds as [|x ds IH]; intros [|tid] d Hall Hd; cbn;
    inversion Hall; subst; repeat constructor; auto.
  apply IH; assumption.
Qed.

Local Lemma collective_step_view : forall p input s e s',
  advance p input Collective s = Some (e, s') ->
  participants s = None /\ entered_threads (decisions s) <> [] /\
  exists codes', release_collective (decisions s) (threads (machine s)) = Some codes' /\
    s' = State (Semantics.State (memory (machine s)) codes') (decisions s)
      (Some (entered_threads (decisions s))).
Proof.
  intros p input s e s' Hstep. unfold advance in Hstep.
  destruct (participants s); [discriminate|].
  destruct (entered_threads (decisions s)) as [|t rest]; [discriminate|].
  destruct (match p with SSO => all_decided (decisions s) | Spec => true end);
    [|discriminate].
  destruct (release_collective (decisions s) (threads (machine s))) as [codes'|];
    [|discriminate].
  inversion Hstep; subst. split; [reflexivity|]. split; [discriminate|].
  exists codes'. split; reflexivity.
Qed.

Lemma advance_uniform_state : forall p input a s e s' b,
  uniform_state b s -> advance p input a s = Some (e, s') -> uniform_state b s'.
Proof.
  intros p input [tid|] s e s' b [Hcodes Hds] Hstep.
  - apply thread_advance_view in Hstep
      as [code [o [m' [code' [ds' [Hcode [Hthread [Hdecide [_ ->]]]]]]]]].
    assert (Hu : uniform_tests b code = true).
    { rewrite Forall_forall in Hcodes. apply Hcodes. eapply nth_error_In; eauto. }
    unfold uniform_state; cbn [threads machine decisions]. split.
    + apply replace_thread_forall; [exact Hcodes|].
      eapply uniform_tests_step; eauto.
    + unfold Commutation.decide in Hdecide.
      destruct (branch_decision tid code) as [v|] eqn:Hbranch.
      * pose proof (uniform_branch_decision _ _ _ _ Hu Hbranch) as ->.
        destruct (nth_error (decisions s) tid) as [[]|]; try discriminate;
          destruct (participants s), b; try discriminate; inversion Hdecide; subst;
          apply forall_replace_decision; auto.
      * inversion Hdecide; subst. exact Hds.
  - apply collective_step_view in Hstep as [_ [_ [codes' [Hrelease ->]]]].
    unfold uniform_state; cbn [threads machine decisions].
    split; [eapply release_collective_uniform; eauto|exact Hds].
Qed.

(* A thread that entered took the shared branch, which must then be true. *)
Local Lemma uniform_entered : forall b s,
  uniform_state b s -> entered_threads (decisions s) <> [] -> b = true.
Proof.
  intros b s [_ Hds] Hnonempty.
  destruct (entered_threads (decisions s)) as [|t rest] eqn:Hentered;
    [contradiction|].
  assert (Hin : In t (entered_threads (decisions s))) by (rewrite Hentered; now left).
  unfold entered_threads in Hin. apply filter_In in Hin as [_ Hin].
  destruct (nth_error (decisions s) t) as [[]|] eqn:Hnth; try discriminate.
  rewrite Forall_forall in Hds. apply nth_error_In in Hnth.
  destruct (Hds _ Hnth) as [Hbad|Hb]; [discriminate|].
  destruct b; [reflexivity|discriminate].
Qed.

(* After Spec releases the collective, an undecided thread whose branch is
   true can never decide, because Spec rejects a late participant. *)
Local Lemma unresolved_stays : forall input s trace last u group,
  execution Spec input s trace last ->
  uniform_state true s -> participants s = Some group ->
  nth_error (decisions s) u = Some Unresolved ->
  nth_error (decisions last) u = Some Unresolved.
Proof.
  intros input s trace last u group Hexec. revert group.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH];
    intros group Huniform Hgroup Hu; [exact Hu|].
  pose proof (advance_uniform_state _ _ _ _ _ _ _ Huniform Hstep) as Huniform'.
  destruct a as [tid|].
  - apply thread_advance_view in Hstep
      as [code [o [m' [code' [ds' [Hcode [_ [Hdecide [_ Hs']]]]]]]]].
    subst s'. apply (IH group Huniform'); [exact Hgroup|]. cbn [decisions].
    destruct (Nat.eq_dec tid u) as [->|Hneq].
    + unfold Commutation.decide in Hdecide. rewrite Hu, Hgroup in Hdecide.
      destruct (branch_decision u code) as [v|] eqn:Hbranch.
      * assert (Hcodeu : uniform_tests true code = true).
        { destruct Huniform as [Hcodes _]. rewrite Forall_forall in Hcodes.
          apply Hcodes. eapply nth_error_In; eauto. }
        pose proof (uniform_branch_decision _ _ _ _ Hcodeu Hbranch) as ->.
        discriminate.
      * inversion Hdecide; subst. exact Hu.
    + rewrite (Commutation.decide_other _ _ _ _ _ _ Hdecide Hneq). exact Hu.
  - destruct (collective_step_view _ _ _ _ _ Hstep) as [Hnone _]. congruence.
Qed.

Local Lemma not_all_decided : forall ds,
  all_decided ds = false -> exists u, nth_error ds u = Some Unresolved.
Proof.
  induction ds as [|d ds IH]; intros Hall; [discriminate|].
  destruct d.
  - exists 0. reflexivity.
  - destruct (IH Hall) as [u Hu]. exists (S u). exact Hu.
  - destruct (IH Hall) as [u Hu]. exists (S u). exact Hu.
Qed.

Local Lemma spec_collective_sso : forall input s e s',
  advance Spec input Collective s = Some (e, s') ->
  all_decided (decisions s) = true ->
  advance SSO input Collective s = Some (e, s').
Proof.
  intros input s e s' Hstep Hall. unfold advance in *.
  destruct (participants s); [discriminate|].
  destruct (entered_threads (decisions s)); [discriminate|].
  rewrite Hall. exact Hstep.
Qed.

(* Thread steps do not depend on the policy, and every collective in a
   completed Spec run found all decisions made, as SSO requires. *)
Lemma completed_spec_is_sso : forall input s trace last b,
  execution Spec input s trace last -> finished last ->
  uniform_state b s -> execution SSO input s trace last.
Proof.
  intros input s trace last b Hexec Hdone.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; intros Huniform;
    [constructor|].
  pose proof (advance_uniform_state _ _ _ _ _ _ _ Huniform Hstep) as Huniform'.
  apply (execution_step SSO input a s e s' trace last); [|exact (IH Hdone Huniform')].
  destruct a as [tid|]; [exact Hstep|].
  apply spec_collective_sso; [exact Hstep|].
  destruct (all_decided (decisions s)) eqn:Hall; [reflexivity|exfalso].
  destruct (not_all_decided _ Hall) as [u Hu].
  destruct (collective_step_view _ _ _ _ _ Hstep)
    as [_ [Hnonempty [codes' [_ Hs']]]].
  pose proof (uniform_entered _ _ Huniform Hnonempty) as Hb. subst b s'.
  pose proof (unresolved_stays _ _ _ _ u _ Hexec Huniform' eq_refl Hu) as Hlast.
  destruct Hdone as [_ Hdecided].
  exact (Commutation.all_decided_not_unresolved _ _ Hdecided Hlast).
Qed.

(* Spec can still release early in warp-uniform code, but the thread it left
   out cannot enter afterwards, so that run is stuck and never completes. *)
Example early_release_gets_stuck :
  exists s,
  run Spec zero_input [Thread 0; Collective] (initial [all_enter; all_enter]) =
    Some ([Synchronize [0]], s) /\
  ~ finished s /\ forall a, advance Spec zero_input a s = None.
Proof.
  eexists. split; [vm_compute; reflexivity|]. split.
  - intros [_ Hdecided]. vm_compute in Hdecided. discriminate.
  - intros [[|[|[|tid]]]|]; vm_compute; reflexivity.
Qed.

(* Spec conforms to the full-warp configuration: every completed run of a
   kernel meeting both conditions agrees with the reference. *)
Theorem spec_full_warp_agreement : forall programs input reference_trace reference_last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  conditions FullWarp programs reference_trace ->
  forall trace last,
  execution Spec input (initial programs) trace last -> finished last ->
  same_observations input reference_trace reference_last trace last.
Proof.
  intros programs input reference_trace reference_last Hrun [Hdrf [[b Hcodes] _]]
    trace last Hexec Hdone.
  apply (sso_agreement_from_drf _ _ _ _ Hrun Hdrf); [|exact Hdone].
  apply (completed_spec_is_sso _ _ _ _ b Hexec Hdone).
  split; [exact Hcodes|].
  apply Forall_forall. intros d Hd. cbn [decisions initial] in Hd.
  left. exact (repeat_spec _ _ _ Hd).
Qed.

(* Condition 2 is needed. The single-writer kernel is memory-DRF, but its
   collective sits under a branch that depends on memory, which the full-warp
   configuration does not permit; Spec conforms to that configuration and
   disagrees with the reference on this kernel. *)
Theorem participation_condition_needed :
  exists programs input reference_trace reference_last trace last,
    Reference.run input programs = Some (reference_trace, reference_last) /\
    MemDRF reference_trace /\
    ~ UnambiguousParticipation FullWarp programs reference_trace /\
    execution Spec input (initial programs) trace last /\ finished last /\
    ~ same_observations input reference_trace reference_last trace last.
Proof.
  destruct reference_reproduces_single_writer as [reference_last [Hreference [_ Hgroup]]].
  destruct single_writer_spec_validated as [last [Hrun [Hdone [Hspec _]]]].
  exists (threads (machine single_writer)), zero_input, single_writer_reference_trace,
    reference_last, speculative_trace, last.
  split; [exact Hreference|]. split; [exact single_writer_reference_memory_drf|].
  split; [exact single_writer_not_full_warp|].
  split; [eapply Participation.run_sound; exact Hrun|]. split; [exact Hdone|].
  intros [Heq _]. rewrite Hgroup, Hspec in Heq. discriminate.
Qed.

(* So memory DRF alone does not give agreement on a conforming target. *)
Corollary memory_drf_alone_insufficient :
  ~ (forall programs input reference_trace reference_last,
       Reference.run input programs = Some (reference_trace, reference_last) ->
       MemDRF reference_trace ->
       forall trace last,
       execution Spec input (initial programs) trace last -> finished last ->
       same_observations input reference_trace reference_last trace last).
Proof.
  intros Hagree.
  destruct participation_condition_needed
    as [programs [input [reference_trace [reference_last [trace [last
      [Hrun [Hdrf [_ [Hexec [Hdone Hdiffer]]]]]]]]]]].
  exact (Hdiffer (Hagree _ _ _ _ Hrun Hdrf _ _ Hexec Hdone)).
Qed.
