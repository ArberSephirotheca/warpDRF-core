From Stdlib Require Import Lists.List Arith.PeanoNat.
From Faial.Warp Require Import Semantics Participation Contract TraceOrder Commutation.
From Faial.Warp Require Reference.

Import ListNotations.

Local Definition action_eq_dec (a b : action) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(* Move an enabled action to the front of a completed DRF execution. Each
   reordering preserves DRF; other schedules are not assumed to be DRF. *)
Lemma pull_enabled : forall input s trace last,
  execution SSO input s trace last -> finished last -> MemDRF trace ->
  forall a, enabled input a s ->
  exists e s' tail final,
    advance SSO input a s = Some (e, s') /\
    execution SSO input s' tail final /\ finished final /\
    state_equiv input last final /\ reorders trace (emit_event e tail).
Proof.
  intros input s trace last Hexec.
  induction Hexec as [s|b s e s1 trace last Hstep Hexec IH];
    intros Hdone Hdrf a Henabled.
  - exfalso. eapply finished_not_enabled; eauto.
  - destruct (action_eq_dec b a) as [->|Hneq].
    + exists e, s1, trace, last. split; [exact Hstep|].
      split; [exact Hexec|]. split; [exact Hdone|].
      split; [apply state_equiv_refl|constructor].
    + assert (Hnext : enabled input a s1).
      { eapply enabled_after_distinct; eauto. }
      assert (Htail : MemDRF trace) by (eapply memory_drf_emit_tail; exact Hdrf).
      destruct (IH Hdone Htail a Hnext)
        as [f [s1' [tail [final [Hfirst [Hrest [Hfinished [Hequiv Horder]]]]]]]].
      assert (Hreordered : MemDRF (emit_event e (emit_event f tail))).
      { eapply reorders_memory_drf; [|exact Hdrf].
        apply reorders_emit; exact Horder. }
      destruct (steps_swap _ _ _ _ _ _ _ _ _ Hneq Hstep Hfirst Henabled Hreordered)
        as [s0' [s2' [Hfront [Hsecond [Hsame Hswap]]]]].
      destruct (execution_equiv _ _ _ _ _ Hrest _ Hsame)
        as [final' [Hrest' Hfinal]].
      exists f, s0', (emit_event e tail), final'.
      split; [exact Hfront|]. split; [econstructor; eauto|].
      split; [eapply finished_equiv; eauto|]. split.
      * eapply state_equiv_trans; eauto.
      * eapply reorders_trans; [apply reorders_emit; exact Horder|exact Hswap].
Qed.

Lemma finished_execution : forall input s trace last,
  finished s -> execution SSO input s trace last -> trace = [] /\ last = s.
Proof.
  intros input s trace last Hdone Hexec. inversion Hexec; subst; auto.
  exfalso. eapply (finished_not_enabled input s a Hdone). eexists; eexists; eauto.
Qed.

(* The target schedule supplies the next action. Pulling it to the front of
   the reference aligns both executions one step at a time. *)
Theorem completed_sso_agreement : forall input s trace last,
  execution SSO input s trace last -> finished last ->
  forall reference_trace reference_last,
  execution SSO input s reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  state_equiv input reference_last last /\ reorders reference_trace trace.
Proof.
  intros input s trace last Htarget.
  induction Htarget as [s|a s e s' trace last Hstep Htarget IH];
    intros Hdone reference_trace reference_last Hreference Hrefdone Hdrf.
  - destruct (finished_execution _ _ _ _ Hdone Hreference) as [-> ->].
    split; [apply state_equiv_refl|constructor].
  - assert (Henabled : enabled input a s) by (exists e, s'; exact Hstep).
    destruct (pull_enabled _ _ _ _ Hreference Hrefdone Hdrf a Henabled)
      as [f [next [tail [final [Hfront [Hrest [Hfinished [Hequiv Horder]]]]]]]].
    rewrite Hstep in Hfront. inversion Hfront; subst f next.
    assert (Htail : MemDRF tail).
    { apply memory_drf_emit_tail with (e := e).
      eapply reorders_memory_drf; eauto. }
    destruct (IH Hdone tail final Hrest Hfinished Htail) as [Hfinal Hrestorder].
    split.
    + eapply state_equiv_trans; eauto.
    + eapply reorders_trans; [exact Horder|now apply reorders_emit].
Qed.

Theorem sso_agreement : SSOAgreement.
Proof.
  intros programs input reference_trace reference_last Hreference [Hdrf _]
    trace last Htarget Hdone.
  apply Reference.run_sound in Hreference as [_ [Hreference Hrefdone]].
  destruct (completed_sso_agreement _ _ _ _ Htarget Hdone
    _ _ Hreference Hrefdone Hdrf) as [[_ [_ [Hgroup Hmemory]]] Horder].
  split; [exact Hgroup|]. split; [now apply reorders_read_history|exact Hmemory].
Qed.

Corollary sso_participation_guaranteed : forall programs input reference_trace reference_last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  ParticipationGuaranteed SSO input (initial programs) (participants reference_last).
Proof.
  intros programs input reference_trace reference_last Hreference Hdrf trace last Htarget Hdone.
  apply Reference.run_sound in Hreference as [_ [Hreference Hrefdone]].
  destruct (completed_sso_agreement _ _ _ _ Htarget Hdone
    _ _ Hreference Hrefdone Hdrf) as [[_ [_ [Hgroup _]]] _].
  symmetry; exact Hgroup.
Qed.

Corollary sso_memory_drf : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  execution SSO input (initial programs) trace last -> finished last -> MemDRF trace.
Proof.
  intros programs input reference_trace reference_last trace last Hreference Hdrf Htarget Hdone.
  apply Reference.run_sound in Hreference as [_ [Hreference Hrefdone]].
  destruct (completed_sso_agreement _ _ _ _ Htarget Hdone
    _ _ Hreference Hrefdone Hdrf) as [_ Horder].
  eapply reorders_memory_drf; eauto.
Qed.
