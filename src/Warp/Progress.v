From Stdlib Require Import Lists.List Lia.
From Faial.Warp Require Import Semantics Participation Contract TraceOrder Commutation Agreement.
From Faial.Warp Require Reference.

Import ListNotations.

(* Align a finite target prefix, without assuming that it has already finished. *)
Theorem sso_prefix_completion : forall input s trace last,
  execution SSO input s trace last ->
  forall reference_trace reference_last,
  execution SSO input s reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  exists suffix final,
    execution SSO input last suffix final /\ finished final /\
    state_equiv input reference_last final /\
    reorders reference_trace (trace ++ suffix).
Proof.
  intros input s trace last Htarget.
  induction Htarget as [s|a s e s' trace last Hstep Htarget IH];
    intros reference_trace reference_last Hreference Hdone Hdrf.
  - exists reference_trace, reference_last. split; [exact Hreference|].
    split; [exact Hdone|]. split; [apply state_equiv_refl|constructor].
  - assert (Henabled : enabled input a s) by (exists e, s'; exact Hstep).
    destruct (pull_enabled _ _ _ _ Hreference Hdone Hdrf a Henabled)
      as [f [next [tail [final [Hfront [Hrest [Hfinished [Hequiv Horder]]]]]]]].
    rewrite Hstep in Hfront. inversion Hfront; subst f next.
    assert (Htail : MemDRF tail).
    { apply memory_drf_emit_tail with (e := e).
      eapply reorders_memory_drf; eauto. }
    destruct (IH tail final Hrest Hfinished Htail)
      as [suffix [final' [Hcompletion [Hfinal [Hsame Hreorders]]]]].
    exists suffix, final'. split; [exact Hcompletion|].
    split; [exact Hfinal|]. split.
    + eapply state_equiv_trans; eauto.
    + eapply reorders_trans; [exact Horder|].
      destruct e; cbn; [now apply (reorders_prefix _ _ Hreorders [_])|exact Hreorders].
Qed.

Corollary sso_prefix_memory_drf : forall input s reference_trace reference_last trace last,
  execution SSO input s reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  execution SSO input s trace last ->
  exists suffix final,
    execution SSO input last suffix final /\ finished final /\ MemDRF (trace ++ suffix).
Proof.
  intros input s reference_trace reference_last trace last Href Hdone Hdrf Htarget.
  destruct (sso_prefix_completion _ _ _ _ Htarget _ _ Href Hdone Hdrf)
    as [suffix [final [Hexec [Hfinished [_ Horder]]]]].
  exists suffix, final. split; [exact Hexec|]. split; [exact Hfinished|].
  eapply reorders_memory_drf; eauto.
Qed.

Theorem sso_progress : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  execution SSO input (initial programs) trace last ->
  finished last \/ exists a e next, advance SSO input a last = Some (e, next).
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Htarget.
  apply Reference.run_sound in Hrun as [_ [Href Hdone]].
  destruct (sso_prefix_completion _ _ _ _ Htarget _ _ Href Hdone Hdrf)
    as [suffix [final [Hexec [Hfinished _]]]].
  inversion Hexec; subst; eauto.
Qed.

Corollary sso_stuck_is_finished : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  execution SSO input (initial programs) trace last ->
  (forall a, advance SSO input a last = None) -> finished last.
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Htarget Hstuck.
  destruct (sso_progress _ _ _ _ _ _ Hrun Hdrf Htarget) as [Hdone|[a [e [next Hstep]]]];
    [assumption|rewrite Hstuck in Hstep; discriminate].
Qed.

(* Scheduling cannot produce infinitely many successful steps in this syntax.
   A scheduler that simply stops taking steps is not a maximal execution. *)
Theorem execution_length_bound : forall p input schedule s trace last,
  run p input schedule s = Some (trace, last) ->
  length schedule + Reference.remaining last <= Reference.remaining s.
Proof.
  intros p input schedule. induction schedule as [|a rest IH];
    intros s trace last Hrun; cbn in Hrun.
  - inversion Hrun; subst; cbn; lia.
  - destruct (advance p input a s) as [[e next]|] eqn:Hstep; try discriminate.
    destruct (run p input rest next) as [[tail final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. specialize (IH _ _ _ Hrest).
    pose proof (Reference.advance_decreases _ _ _ _ _ _ Hstep). cbn; lia.
Qed.

Theorem no_infinite_execution : forall p input (states : nat -> state) (actions : nat -> action),
  ~ (forall n, exists e, advance p input (actions n) (states n) = Some (e, states (S n))).
Proof.
  intros p input states actions Hsteps.
  assert (Hbound : forall n, n + Reference.remaining (states n) <= Reference.remaining (states 0)).
  { induction n; [lia|]. destruct (Hsteps n) as [e Hstep].
    pose proof (Reference.advance_decreases _ _ _ _ _ _ Hstep). lia. }
  specialize (Hbound (S (Reference.remaining (states 0)))). lia.
Qed.

Corollary sso_maximal_agreement : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  execution SSO input (initial programs) trace last ->
  (forall a, advance SSO input a last = None) ->
  finished last /\ same_observations input reference_trace reference_last trace last /\ MemDRF trace.
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Htarget Hstuck.
  assert (Hdone : finished last) by (eapply sso_stuck_is_finished; eauto).
  split; [exact Hdone|]. split.
  - eapply sso_agreement; eauto. split; [exact Hdrf|].
    eapply sso_participation_guaranteed; eauto.
  - eapply sso_memory_drf; eauto.
Qed.
