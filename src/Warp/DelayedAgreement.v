From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import AVal NatUtil.
From Faial.Warp Require Import Semantics Participation Contract TraceOrder Commutation Agreement Progress.
From Faial.Warp Require Delayed DelayedExecution Reference.

Import ListNotations.

Definition write_event w :=
  Memory (Observe (av_write (Delayed.owner w) (Delayed.address w)) (Delayed.contents w)).

(* The write has been issued, but no later collective has included its owner. *)
Definition unpublished trace w := exists before after,
  trace = before ++ write_event w :: after /\
  forall group, In (Synchronize group) after -> ~ In (Delayed.owner w) group.

Definition pending_supported trace s :=
  forall w, In w (Delayed.pending s) -> unpublished trace w.

Lemma unpublished_append : forall trace tail w,
  unpublished trace w ->
  (forall group, In (Synchronize group) tail -> ~ In (Delayed.owner w) group) ->
  unpublished (trace ++ tail) w.
Proof.
  intros trace tail w [before [after [-> Hafter]]] Htail.
  exists before, (after ++ tail). split.
  - now rewrite <- app_assoc.
  - intros group Hin. apply in_app_or in Hin as [Hin|Hin]; eauto.
Qed.

Lemma pending_memory_event : forall trace s o,
  pending_supported trace s -> pending_supported (trace ++ [Memory o]) s.
Proof.
  intros trace s o Hsupported w Hin. eapply unpublished_append; [apply Hsupported; exact Hin|].
  intros group [Hbad|[]]. discriminate.
Qed.

Lemma pending_store : forall trace s tid location value,
  pending_supported trace s ->
  pending_supported (trace ++ [Memory (Observe (av_write tid location) value)])
    (Delayed.store tid location value s).
Proof.
  intros trace s tid location value Hsupported w [<-|Hin].
  - exists trace, []. split; [reflexivity|]. intros group [].
  - eapply pending_memory_event; eauto.
Qed.

Lemma pending_flush : forall trace s group,
  pending_supported trace s ->
  pending_supported (trace ++ [Synchronize group]) (Delayed.flush group s).
Proof.
  intros trace s group Hsupported w Hin.
  pose proof (Delayed.flush_removes_participant_writes _ _ _ Hin) as Houtside.
  apply filter_In in Hin as [Hin _].
  eapply unpublished_append; [apply Hsupported; exact Hin|].
  intros g [Heq|[]]. inversion Heq; subst; exact Houtside.
Qed.

Lemma unflushed_write_cannot_conflict : forall trace suffix w o,
  unpublished trace w -> MemDRF (trace ++ Memory o :: suffix) ->
  ~ Conflict (av_write (Delayed.owner w) (Delayed.address w)) (access o).
Proof.
  intros trace suffix w o [before [after [-> Hafter]]] Hdrf Hconflict.
  rewrite <- app_assoc in Hdrf. cbn in Hdrf.
  assert (Hw : nth_error (before ++ write_event w :: after ++ Memory o :: suffix)
    (length before) = Some (write_event w)).
  { rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Ho : nth_error (before ++ write_event w :: after ++ Memory o :: suffix)
    (length before + S (length after)) = Some (Memory o)).
  { rewrite nth_error_app2 by lia.
    replace (length before + S (length after) - length before) with (S (length after)) by lia.
    cbn. rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag. }
  destruct (Hdrf _ _ _ _ Hw Ho Hconflict) as [Horder|Horder].
  2: { apply collective_orders_forward in Horder; lia. }
  destruct Horder as [k [group [Hk [Hlo [Hhi [Howner _]]]]]].
  unfold write_event in Hk.
  rewrite nth_error_app2 in Hk by lia.
  destruct (k - length before) as [|j] eqn:Hj; [lia|]. cbn in Hk.
  assert (Hbound : j < length after) by lia.
  rewrite nth_error_app1 in Hk by exact Hbound.
  apply nth_error_In in Hk. exact (Hafter group Hk Howner).
Qed.

Lemma unflushed_same_location_has_same_owner : forall trace suffix s o,
  pending_supported trace s -> MemDRF (trace ++ Memory o :: suffix) ->
  forall w, In w (Delayed.pending s) -> Delayed.address w = av_index (access o) ->
  Delayed.owner w = av_owner (access o).
Proof.
  intros trace suffix s o Hsupported Hdrf w Hin Heq.
  destruct (Nat.eq_dec (Delayed.owner w) (av_owner (access o))) as [Howner|Hneq]; auto.
  exfalso. eapply unflushed_write_cannot_conflict; [apply Hsupported; exact Hin|exact Hdrf|].
  apply conflict_l; cbn; auto.
Qed.

Lemma execution_append : forall input s prefix mid suffix last,
  execution SSO input s prefix mid -> execution SSO input mid suffix last ->
  execution SSO input s (prefix ++ suffix) last.
Proof.
  intros input s prefix mid suffix last Hprefix Hsuffix.
  induction Hprefix as [s|a s e next trace mid Hstep Hprefix IH]; [exact Hsuffix|].
  replace (emit_event e trace ++ suffix) with (emit_event e (trace ++ suffix))
    by (destruct e; reflexivity).
  econstructor; eauto.
Qed.

Definition logical_control s :=
  DelayedExecution.with_memory (Delayed.logical (DelayedExecution.memory_of s))
    (DelayedExecution.control s).

Lemma memory_of_pack : forall c m, DelayedExecution.memory_of (DelayedExecution.pack c m) = m.
Proof. intros c [m writes]; reflexivity. Qed.

Lemma thread_replay_with_memory : forall input tid s e next m,
  advance SSO input (Thread tid) s = Some (e, next) ->
  (forall o, e = Some (Memory o) -> readable input m (Some o)) ->
  exists memory', advance SSO input (Thread tid) (DelayedExecution.with_memory m s) =
    Some (e, DelayedExecution.with_memory memory' next).
Proof.
  intros input tid s e next m Hstep Hread.
  apply thread_advance_view in Hstep as
    [code [o [m' [code' [ds' [Hcode [Hthread [Hdecide [-> ->]]]]]]]]].
  destruct (thread_step_replay _ _ _ _ _ _ _ Hthread) as [_ [_ [_ Hreplay]]].
  assert (Hr : readable input m o).
  { destruct o; cbn; [apply (Hread _ eq_refl)|exact I]. }
  exists (effect o m).
  eapply (Commutation.thread_advance_build _ _ _ (DelayedExecution.with_memory m s)
    code o (effect o m) code' ds'); cbn; eauto.
Qed.

Lemma thread_available_with_memory : forall input tid s e next m,
  advance SSO input (Thread tid) s = Some (e, next) ->
  exists f final, advance SSO input (Thread tid) (DelayedExecution.with_memory m s) = Some (f, final).
Proof.
  intros input tid s e next m Hstep.
  apply thread_advance_view in Hstep as
    [code [o [m' [code' [ds' [Hcode [Hthread [Hdecide [-> ->]]]]]]]]].
  destruct (thread_step_enabled_memory _ _ _ _ _ _ _ m Hthread) as [f [n [rest Hother]]].
  do 2 eexists. eapply Commutation.thread_advance_build; cbn; eauto.
Qed.

Lemma buffered_thread_matches : forall input tid history sc weak e next,
  state_equiv input sc (logical_control weak) ->
  pending_supported history (DelayedExecution.memory_of weak) ->
  Delayed.coherent (DelayedExecution.memory_of weak) ->
  (forall f final, advance SSO input (Thread tid) sc = Some (f, final) ->
    exists suffix, MemDRF (history ++ emit_event f suffix)) ->
  DelayedExecution.advance input (DelayedExecution.Execute (Thread tid)) weak = Some (e, next) ->
  exists sc', advance SSO input (Thread tid) sc = Some (e, sc') /\
    state_equiv input sc' (logical_control next) /\
    pending_supported (history ++ emit_event e []) (DelayedExecution.memory_of next) /\
    Delayed.coherent (DelayedExecution.memory_of next).
Proof.
  intros input tid history [[m codes] ds group] [[[cm codes'] ds' group'] writes] e next
    [Hcodes [Hds [Hgroup Hmem]]] Hsupported Hcoherent Hfuture Hstep.
  cbn in Hcodes, Hds, Hgroup. subst codes' ds' group'.
  change (match advance SSO input (Thread tid)
    (DelayedExecution.with_memory (Delayed.view tid (Delayed.State cm writes))
      (State (Semantics.State cm codes) ds group)) with
    | Some (ev, local) => Some (ev, DelayedExecution.pack local
        (DelayedExecution.record_write ev (Delayed.State cm writes)))
    | None => None end = Some (e, next)) in Hstep.
  destruct (advance SSO input (Thread tid)
    (DelayedExecution.with_memory (Delayed.view tid (Delayed.State cm writes))
      (State (Semantics.State cm codes) ds group))) as [[ev local]|] eqn:Hlocal;
    try discriminate.
  inversion Hstep; subst e next; clear Hstep.
  destruct (thread_available_with_memory _ _ _ _ _ m Hlocal) as [f [sc' Hsc]].
  change (advance SSO input (Thread tid) (State (Semantics.State m codes) ds group) =
    Some (f, sc')) in Hsc.
  destruct (Hfuture _ _ Hsc) as [suffix Hdrf].
  pose proof Hsc as Hview.
  apply thread_advance_view in Hview as
    [code [o [m' [code' [nextds [Hcode [Hthread [Hdecide [-> Hsc']]]]]]]]].
  destruct (thread_step_replay _ _ _ _ _ _ _ Hthread) as [Hmemstep [Hread [Howner _]]].
  assert (Hown : forall obs, o = Some obs -> forall w, In w writes ->
    Delayed.address w = av_index (access obs) -> Delayed.owner w = av_owner (access obs)).
  { intros obs Ho. subst o.
    exact (unflushed_same_location_has_same_owner _ _ (Delayed.State cm writes) _ Hsupported Hdrf). }
  assert (Hreadlocal : forall obs, option_map Memory o = Some (Memory obs) ->
    readable input (Delayed.view tid (Delayed.State cm writes)) (Some obs)).
  { intros obs Hobs. destruct o as [actual|]; try discriminate.
    inversion Hobs; subst actual.
    destruct obs as [[who location mode] value]. destruct mode; cbn in *; auto.
    change (Delayed.read input tid location (Delayed.State cm writes) = value).
    rewrite Delayed.read_matches_logical.
    - rewrite <- Hmem. exact Hread.
    - intros w Hin Haddr. rewrite (Hown _ eq_refl w Hin Haddr). exact (Howner _ eq_refl). }
  destruct (thread_replay_with_memory _ _ _ _ _
    (Delayed.view tid (Delayed.State cm writes)) Hsc Hreadlocal) as [localmem Hreplay].
  change (advance SSO input (Thread tid)
    (DelayedExecution.with_memory (Delayed.view tid (Delayed.State cm writes))
      (State (Semantics.State cm codes) ds group)) =
    Some (option_map Memory o, DelayedExecution.with_memory localmem sc')) in Hreplay.
  rewrite Hlocal in Hreplay. inversion Hreplay; subst ev local.
  exists sc'. split; [exact Hsc|]. split.
  - subst sc'. unfold state_equiv, logical_control. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros location. change (load input m' location =
      load input (Delayed.logical (DelayedExecution.record_write (option_map Memory o)
        (Delayed.State cm writes))) location).
    rewrite Hmemstep.
    replace (Delayed.logical (DelayedExecution.record_write (option_map Memory o)
      (Delayed.State cm writes))) with (effect o (Delayed.logical (Delayed.State cm writes)))
      by (destruct o as [[[who index mode] value]|]; [destruct mode|]; reflexivity).
    apply effect_equiv. exact Hmem.
  - rewrite memory_of_pack. split.
    + destruct o as [[[who index mode] value]|]; cbn.
      * destruct mode; cbn; [now apply pending_memory_event|now apply pending_store].
      * now rewrite app_nil_r.
    + destruct o as [[[who index mode] value]|]; cbn; [destruct mode; cbn|]; auto.
      apply Delayed.store_preserves_coherence; [exact Hcoherent|exact (Hown _ eq_refl)].
Qed.

Lemma collective_with_memory : forall input c e next m,
  advance SSO input Collective c = Some (e, next) ->
  advance SSO input Collective (DelayedExecution.with_memory m c) =
    Some (e, DelayedExecution.with_memory m next).
Proof.
  intros input [[cm codes] ds group] e next m Hstep.
  cbn [DelayedExecution.with_memory advance machine participants decisions Semantics.threads
    Semantics.memory] in *.
  destruct group; try discriminate.
  destruct (entered_threads ds); try discriminate.
  destruct (all_decided ds); try discriminate.
  destruct (release_collective ds codes); try discriminate.
  inversion Hstep; subst. reflexivity.
Qed.

Lemma buffered_collective_matches : forall input history sc weak e next,
  state_equiv input sc (logical_control weak) ->
  pending_supported history (DelayedExecution.memory_of weak) ->
  Delayed.coherent (DelayedExecution.memory_of weak) ->
  DelayedExecution.advance input (DelayedExecution.Execute Collective) weak = Some (e, next) ->
  exists sc', advance SSO input Collective sc = Some (e, sc') /\
    state_equiv input sc' (logical_control next) /\
    pending_supported (history ++ emit_event e []) (DelayedExecution.memory_of next) /\
    Delayed.coherent (DelayedExecution.memory_of next).
Proof.
  intros input history [[m codes] ds oldgroup] [[[cm codes'] ds' group'] writes] e next
    [Hcodes [Hds [Hgroup Hmem]]] Hsupported Hcoherent Hstep.
  cbn in Hcodes, Hds, Hgroup. subst codes' ds' group'.
  cbn [DelayedExecution.advance DelayedExecution.control] in Hstep.
  destruct (advance SSO input Collective (State (Semantics.State cm codes) ds oldgroup))
    as [[ev c]|] eqn:Hcollective; try discriminate.
  destruct ev as [[obs|group]|]; try discriminate. inversion Hstep; subst e next.
  exists (DelayedExecution.with_memory m c). split.
  - exact (collective_with_memory _ _ _ _ m Hcollective).
  - split.
    + unfold state_equiv, logical_control. cbn.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      intros location. change (load input m location =
        load input (Delayed.logical (Delayed.flush group (Delayed.State cm writes))) location).
      rewrite Delayed.flush_preserves_logical; [exact (Hmem location)|exact Hcoherent].
    + rewrite memory_of_pack. split.
      * apply pending_flush. exact Hsupported.
      * apply Delayed.flush_preserves_coherence. exact Hcoherent.
Qed.

Lemma buffered_step_matches : forall input start reference_trace reference_last history sc weak a e next,
  execution SSO input start reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  execution SSO input start history sc ->
  state_equiv input sc (logical_control weak) ->
  pending_supported history (DelayedExecution.memory_of weak) ->
  Delayed.coherent (DelayedExecution.memory_of weak) ->
  DelayedExecution.advance input a weak = Some (e, next) ->
  exists sc', execution SSO input sc (emit_event e []) sc' /\
    state_equiv input sc' (logical_control next) /\
    pending_supported (history ++ emit_event e []) (DelayedExecution.memory_of next) /\
    Delayed.coherent (DelayedExecution.memory_of next).
Proof.
  intros input start reference_trace reference_last history sc weak [act|] e next
    Href Hdone Hdrf Hprefix Haligned Hsupported Hcoherent Hstep.
  - destruct act as [tid|].
    + destruct (buffered_thread_matches input tid history sc weak e next Haligned Hsupported Hcoherent)
        as [sc' [Hsc Hrest]]; [|exact Hstep|].
      { intros f final Hsc.
        assert (Hextended : execution SSO input start (history ++ emit_event f []) final).
        { eapply execution_append; [exact Hprefix|]. econstructor; [exact Hsc|constructor]. }
        destruct (sso_prefix_memory_drf _ _ _ _ _ _ Href Hdone Hdrf Hextended)
          as [suffix [last [_ [_ Hsafe]]]].
        exists suffix. rewrite <- app_assoc in Hsafe. destruct f; exact Hsafe. }
      exists sc'. split; [econstructor; [exact Hsc|constructor]|exact Hrest].
    + destruct (buffered_collective_matches _ _ _ _ _ _ Haligned Hsupported Hcoherent Hstep)
        as [sc' [Hsc Hrest]].
      exists sc'. split; [econstructor; [exact Hsc|constructor]|exact Hrest].
  - cbn [DelayedExecution.advance] in Hstep.
    destruct (DelayedExecution.writes weak); try discriminate.
    destruct (Reference.finishedb (DelayedExecution.control weak)); try discriminate.
    inversion Hstep; subst e next.
    exists sc. split; [constructor|]. split.
    + destruct weak as [[[cm codes] ds group] writes]. exact Haligned.
    + rewrite memory_of_pack. split.
      * intros x Hin; contradiction.
      * intros x y Hx; contradiction.
Qed.

Theorem delayed_execution_matches_sc : forall input start reference_trace reference_last weak trace last,
  execution SSO input start reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  DelayedExecution.execution input weak trace last ->
  forall history sc,
  execution SSO input start history sc ->
  state_equiv input sc (logical_control weak) ->
  pending_supported history (DelayedExecution.memory_of weak) ->
  Delayed.coherent (DelayedExecution.memory_of weak) ->
  exists final, execution SSO input sc trace final /\
    state_equiv input final (logical_control last).
Proof.
  intros input start reference_trace reference_last weak trace last Href Hdone Hdrf Hweak.
  induction Hweak as [weak|a weak e next trace last Hstep Hweak IH];
    intros history sc Hprefix Haligned Hsupported Hcoherent.
  - exists sc. split; [constructor|exact Haligned].
  - destruct (buffered_step_matches _ _ _ _ _ _ _ _ _ _ Href Hdone Hdrf Hprefix
      Haligned Hsupported Hcoherent Hstep) as [sc' [Hsc [Hsame [Hpending Hconsistent]]]].
    assert (Hprefix' : execution SSO input start (history ++ emit_event e []) sc').
    { eapply execution_append; eauto. }
    destruct (IH _ _ Hprefix' Hsame Hpending Hconsistent) as [final [Hrest Hfinal]].
    exists final. split; [|exact Hfinal].
    replace (emit_event e trace) with (emit_event e [] ++ trace) by (destruct e; reflexivity).
    eapply execution_append; eauto.
Qed.

Corollary delayed_prefix_matches_sc : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  DelayedExecution.execution input (DelayedExecution.initial programs) trace last ->
  exists sc, execution SSO input (initial programs) trace sc /\
    state_equiv input sc (logical_control last).
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Hweak.
  apply Reference.run_sound in Hrun as [_ [Href Hdone]].
  eapply (delayed_execution_matches_sc _ _ _ _ _ _ _ Href Hdone Hdrf Hweak
    [] (initial programs)).
  - constructor.
  - apply state_equiv_refl.
  - intros w Hin; contradiction.
  - intros w v Hin; contradiction.
Qed.

(* Only reference DRF is assumed. The target's reads, participant group, and
   final memory are consequences, not premises of the simulation. *)
Theorem delayed_sso_agreement : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  DelayedExecution.execution input (DelayedExecution.initial programs) trace last ->
  DelayedExecution.finished last ->
  same_observations input reference_trace reference_last trace (DelayedExecution.control last) /\
  MemDRF trace.
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Hweak [Hdone Hempty].
  destruct (delayed_prefix_matches_sc _ _ _ _ _ _ Hrun Hdrf Hweak) as [sc [Hsc Haligned]].
  assert (Hscdone : finished sc).
  { destruct Haligned as [Hcodes [Hds _]], Hdone as [Hthreads Hdecisions].
    split; [unfold Semantics.finished in *; now rewrite Hcodes|now rewrite Hds]. }
  destruct (sso_agreement_from_drf _ _ _ _ Hrun Hdrf _ _ Hsc Hscdone)
    as [Hgroup [Hreads Hmemory]].
  destruct Haligned as [_ [_ [Hparticipants Hlogical]]].
  split; [|eapply sso_memory_drf; eauto].
  split; [now rewrite Hgroup|]. split; [exact Hreads|].
  intros location. rewrite Hmemory, Hlogical.
  change (load input (Delayed.publish (DelayedExecution.writes last)
    (memory (machine (DelayedExecution.control last)))) location =
    load input (memory (machine (DelayedExecution.control last))) location).
  now rewrite Hempty.
Qed.

Lemma buffered_action_available : forall input sc weak a e next,
  state_equiv input sc (logical_control weak) ->
  advance SSO input a sc = Some (e, next) ->
  exists f last, DelayedExecution.advance input (DelayedExecution.Execute a) weak = Some (f, last).
Proof.
  intros input [[m codes] ds group] [[[cm codes'] ds' group'] writes] [tid|] e next
    [Hcodes [Hds [Hgroup _]]] Hstep;
    cbn in Hcodes, Hds, Hgroup; subst codes' ds' group'.
  - destruct (thread_available_with_memory _ _ _ _ _
      (Delayed.view tid (Delayed.State cm writes)) Hstep) as [f [local Hlocal]].
    change (advance SSO input (Thread tid)
      (DelayedExecution.with_memory (Delayed.view tid (Delayed.State cm writes))
        (State (Semantics.State cm codes) ds group)) = Some (f, local)) in Hlocal.
    exists f, (DelayedExecution.pack local (DelayedExecution.record_write f (Delayed.State cm writes))).
    cbn [DelayedExecution.advance DelayedExecution.control].
    change (match advance SSO input (Thread tid)
      (DelayedExecution.with_memory (Delayed.view tid (Delayed.State cm writes))
        (State (Semantics.State cm codes) ds group)) with
      | Some (ev, c) => Some (ev, DelayedExecution.pack c
          (DelayedExecution.record_write ev (Delayed.State cm writes)))
      | None => None end = Some (f, DelayedExecution.pack local
        (DelayedExecution.record_write f (Delayed.State cm writes)))).
    now rewrite Hlocal.
  - pose proof (collective_with_memory _ _ _ _ cm Hstep) as Hlocal.
    change (advance SSO input Collective (State (Semantics.State cm codes) ds group) =
      Some (e, DelayedExecution.with_memory cm next)) in Hlocal.
    apply collective_advance_view in Hstep as [_ [_ [participants [codes' [_ [_ [_ [-> _]]]]]]]].
    do 2 eexists. cbn [DelayedExecution.advance DelayedExecution.control]. now rewrite Hlocal.
Qed.

Theorem delayed_progress : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  DelayedExecution.execution input (DelayedExecution.initial programs) trace last ->
  DelayedExecution.finished last \/
    exists a e next, DelayedExecution.advance input a last = Some (e, next).
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Hweak.
  destruct (delayed_prefix_matches_sc _ _ _ _ _ _ Hrun Hdrf Hweak) as [sc [Hsc Haligned]].
  destruct (sso_progress _ _ _ _ _ _ Hrun Hdrf Hsc) as [Hdone|[a [e [next Hstep]]]].
  - pose proof (finished_equiv _ _ _ Haligned Hdone) as Hfinished.
    change (finished (DelayedExecution.control last)) in Hfinished.
    destruct (DelayedExecution.writes last) eqn:Hwrites.
    + left; split; assumption.
    + right. exists DelayedExecution.PublishFinal.
      apply Reference.finishedb_spec in Hfinished.
      do 2 eexists. cbn [DelayedExecution.advance]. now rewrite Hwrites, Hfinished.
  - right. destruct (buffered_action_available _ _ _ _ _ _ Haligned Hstep) as [f [final Hweakstep]].
    exists (DelayedExecution.Execute a), f, final. exact Hweakstep.
Qed.

Corollary delayed_maximal_agreement : forall programs input reference_trace reference_last trace last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  DelayedExecution.execution input (DelayedExecution.initial programs) trace last ->
  (forall a, DelayedExecution.advance input a last = None) ->
  DelayedExecution.finished last /\
  same_observations input reference_trace reference_last trace (DelayedExecution.control last) /\
  MemDRF trace.
Proof.
  intros programs input reference_trace reference_last trace last Hrun Hdrf Hweak Hstuck.
  destruct (delayed_progress _ _ _ _ _ _ Hrun Hdrf Hweak) as [Hdone|[a [e [next Hstep]]]].
  - split; [exact Hdone|]. eapply delayed_sso_agreement; eauto.
  - rewrite Hstuck in Hstep; discriminate.
Qed.
