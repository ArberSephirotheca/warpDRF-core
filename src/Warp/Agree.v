From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Commute.

Import ListNotations.

Definition action_eq_dec (a b : action) : {a = b} + {a <> b}.
Proof. decide equality; [apply Nat.eq_dec|apply instance_eq_dec]. Defined.

(* Move an enabled action to the front of a completed DRF execution. Each
   reordering preserves DRF; other schedules are not assumed to be DRF. *)
Lemma pull_enabled : forall input s trace last,
  execution input s trace last -> finished last -> MemDRF trace ->
  forall a, enabled input a s ->
  exists e s' tail final,
    advance input a s = Some (e, s') /\
    execution input s' tail final /\ finished final /\
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
      destruct (steps_swap_actions _ _ _ _ _ _ _ _ _ Hneq Hstep Hfirst Henabled Hreordered)
        as [s0' [s2' [Hfront [Hsecond [Hsame Hswap]]]]].
      destruct (execution_equiv _ _ _ _ Hrest _ Hsame) as [final' [Hrest' Hfinal]].
      exists f, s0', (emit_event e tail), final'.
      split; [exact Hfront|]. split; [econstructor; eauto|].
      split; [eapply finished_equiv; eauto|]. split.
      * eapply state_equiv_trans; eauto.
      * eapply reorders_trans; [apply reorders_emit; exact Horder|exact Hswap].
Qed.

Lemma finished_execution : forall input s trace last,
  finished s -> execution input s trace last -> trace = [] /\ last = s.
Proof.
  intros input s trace last Hdone Hexec. inversion Hexec; subst; auto.
  exfalso. eapply (finished_not_enabled input s a Hdone). eexists; eexists; eauto.
Qed.

Lemma emit_event_app : forall e trace rest,
  emit_event e (trace ++ rest) = emit_event e trace ++ rest.
Proof. intros [e|] trace rest; reflexivity. Qed.

(* Any execution, finished or not, matches the start of a completed DRF one:
   the target schedule supplies the next action, and pulling it to the front
   of the reference aligns the two executions one step at a time. The rest of
   the rearranged reference then completes the target run. *)
Theorem prefix_agreement : forall input s trace last,
  execution input s trace last ->
  forall reference_trace reference_last,
  execution input s reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  exists rest final,
    execution input last rest final /\ finished final /\
    state_equiv input reference_last final /\ reorders reference_trace (trace ++ rest).
Proof.
  intros input s trace last Htarget.
  induction Htarget as [s|a s e s' trace last Hstep Htarget IH];
    intros reference_trace reference_last Hreference Hrefdone Hdrf.
  - exists reference_trace, reference_last.
    split; [exact Hreference|]. split; [exact Hrefdone|].
    split; [apply state_equiv_refl|constructor].
  - assert (Henabled : enabled input a s) by (exists e, s'; exact Hstep).
    destruct (pull_enabled _ _ _ _ Hreference Hrefdone Hdrf a Henabled)
      as [f [next [tail [final [Hfront [Hrest [Hfinished [Hequiv Horder]]]]]]]].
    rewrite Hstep in Hfront. inversion Hfront; subst f next.
    assert (Htail : MemDRF tail).
    { apply memory_drf_emit_tail with (e := e).
      eapply reorders_memory_drf; eauto. }
    destruct (IH tail final Hrest Hfinished Htail)
      as [rest [final' [Hcomplete [Hdone [Hequiv' Horder']]]]].
    exists rest, final'. split; [exact Hcomplete|]. split; [exact Hdone|].
    split; [eapply state_equiv_trans; eauto|].
    rewrite <- emit_event_app.
    eapply reorders_trans; [exact Horder|now apply reorders_emit].
Qed.

(* A finished execution has nothing left to complete. *)
Corollary completed_agreement : forall input s trace last,
  execution input s trace last -> finished last ->
  forall reference_trace reference_last,
  execution input s reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  state_equiv input reference_last last /\ reorders reference_trace trace.
Proof.
  intros input s trace last Htarget Hdone reference_trace reference_last
    Hreference Hrefdone Hdrf.
  destruct (prefix_agreement _ _ _ _ Htarget _ _ Hreference Hrefdone Hdrf)
    as [rest [final [Hcomplete [_ [Hequiv Horder]]]]].
  destruct (finished_execution _ _ _ _ Hdone Hcomplete) as [-> ->].
  rewrite app_nil_r in Horder. split; assumption.
Qed.

(* The reference execution: run the lowest runnable thread; release an
   instance only when no thread can run. Loops can run forever, so the run
   takes a step budget. *)

Definition finishedb (st : state) :=
  forallb (fun c => match c with Skip | Return => true | _ => false end) (threads st).

Lemma finishedb_spec : forall st, finishedb st = true <-> finished st.
Proof.
  intros st. unfold finishedb, finished.
  rewrite forallb_forall, Forall_forall. split.
  - intros H c Hin. specialize (H c Hin). destruct c; try discriminate; auto.
  - intros H c Hin. now destruct (H c Hin) as [-> | ->].
Qed.

Definition waiting_instances (codes : list code) : list instance :=
  flat_map (fun c =>
    match at_collective c with Some (i, _, _) => [i] | None => [] end) codes.

Definition next input st :=
  find (fun a => match advance input a st with Some _ => true | None => false end)
    (map Thread (seq 0 (length (threads st))) ++
     map Release (waiting_instances (threads st))).

Lemma next_enabled : forall input st a,
  next input st = Some a -> exists e st', advance input a st = Some (e, st').
Proof.
  intros input st a Hnext. apply find_some in Hnext as [_ Hstep].
  destruct (advance input a st) as [[e st']|]; [eauto|discriminate].
Qed.

Fixpoint evaluate fuel input st : option (list event * state) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if finishedb st then Some ([], st) else
      match next input st with
      | Some a =>
          match advance input a st with
          | Some (e, st') =>
              match evaluate fuel' input st' with
              | Some (trace, last) => Some (emit_event e trace, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Lemma evaluate_sound : forall fuel input st trace last,
  evaluate fuel input st = Some (trace, last) ->
  execution input st trace last /\ finished last.
Proof.
  induction fuel as [|fuel IH]; intros input st trace last Hrun;
    cbn [evaluate] in Hrun; [discriminate|].
  destruct (finishedb st) eqn:Hdone.
  - inversion Hrun; subst. split; [constructor|now apply finishedb_spec].
  - destruct (next input st) as [a|]; try discriminate.
    destruct (advance input a st) as [[e st']|] eqn:Hstep; try discriminate.
    destruct (evaluate fuel input st') as [[events final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. apply IH in Hrest as [Hexec Hfinished].
    split; [econstructor; eauto|exact Hfinished].
Qed.

Fixpoint nodup_sites (l : list site) : bool :=
  match l with
  | [] => true
  | s :: rest => negb (existsb (site_eqb s) rest) && nodup_sites rest
  end.

Lemma nodup_sites_spec : forall l, nodup_sites l = true <-> NoDup l.
Proof.
  induction l as [|s rest IH]; cbn.
  - split; [constructor|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH, NoDup_cons_iff. split.
    + intros [Hnot Hnodup]. split; [|exact Hnodup].
      intros Hin. assert (Hex : existsb (site_eqb s) rest = true).
      { apply existsb_exists. exists s. split; [exact Hin|now apply site_eqb_true]. }
      congruence.
    + intros [Hnot Hnodup]. split; [|exact Hnodup].
      destruct (existsb (site_eqb s) rest) eqn:Hex; [|reflexivity].
      apply existsb_exists in Hex as [s' [Hin Heq]]. apply site_eqb_true in Heq.
      subst s'. contradiction.
Qed.

(* The collective sites of a program, each occurrence once; a loop body's
   sites are counted once, not once per iteration. *)
Fixpoint sites (c : code) : list site :=
  match c with
  | Prim n sync full _ _ _ body | Wait n sync full _ _ _ body =>
      Site n sync full :: sites body
  | Read _ _ body | Loop body | Local _ _ _ body => sites body
  | Seq first rest | Cond _ first rest => sites first ++ sites rest
  | Iter _ rest body => sites rest ++ sites body
  | Write _ _ | Break | Continue | Skip | Return => []
  end.

(* Source programs: Iter and Wait are runtime forms. *)
Fixpoint static (c : code) : bool :=
  match c with
  | Iter _ _ _ | Wait _ _ _ _ _ _ _ => false
  | Read _ _ body | Loop body | Prim _ _ _ _ _ _ body | Local _ _ _ body => static body
  | Seq first rest | Cond _ first rest => static first && static rest
  | Write _ _ | Break | Continue | Skip | Return => true
  end.

(* Distinct sites name distinct collectives: no thread's code names a site
   twice, so a site together with its iteration counts is one dynamic block. *)
Definition well_sited (programs : list code) :=
  Forall (fun c => static c = true /\ NoDup (sites c)) programs.

Definition run fuel input programs :=
  if forallb (fun c => static c && nodup_sites (sites c)) programs
  then evaluate fuel input (initial programs)
  else None.

Theorem run_sound : forall fuel input programs trace last,
  run fuel input programs = Some (trace, last) ->
  well_sited programs /\ execution input (initial programs) trace last /\ finished last.
Proof.
  intros fuel input programs trace last Hrun. unfold run in Hrun.
  destruct (forallb (fun c => static c && nodup_sites (sites c)) programs) eqn:Hsites;
    try discriminate.
  split; [|now apply evaluate_sound in Hrun].
  apply Forall_forall. intros c Hin. rewrite forallb_forall in Hsites.
  specialize (Hsites c Hin). apply andb_true_iff in Hsites as [Hstatic Hnodup].
  split; [exact Hstatic|now apply nodup_sites_spec].
Qed.

(* The contract. As in the paper, condition 2 checks the group of every
   instance in the reference execution. The full-warp configuration requires
   every executed collective to include the whole warp; the structured partial
   configuration also admits the partial groups the reference forms, except
   for a primitive that requires the whole warp (req(p) = full). *)

Inductive participation_config := FullWarp | StructuredPartial.

Definition UnambiguousParticipation c (programs : list code)
    (reference_trace : list event) :=
  forall i group, In (Sync i group) reference_trace ->
  group <> [] /\ NoDup group /\ Forall (fun tid => tid < length programs) group /\
  match c with
  | FullWarp => group = seq 0 (length programs)
  | StructuredPartial => site_full (fst i) = true -> group = seq 0 (length programs)
  end.

Definition conditions c programs reference_trace :=
  MemDRF reference_trace /\ UnambiguousParticipation c programs reference_trace.

Definition same_observations input reference_trace (reference_last : state)
    trace (last : state) :=
  (forall i, groups_at i reference_trace = groups_at i trace) /\
  (forall tid, read_history tid reference_trace = read_history tid trace) /\
  (forall address,
    load input (memory reference_last) address =
    load input (memory last) address).

(* Reference memory DRF alone suffices: the group of every instance is a
   conclusion. *)
Theorem agreement_from_drf : forall programs fuel input reference_trace reference_last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  forall trace last,
  execution input (initial programs) trace last -> finished last ->
  same_observations input reference_trace reference_last trace last.
Proof.
  intros programs fuel input reference_trace reference_last Hreference Hdrf
    trace last Htarget Hdone.
  apply run_sound in Hreference as [_ [Hreference Hrefdone]].
  destruct (completed_agreement _ _ _ _ Htarget Hdone
    _ _ Hreference Hrefdone Hdrf) as [[_ Hmemory] Horder].
  split; [now apply reorders_groups_at|].
  split; [now apply reorders_read_history|exact Hmemory].
Qed.

(* WarpDRF's guarantee for configuration c on a target whose completed runs
   are described by completed: every completed run of a kernel that meets
   both conditions has the reference's observations. *)
Definition Guarantee c
    (completed : (nat -> nat) -> list code -> list event -> state -> Prop) : Prop :=
  forall programs fuel input reference_trace reference_last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  conditions c programs reference_trace ->
  forall trace last, completed input programs trace last ->
  same_observations input reference_trace reference_last trace last.

(* A completed SSO run. *)
Definition sso_completed input programs trace last :=
  execution input (initial programs) trace last /\ finished last.

(* Theorem 1 of the paper for SSO, under either configuration. *)
Theorem sso_agreement : forall c, Guarantee c sso_completed.
Proof.
  intros c programs fuel input reference_trace reference_last Hreference [Hdrf _]
    trace last [Htarget Hdone].
  exact (agreement_from_drf _ _ _ _ _ Hreference Hdrf _ _ Htarget Hdone).
Qed.

Corollary target_memory_drf : forall programs fuel input reference_trace reference_last
    trace last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  execution input (initial programs) trace last -> finished last -> MemDRF trace.
Proof.
  intros programs fuel input reference_trace reference_last trace last Hreference Hdrf
    Htarget Hdone.
  apply run_sound in Hreference as [_ [Hreference Hrefdone]].
  destruct (completed_agreement _ _ _ _ Htarget Hdone
    _ _ Hreference Hrefdone Hdrf) as [_ Horder].
  eapply reorders_memory_drf; eauto.
Qed.

(* Every recorded group is nonempty, has no duplicates, and names threads of
   the warp. Steps keep the number of threads. *)
Lemma execution_groups_valid : forall input s trace last,
  execution input s trace last ->
  forall i group, In (Sync i group) trace ->
  group <> [] /\ NoDup group /\
  Forall (fun tid => tid < length (threads s)) group.
Proof.
  intros input s trace last Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; intros x group Hin;
    [contradiction|].
  destruct a as [tid|y].
  - apply thread_view in Hstep as [c [o [m' [c' [_ [_ [-> ->]]]]]]].
    cbn [threads] in IH. rewrite replace_thread_length in IH.
    destruct o as [o|]; cbn [emit_event option_map In] in Hin;
      [destruct Hin as [Hbad|Hin]; [discriminate|]|].
    all: eapply IH; exact Hin.
  - apply release_view in Hstep as [Harrived [_ [-> ->]]].
    cbn [threads] in IH. rewrite release_length in IH.
    cbn [emit_event In] in Hin. destruct Hin as [Heq|Hin]; [|eapply IH; exact Hin].
    inversion Heq; subst x group. split; [exact Harrived|].
    split; [apply select_nodup|].
    apply Forall_forall. intros tid Htid. eapply select_bound; exact Htid.
Qed.

(* A reference run passes the StructuredPartial check as soon as every
   primitive that requires the whole warp got it; the other groups the
   reference forms are always valid. *)
Theorem reference_structured_partial : forall programs fuel input reference_trace
    reference_last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  (forall i group, In (Sync i group) reference_trace -> site_full (fst i) = true ->
    group = seq 0 (length programs)) ->
  UnambiguousParticipation StructuredPartial programs reference_trace.
Proof.
  intros programs fuel input reference_trace reference_last Hreference Hfull i group Hin.
  pose proof (Hfull i group Hin) as Hgroup.
  apply run_sound in Hreference as [_ [Hreference _]].
  destruct (execution_groups_valid _ _ _ _ Hreference i group Hin)
    as [Hne [Hnodup Hbound]].
  repeat split; auto.
Qed.
