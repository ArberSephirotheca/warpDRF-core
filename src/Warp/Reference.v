From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import Var.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation.
From Faial.Warp Require Lang.

Import ListNotations.

Fixpoint ordinary (code : Lang.t) : bool :=
  match code with
  | Lang.Read _ _ body => ordinary body
  | Lang.Write _ _ | Lang.Skip => true
  | Lang.Seq first rest => ordinary first && ordinary rest
  | _ => false
  end.

(* Exactly one collective, with ordinary computation before and after it. *)
Fixpoint collective_body (code : Lang.t) : bool :=
  match code with
  | Lang.AddZero => true
  | Lang.Read _ _ body => collective_body body
  | Lang.Seq first rest =>
      (ordinary first && collective_body rest) ||
      (collective_body first && ordinary rest)
  | _ => false
  end.

(* Exactly one branch decision; only its true branch contains a collective. *)
Fixpoint supported_thread (code : Lang.t) : bool :=
  match code with
  | Lang.Cond _ yes no => collective_body yes && ordinary no
  | Lang.Read _ _ body => supported_thread body
  | Lang.Seq first rest =>
      (ordinary first && supported_thread rest) ||
      (supported_thread first && ordinary rest)
  | _ => false
  end.

Definition supported (programs : list Lang.t) : bool :=
  match programs with [] => false | _ => forallb supported_thread programs end.

(* Every successful step consumes syntax. Substitution does not change size. *)
Fixpoint size (code : Lang.t) : nat :=
  match code with
  | Lang.Skip => 0
  | Lang.Read _ _ body => S (size body)
  | Lang.Seq first rest | Lang.Cond _ first rest => S (size first + size rest)
  | _ => 1
  end.

Definition program_size (programs : list Lang.t) :=
  fold_right (fun code n => size code + n) 0 programs.

Definition remaining (s : state) := program_size (threads (machine s)).

Lemma size_subst : forall code x value,
  size (Lang.subst x value code) = size code.
Proof.
  induction code; intros x value; cbn; try congruence.
  destruct (Var.VAR.eq_dec x v); cbn; auto.
Qed.

Lemma thread_step_decreases : forall code tid input m event m' code',
  thread_step tid input m code = Some (event, m', code') -> size code' < size code.
Proof.
  induction code; intros tid input m event m' code' Hstep; cbn in Hstep;
    try discriminate.
  - destruct (n_step tid n) eqn:Haddress; try discriminate.
    inversion Hstep; subst. cbn. rewrite size_subst. lia.
  - destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion Hstep; subst. cbn. lia.
  - destruct code1; cbn -[thread_step] in Hstep.
    all: try solve [inversion Hstep; subst; cbn; lia].
    all: match type of Hstep with
    | context [thread_step ?owner ?base ?mem ?first] =>
        destruct (thread_step owner base mem first)
          as [[[e next_mem] next_code]|] eqn:Hfirst; try discriminate;
        inversion Hstep; subst;
        specialize (IHcode1 _ _ _ _ _ _ Hfirst); cbn in *; lia
    end.
  - destruct (b_step tid b); try discriminate.
    inversion Hstep; subst. destruct b0; cbn; lia.
Qed.

Lemma replace_thread_decreases : forall programs tid code code',
  nth_error programs tid = Some code -> size code' < size code ->
  program_size (replace_thread tid code' programs) < program_size programs.
Proof.
  induction programs as [|first rest IH]; intros [|tid] code code' Hcode Hsize;
    cbn in Hcode; try discriminate.
  - inversion Hcode; subst. cbn. lia.
  - specialize (IH tid code code' Hcode Hsize). unfold program_size in *. cbn. lia.
Qed.

Lemma at_collective_decreases : forall code code',
  at_add_zero code = Some code' -> size code' < size code.
Proof.
  induction code; intros code' Hstep; cbn in Hstep; try discriminate.
  - destruct (at_add_zero code1) eqn:Hfirst; try discriminate.
    inversion Hstep; subst. specialize (IHcode1 _ eq_refl). cbn. lia.
  - inversion Hstep; subst. cbn. lia.
Qed.

Lemma release_collective_decreases : forall ds programs programs',
  release_collective ds programs = Some programs' ->
  program_size programs' <= program_size programs /\
  (In Entered ds -> program_size programs' < program_size programs).
Proof.
  induction ds as [|d ds IH]; intros [|code rest] programs' Hrelease;
    cbn in Hrelease; try discriminate.
  - inversion Hrelease; subst. cbn. split; [lia|contradiction].
  - destruct (release_collective ds rest) as [rest'|] eqn:Hrest; try discriminate.
    specialize (IH _ _ Hrest). destruct IH as [Hle Hlt].
    unfold program_size in *.
    destruct d.
    + inversion Hrelease; subst. cbn. split; [lia|].
      intros [Hbad|Hin]; [discriminate|]. specialize (Hlt Hin). lia.
    + destruct (at_add_zero code) as [code'|] eqn:Hcode; try discriminate.
      apply at_collective_decreases in Hcode.
      inversion Hrelease; subst. cbn. split; [lia|intros; lia].
    + inversion Hrelease; subst. cbn. split; [lia|].
      intros [Hbad|Hin]; [discriminate|]. specialize (Hlt Hin). lia.
Qed.

Lemma advance_decreases : forall p input a s event s',
  advance p input a s = Some (event, s') -> remaining s' < remaining s.
Proof.
  intros p input [tid|] [core ds group] event s' Hstep.
  - cbn [advance machine decisions participants] in Hstep.
    destruct (nth_error (threads core) tid) as [code|] eqn:Hcode; try discriminate.
    destruct (branch_decision tid code) as [b|];
      [destruct (nth_error ds tid) as [[]|];
        destruct group; destruct b; try discriminate|].
    all: destruct (thread_step tid input (memory core) code)
      as [[[e m'] code']|] eqn:Hthread; try discriminate.
    all: inversion Hstep; subst; unfold remaining; cbn;
      eapply replace_thread_decreases; [exact Hcode|];
      eapply thread_step_decreases; exact Hthread.
  - cbn [advance machine decisions participants] in Hstep.
    destruct group; try discriminate.
    destruct (entered_threads ds) as [|tid rest] eqn:Hgroup; try discriminate.
    destruct (match p with SSO => all_decided ds | Spec => true end); try discriminate.
    destruct (release_collective ds (threads core)) as [programs'|] eqn:Hrelease;
      try discriminate.
    inversion Hstep; subst. unfold remaining; cbn.
    apply release_collective_decreases in Hrelease as [_ Hlt]. apply Hlt.
    assert (Hin : In tid (entered_threads ds)) by (rewrite Hgroup; cbn; auto).
    unfold entered_threads in Hin. apply filter_In in Hin as [_ Hin].
    destruct (nth_error ds tid) as [[]|] eqn:Hdecision; try discriminate.
    now apply nth_error_In in Hdecision.
Qed.

Definition finishedb s :=
  forallb (fun code => match code with Lang.Skip => true | _ => false end)
    (threads (machine s)) && all_decided (decisions s).

Lemma finishedb_spec : forall s, finishedb s = true <-> finished s.
Proof.
  intros s. unfold finishedb, finished, Semantics.finished.
  rewrite andb_true_iff, forallb_forall, Forall_forall.
  split; intros [Hcodes Hdecided]; split; try assumption.
  - intros code Hin. specialize (Hcodes code Hin). destruct code; congruence.
  - intros code Hin. specialize (Hcodes code Hin). now subst code.
Qed.

(* Retry the lowest runnable thread until it waits or finishes. *)
Definition next input s :=
  find (fun a => match advance SSO input a s with Some _ => true | None => false end)
    (map Thread (seq 0 (length (threads (machine s)))) ++ [Collective]).

Lemma next_enabled : forall input s a,
  next input s = Some a -> exists event s', advance SSO input a s = Some (event, s').
Proof.
  intros input s a Hnext. apply find_some in Hnext as [_ Hstep].
  destruct (advance SSO input a s) as [[event s']|]; [eauto|discriminate].
Qed.

Lemma next_none_stuck : forall input s,
  next input s = None -> forall a, advance SSO input a s = None.
Proof.
  intros input s Hnext a. unfold next in Hnext.
  destruct (advance SSO input a s) as [[event s']|] eqn:Hstep; [|reflexivity].
  exfalso.
  assert (Hin : In a
    (map Thread (seq 0 (length (threads (machine s)))) ++ [Collective])).
  { destruct a as [tid|].
    - apply in_or_app; left. apply in_map. apply in_seq. split; [lia|].
      cbn [advance] in Hstep.
      destruct (nth_error (threads (machine s)) tid) as [code|] eqn:Hcode;
        try discriminate.
      apply (proj1 (nth_error_Some (threads (machine s)) tid)).
      rewrite Hcode. discriminate.
    - apply in_or_app; right. cbn; auto. }
  pose proof (find_none _ _ Hnext a Hin) as Hdisabled.
  cbv beta in Hdisabled. rewrite Hstep in Hdisabled. discriminate.
Qed.

Fixpoint evaluate fuel input s : option (list event * state) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if finishedb s then Some ([], s) else
      match next input s with
      | Some a =>
          match advance SSO input a s with
          | Some (event, s') =>
              match evaluate fuel' input s' with
              | Some (trace, last) => Some (emit_event event trace, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Definition run input programs :=
  if supported programs then
    evaluate (S (program_size programs)) input (initial programs)
  else None.

Lemma evaluate_sound : forall fuel input s trace last,
  evaluate fuel input s = Some (trace, last) ->
  execution SSO input s trace last /\ finished last.
Proof.
  induction fuel as [|fuel IH]; intros input s trace last Hrun;
    cbn [evaluate] in Hrun; [discriminate|].
  destruct (finishedb s) eqn:Hdone.
  - inversion Hrun; subst. split; [constructor|now apply finishedb_spec].
  - destruct (next input s) as [a|]; try discriminate.
    destruct (advance SSO input a s) as [[event s']|] eqn:Hstep; try discriminate.
    destruct (evaluate fuel input s') as [[events final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. apply IH in Hrest as [Hexec Hfinished].
    split; [econstructor; eauto|exact Hfinished].
Qed.

Theorem run_sound : forall input programs trace last,
  run input programs = Some (trace, last) ->
  supported programs = true /\
  execution SSO input (initial programs) trace last /\ finished last.
Proof.
  intros input programs trace last Hrun. unfold run in Hrun.
  destruct (supported programs) eqn:Hsupported; try discriminate.
  split; [reflexivity|]. now apply evaluate_sound in Hrun.
Qed.

(* The syntax-derived fuel cannot run out: failure reaches an unfinished state
   in which no action can be selected, rather than silently truncating a run. *)
Lemma evaluate_failure : forall fuel input s,
  remaining s < fuel -> evaluate fuel input s = None ->
  exists trace last, execution SSO input s trace last /\
    ~ finished last /\ next input last = None.
Proof.
  induction fuel as [|fuel IH]; intros input s Hbound Hrun; [lia|].
  cbn [evaluate] in Hrun.
  destruct (finishedb s) eqn:Hdone; try discriminate.
  destruct (next input s) as [a|] eqn:Hnext.
  - destruct (next_enabled _ _ _ Hnext) as [event [s' Hstep]].
    rewrite Hstep in Hrun.
    destruct (evaluate fuel input s') as [[events last]|] eqn:Hrest; try discriminate.
    pose proof (advance_decreases _ _ _ _ _ _ Hstep) as Hsmaller.
    destruct (IH input s') as [trace [last [Hexec Hstuck]]]; try lia; try assumption.
    exists (emit_event event trace), last. split; [econstructor; eauto|exact Hstuck].
  - exists [], s. split; [constructor|]. split; [|exact Hnext].
    intros Hfinished. apply finishedb_spec in Hfinished. congruence.
Qed.

Theorem run_failure : forall input programs,
  supported programs = true -> run input programs = None ->
  exists trace last, execution SSO input (initial programs) trace last /\
    ~ finished last /\ (forall a, advance SSO input a last = None).
Proof.
  intros input programs Hsupported Hrun. unfold run in Hrun. rewrite Hsupported in Hrun.
  assert (Hbound : remaining (initial programs) < S (program_size programs)).
  { change (program_size programs < S (program_size programs)). lia. }
  destruct (evaluate_failure _ _ _ Hbound Hrun)
    as [trace [last [Hexec [Hunfinished Hnext]]]].
  exists trace, last. repeat split; auto using next_none_stuck.
Qed.
