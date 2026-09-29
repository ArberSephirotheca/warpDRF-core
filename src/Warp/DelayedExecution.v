From Stdlib Require Import Lists.List Bool.Bool Lia.
From Faial.Core Require Import AVal.
From Faial.Core Require Mem.
From Faial.Warp Require Import Semantics Participation.
From Faial.Warp Require Delayed Reference.

Import ListNotations.

Record state := State {
  control : Participation.state;
  writes : list Delayed.write;
}.

Definition memory_of s := Delayed.State (memory (machine (control s))) (writes s).

Definition with_memory m c :=
  Participation.State (Semantics.State m (threads (machine c))) (decisions c) (participants c).

Definition pack c m := State (with_memory (Delayed.committed m) c) (Delayed.pending m).

Definition initial programs := State (Participation.initial programs) [].

Definition record_write e m :=
  match e with
  | Some (Memory o) =>
      match av_mode (access o) with
      | m_read => m
      | m_write => Delayed.store (av_owner (access o)) (av_index (access o)) (value o) m
      end
  | _ => m
  end.

Inductive action := Execute (a : Participation.action) | PublishFinal.

(* The control rules are unchanged. Ordinary instructions use the issuing
   thread's view, and synchronization publishes only the recorded group. *)
Definition advance input a s : option (option event * state) :=
  match a with
  | Execute (Thread tid) =>
      let m := memory_of s in
      match Participation.advance SSO input (Thread tid)
        (with_memory (Delayed.view tid m) (control s)) with
      | Some (e, next) => Some (e, pack next (record_write e m))
      | None => None
      end
  | Execute Collective =>
      match Participation.advance SSO input Collective (control s) with
      | Some (Some (Synchronize group), next) =>
          Some (Some (Synchronize group), pack next (Delayed.flush group (memory_of s)))
      | _ => None
      end
  | PublishFinal =>
      match writes s with
      | [] => None
      | _ :: _ => if Reference.finishedb (control s)
          then Some (None, pack (control s) (Delayed.finish (memory_of s))) else None
      end
  end.

Definition finished s := Participation.finished (control s) /\ writes s = [].

Inductive execution input : state -> list event -> state -> Prop :=
| execution_refl : forall s, execution input s [] s
| execution_step : forall a s e next trace last,
    advance input a s = Some (e, next) ->
    execution input next trace last ->
    execution input s (emit_event e trace) last.

Fixpoint run input schedule s : option (list event * state) :=
  match schedule with
  | [] => Some ([], s)
  | a :: rest =>
      match advance input a s with
      | Some (e, next) =>
          match run input rest next with
          | Some (trace, last) => Some (emit_event e trace, last)
          | None => None
          end
      | None => None
      end
  end.

Theorem run_sound : forall input schedule s trace last,
  run input schedule s = Some (trace, last) -> execution input s trace last.
Proof.
  intros input schedule. induction schedule as [|a rest IH]; intros s trace last Hrun;
    cbn in Hrun.
  - inversion Hrun; subst; constructor.
  - destruct (advance input a s) as [[e next]|] eqn:Hstep; try discriminate.
    destruct (run input rest next) as [[tail final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. econstructor; [exact Hstep|now apply IH].
Qed.

Theorem run_complete : forall input s trace last,
  execution input s trace last -> exists schedule, run input schedule s = Some (trace, last).
Proof.
  intros input s trace last Hexec. induction Hexec as [s|a s e next trace last Hstep Hexec IH].
  - exists []; reflexivity.
  - destruct IH as [rest Hrest]. exists (a :: rest). cbn. now rewrite Hstep, Hrest.
Qed.

Lemma ordinary_step_does_not_publish : forall input tid s e next,
  advance input (Execute (Thread tid)) s = Some (e, next) ->
  memory (machine (control next)) = memory (machine (control s)).
Proof.
  intros input tid s e next Hstep. cbn [advance] in Hstep.
  destruct (Participation.advance SSO input (Thread tid)
    (with_memory (Delayed.view tid (memory_of s)) (control s))) as [[ev c]|]; try discriminate.
  inversion Hstep; subst. destruct e as [[o|g]|]; cbn; auto.
  destruct (av_mode (access o)); reflexivity.
Qed.

Lemma collective_flushes_its_group : forall input s group next,
  advance input (Execute Collective) s = Some (Some (Synchronize group), next) ->
  memory_of next = Delayed.flush group (memory_of s).
Proof.
  intros input s group next Hstep. cbn [advance] in Hstep.
  destruct (Participation.advance SSO input Collective (control s)) as [[ev c]|];
    try discriminate. destruct ev as [[o|g]|]; try discriminate.
  inversion Hstep; subst. reflexivity.
Qed.

Lemma final_publication_requires_finished_threads : forall input s e next,
  advance input PublishFinal s = Some (e, next) ->
  Participation.finished (control s) /\ e = None /\ finished next.
Proof.
  intros input s e next Hstep. cbn [advance] in Hstep.
  destruct (writes s); try discriminate.
  destruct (Reference.finishedb (control s)) eqn:Hdone; try discriminate.
  inversion Hstep; subst. apply Reference.finishedb_spec in Hdone.
  split; [exact Hdone|]. split; [reflexivity|].
  split; [exact Hdone|reflexivity].
Qed.

Definition remaining s := 2 * Reference.remaining (control s) + length (writes s).

Lemma record_write_length : forall e m,
  length (Delayed.pending (record_write e m)) <= S (length (Delayed.pending m)).
Proof. intros [[o|g]|] m; cbn; try lia. destruct (av_mode (access o)); cbn; lia. Qed.

Lemma advance_decreases : forall input a s e next,
  advance input a s = Some (e, next) -> remaining next < remaining s.
Proof.
  intros input [act|] s e next Hstep.
  - destruct act as [tid|]; cbn [advance] in Hstep.
    + destruct (Participation.advance SSO input (Thread tid)
        (with_memory (Delayed.view tid (memory_of s)) (control s))) as [[ev c]|] eqn:Hlocal;
        try discriminate.
      pose proof (Reference.advance_decreases _ _ _ _ _ _ Hlocal) as Hsize.
      change (Reference.remaining c < Reference.remaining (control s)) in Hsize.
      inversion Hstep; subst e next.
      change (2 * Reference.remaining c + length (Delayed.pending (record_write ev (memory_of s))) <
        2 * Reference.remaining (control s) + length (writes s)).
      pose proof (record_write_length ev (memory_of s)) as Hlength.
      change (length (Delayed.pending (record_write ev (memory_of s))) <= S (length (writes s)))
        in Hlength. lia.
    + destruct (Participation.advance SSO input Collective (control s)) as [[ev c]|] eqn:Hlocal;
        try discriminate.
      pose proof (Reference.advance_decreases _ _ _ _ _ _ Hlocal) as Hsize.
      destruct ev as [[obs|group]|]; try discriminate. inversion Hstep; subst e next.
      change (2 * Reference.remaining c +
        length (filter (fun w => negb (Delayed.selected group w)) (writes s)) < remaining s).
      pose proof (filter_length_le (fun w => negb (Delayed.selected group w)) (writes s)).
      unfold remaining. lia.
  - cbn [advance] in Hstep. destruct (writes s) as [|w rest] eqn:Hwrites; try discriminate.
    destruct (Reference.finishedb (control s)); try discriminate. inversion Hstep; subst e next.
    change (2 * Reference.remaining (control s) + 0 < remaining s).
    unfold remaining. rewrite Hwrites. cbn. lia.
Qed.

Theorem no_infinite_execution : forall input (states : nat -> state) (actions : nat -> action),
  ~ (forall n, exists e, advance input (actions n) (states n) = Some (e, states (S n))).
Proof.
  intros input states actions Hsteps.
  assert (Hbound : forall n, n + remaining (states n) <= remaining (states 0)).
  { induction n; [lia|]. destruct (Hsteps n) as [e Hstep].
    pose proof (advance_decreases _ _ _ _ _ Hstep). lia. }
  specialize (Hbound (S (remaining (states 0)))). lia.
Qed.
