From Stdlib Require Import Lists.List Arith.PeanoNat.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics.
From Faial.Warp Require Lang.

Import ListNotations.

(* One warp, one conditional per thread, and one collective in its true branch.
   AddZero represents subgroupAdd(0) with its unused, necessarily zero result.
   Both policies give it memory ordering among its recorded participants.
   This bounded model does not identify repeated or nested dynamic blocks. *)
Inductive policy := SSO | Spec.
Inductive decision := Unresolved | Entered | Skipped.

Record state := State {
  machine : Semantics.state;
  decisions : list decision;
  participants : option (list nat);
}.

Definition initial programs :=
  State (Semantics.initial programs)
    (repeat Unresolved (length programs)) None.

Definition all_decided ds :=
  forallb (fun d => match d with Unresolved => false | _ => true end) ds.

Definition finished s :=
  Semantics.finished (machine s) /\ all_decided (decisions s) = true.

(* Observe the decision made by the ordinary conditional transition. *)
Fixpoint branch_decision tid code : option bool :=
  match code with
  | Lang.Cond test _ _ => b_step tid test
  | Lang.Seq first _ => branch_decision tid first
  | _ => None
  end.

Fixpoint at_add_zero code : option Lang.t :=
  match code with
  | Lang.AddZero => Some Lang.Skip
  | Lang.Seq first rest =>
      match at_add_zero first with
      | Some first' => Some (Lang.Seq first' rest)
      | None => None
      end
  | _ => None
  end.

Definition entered_threads ds :=
  filter (fun tid =>
    match nth_error ds tid with Some Entered => true | _ => false end)
    (seq 0 (length ds)).

(* Known participants must all arrive. Unknown threads are left untouched. *)
Fixpoint release_collective ds programs : option (list Lang.t) :=
  match ds, programs with
  | [], [] => Some []
  | d :: ds', code :: rest =>
      match release_collective ds' rest with
      | Some rest' =>
          match d with
          | Entered =>
              match at_add_zero code with
              | Some code' => Some (code' :: rest')
              | None => None
              end
          | _ => Some (code :: rest')
          end
      | None => None
      end
  | _, _ => None
  end.

Inductive action := Thread (tid : nat) | Collective.

Inductive event := Memory (access : observation) | Synchronize (group : list nat).

Fixpoint memory_events (trace : list event) : list observation :=
  match trace with
  | [] => []
  | Memory e :: rest => e :: memory_events rest
  | Synchronize _ :: rest => memory_events rest
  end.

Definition emit_event (e : option event) (trace : list event) :=
  match e with Some e' => e' :: trace | None => trace end.

Definition advance (p : policy) input a s : option (option event * state) :=
  match a with
  | Thread tid =>
      let core := machine s in
      match nth_error (threads core) tid with
      | Some code =>
          let ds :=
            match branch_decision tid code with
            | None => Some (decisions s)
            | Some b =>
                match nth_error (decisions s) tid, participants s, b with
                | Some Unresolved, None, _
                | Some Unresolved, Some _, false =>
                    Some (firstn tid (decisions s) ++
                      [if b then Entered else Skipped] ++
                      skipn (S tid) (decisions s))
                | _, _, _ => None
                end
            end in
          match ds with
          | Some ds' =>
              match thread_step tid input (memory core) code with
              | Some (event, m', code') =>
                  Some (option_map Memory event,
                    State (Semantics.State m' (replace_thread tid code' (threads core)))
                      ds' (participants s))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | Collective =>
      match participants s, entered_threads (decisions s) with
      | None, (_ :: _) as group =>
          if match p with SSO => all_decided (decisions s) | Spec => true end then
            match release_collective (decisions s) (threads (machine s)) with
            | Some programs =>
                Some (Some (Synchronize group),
                  State (Semantics.State (memory (machine s)) programs)
                  (decisions s) (Some group))
            | None => None
            end
          else None
      | _, _ => None
      end
  end.

Inductive execution p input : state -> list event -> state -> Prop :=
| execution_refl : forall s, execution p input s [] s
| execution_step : forall a s event s' trace last,
    advance p input a s = Some (event, s') ->
    execution p input s' trace last ->
    execution p input s (emit_event event trace) last.

Fixpoint run p input schedule s : option (list event * state) :=
  match schedule with
  | [] => Some ([], s)
  | a :: rest =>
      match advance p input a s with
      | Some (event, s') =>
          match run p input rest s' with
          | Some (trace, last) => Some (emit_event event trace, last)
          | None => None
          end
      | None => None
      end
  end.

Lemma run_sound : forall p input schedule s trace last,
  run p input schedule s = Some (trace, last) -> execution p input s trace last.
Proof.
  intros p input schedule.
  induction schedule as [|a rest IH]; intros s trace last Hrun; simpl in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (advance p input a s) as [[event next]|] eqn:Hstep; try discriminate.
    destruct (run p input rest next) as [[events final]|] eqn:Hrest;
      try discriminate.
    inversion Hrun; subst. econstructor; [exact Hstep|now apply IH].
Qed.

Lemma run_complete : forall p input s trace last,
  execution p input s trace last ->
  exists schedule, run p input schedule s = Some (trace, last).
Proof.
  intros p input s trace last Hexec.
  induction Hexec as [s|a s event next trace last Hstep Hexec [schedule Hrun]].
  - exists []; reflexivity.
  - exists (a :: schedule). simpl. rewrite Hstep, Hrun. reflexivity.
Qed.

Lemma collective_preserves_memory : forall p input s event s',
  advance p input Collective s = Some (event, s') ->
  event = option_map Synchronize (participants s') /\
  memory (machine s') = memory (machine s).
Proof.
  intros p input s event s' Hstep.
  unfold advance in Hstep.
  destruct (participants s); try discriminate.
  destruct (entered_threads (decisions s)); try discriminate.
  destruct (match p with SSO => all_decided (decisions s) | Spec => true end);
    try discriminate.
  destruct (release_collective (decisions s) (threads (machine s)));
    try discriminate.
  inversion Hstep; subst. split; reflexivity.
Qed.

Lemma late_participant_rejected : forall p input s group tid code,
  participants s = Some group ->
  nth_error (threads (machine s)) tid = Some code ->
  branch_decision tid code = Some true ->
  advance p input (Thread tid) s = None.
Proof.
  intros p input s group tid code Hgroup Hcode Hbranch.
  unfold advance. rewrite Hcode, Hbranch, Hgroup.
  destruct (nth_error (decisions s) tid) as [[]|]; reflexivity.
Qed.
