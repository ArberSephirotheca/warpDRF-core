From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Faial.Core Require Import NatUtil AVal.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Approx.D Require Lang Subst.

Import ListNotations.

Record observation := Observe {
  access : access_val;
  value : nat;
}.

Record state := State {
  memory : Mem.t;
  threads : list Lang.t;
}.

Definition initial (programs : list Lang.t) : state :=
  State Mem.empty programs.

Definition finished (s : state) : Prop :=
  Forall (fun code => code = Lang.Skip) (threads s).

Definition load (input : nat -> nat) (m : Mem.t) (address : nat) : nat :=
  match Map_NAT.find address m with
  | Some v => v
  | None => input address
  end.

Lemma load_matches_faial :
  forall input m address,
  Mem.MapsTo.t address (load input m address) m input.
Proof.
  intros input m address.
  unfold load.
  destruct (Map_NAT.find address m) eqn:Hfind.
  - apply Mem.MapsTo.defined.
    apply Map_NAT.find_2; assumption.
  - apply Mem.MapsTo.undefined.
    intros [v Hmaps].
    apply Map_NAT.find_1 in Hmaps.
    congruence.
Qed.

Lemma load_after_write :
  forall input m address v,
  load input (Map_NAT.add address v m) address = v.
Proof.
  intros.
  unfold load.
  rewrite Map_NAT_Facts.add_eq_o by reflexivity.
  reflexivity.
Qed.

(* Reads bind their results by substitution, as in Approx.D.LRun. *)
Fixpoint thread_step (tid : nat) (input : nat -> nat) (m : Mem.t)
    (code : Lang.t) : option (option observation * Mem.t * Lang.t) :=
  match code with
  | Lang.Read x address body =>
      match n_step tid address with
      | Some a =>
          let v := load input m a in
          Some (Some (Observe (av_read tid a) v), m,
                Subst.f x (NNum v) body)
      | None => None
      end
  | Lang.Write address contents =>
      match n_step tid address, n_step tid contents with
      | Some a, Some v =>
          Some (Some (Observe (av_write tid a) v),
                Map_NAT.add a v m, Lang.Skip)
      | _, _ => None
      end
  | Lang.Seq first rest =>
      match first with
      | Lang.Skip => Some (None, m, rest)
      | _ =>
          match thread_step tid input m first with
          | Some (event, m', first') =>
              Some (event, m', Lang.Seq first' rest)
          | None => None
          end
      end
  | Lang.Skip | Lang.Cond _ _ _ | Lang.Loop _ _ _ | Lang.Decl _ _ => None
  end.

Fixpoint replace_thread (tid : nat) (code : Lang.t) (programs : list Lang.t)
    : list Lang.t :=
  match tid, programs with
  | 0, _ :: rest => code :: rest
  | S tid', first :: rest => first :: replace_thread tid' code rest
  | _, [] => []
  end.

Definition advance (input : nat -> nat) (tid : nat) (s : state)
    : option (option observation * state) :=
  match nth_error (threads s) tid with
  | Some code =>
      match thread_step tid input (memory s) code with
      | Some (event, m', code') =>
          Some (event, State m' (replace_thread tid code' (threads s)))
      | None => None
      end
  | None => None
  end.

Definition emit (event : option observation) (trace : list observation) :=
  match event with
  | Some e => e :: trace
  | None => trace
  end.

(* Each step may select any thread that can advance. *)
Inductive execution (input : nat -> nat) : state -> list observation -> state -> Prop :=
| execution_refl :
    forall s, execution input s [] s
| execution_step :
    forall tid s event s' trace s'',
    advance input tid s = Some (event, s') ->
    execution input s' trace s'' ->
    execution input s (emit event trace) s''.

Fixpoint run (input : nat -> nat) (schedule : list nat) (s : state)
    : option (list observation * state) :=
  match schedule with
  | [] => Some ([], s)
  | tid :: rest =>
      match advance input tid s with
      | Some (event, s') =>
          match run input rest s' with
          | Some (trace, s'') => Some (emit event trace, s'')
          | None => None
          end
      | None => None
      end
  end.

Lemma run_sound :
  forall input schedule s trace s',
  run input schedule s = Some (trace, s') ->
  execution input s trace s'.
Proof.
  intros input schedule.
  induction schedule as [|tid rest IH]; intros s trace s' Hrun; simpl in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (advance input tid s) as [[event next]|] eqn:Hstep;
      try discriminate.
    destruct (run input rest next) as [[events last]|] eqn:Hrest;
      try discriminate.
    inversion Hrun; subst.
    econstructor.
    + exact Hstep.
    + eapply IH; exact Hrest.
Qed.

Lemma run_complete :
  forall input s trace s',
  execution input s trace s' ->
  exists schedule, run input schedule s = Some (trace, s').
Proof.
  intros input s trace s' Hexec.
  induction Hexec as [s|tid s event next trace last Hstep Hexec [schedule Hrun]].
  - exists []; reflexivity.
  - exists (tid :: schedule).
    simpl. rewrite Hstep, Hrun. reflexivity.
Qed.

Lemma replace_thread_length :
  forall programs tid code,
  length (replace_thread tid code programs) = length programs.
Proof.
  induction programs as [|first rest IH]; intros [|tid] code; simpl; auto.
Qed.

Lemma replace_thread_other :
  forall programs tid other code,
  other <> tid ->
  nth_error (replace_thread tid code programs) other = nth_error programs other.
Proof.
  induction programs as [|first rest IH]; intros tid other code Hneq.
  - destruct tid, other; reflexivity.
  - destruct tid, other; simpl.
    + contradiction.
    + reflexivity.
    + reflexivity.
    + apply IH. intros Heq. apply Hneq. now f_equal.
Qed.

Lemma advance_preserves_thread_count :
  forall input tid s event s',
  advance input tid s = Some (event, s') ->
  length (threads s') = length (threads s).
Proof.
  intros input tid [m programs] event s' Hstep.
  unfold advance in Hstep; simpl in Hstep.
  destruct (nth_error programs tid) as [code|]; try discriminate.
  destruct (thread_step tid input m code) as [[[e m'] code']|]; try discriminate.
  inversion Hstep; subst. simpl. apply replace_thread_length.
Qed.

Lemma advance_preserves_other_threads :
  forall input tid s event s' other,
  advance input tid s = Some (event, s') ->
  other <> tid ->
  nth_error (threads s') other = nth_error (threads s) other.
Proof.
  intros input tid [m programs] event s' other Hstep Hneq.
  unfold advance in Hstep; simpl in Hstep.
  destruct (nth_error programs tid) as [code|]; try discriminate.
  destruct (thread_step tid input m code) as [[[e m'] code']|]; try discriminate.
  inversion Hstep; subst. simpl. now apply replace_thread_other.
Qed.

Lemma finished_cannot_advance :
  forall input s tid,
  finished s -> advance input tid s = None.
Proof.
  intros input [m programs] tid Hfinished.
  unfold finished in Hfinished; simpl in Hfinished.
  unfold advance; simpl.
  destruct (nth_error programs tid) as [code|] eqn:Hcode; auto.
  apply nth_error_In in Hcode.
  rewrite Forall_forall in Hfinished.
  specialize (Hfinished code Hcode). subst code. reflexivity.
Qed.
