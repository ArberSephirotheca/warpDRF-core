From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Faial.Core Require Import NatUtil AVal.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Lang.

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

Fixpoint thread_step (tid : nat) (input : nat -> nat) (m : Mem.t)
    (code : Lang.t) : option (option observation * Mem.t * Lang.t) :=
  match code with
  | Lang.Read x address body =>
      match n_step tid address with
      | Some a =>
          let v := load input m a in
          Some (Some (Observe (av_read tid a) v), m,
                Lang.subst x (NNum v) body)
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
  | Lang.Cond test yes no =>
      match b_step tid test with
      | Some b => Some (None, m, if b then yes else no)
      | None => None
      end
  | Lang.Skip | Lang.Barrier _ | Lang.AddZero => None
  end.

Fixpoint replace_thread (tid : nat) (code : Lang.t) (programs : list Lang.t)
    : list Lang.t :=
  match tid, programs with
  | 0, _ :: rest => code :: rest
  | S tid', first :: rest => first :: replace_thread tid' code rest
  | _, [] => []
  end.

(* Reaching a barrier does not execute it; the entire warp must be ready. *)
Fixpoint at_barrier (code : Lang.t) : option (nat * Lang.t) :=
  match code with
  | Lang.Barrier site => Some (site, Lang.Skip)
  | Lang.Seq first rest =>
      match at_barrier first with
      | Some (site, first') => Some (site, Lang.Seq first' rest)
      | None => None
      end
  | _ => None
  end.

Fixpoint release (site : nat) (programs : list Lang.t) : option (list Lang.t) :=
  match programs with
  | [] => Some []
  | code :: rest =>
      match at_barrier code, release site rest with
      | Some (site', code'), Some rest' =>
          if Nat.eqb site site' then Some (code' :: rest') else None
      | _, _ => None
      end
  end.

Definition synchronize (width warp : nat) (s : state) : option state :=
  let start := warp * width in
  let group := firstn width (skipn start (threads s)) in
  match width, group with
  | S _, first :: _ =>
      match at_barrier first with
      | Some (site, _) =>
          if Nat.eqb (length group) width then
            match release site group with
            | Some group' =>
                Some (State (memory s)
                  (firstn start (threads s) ++ group' ++
                   skipn (start + width) (threads s)))
            | None => None
            end
          else None
      | None => None
      end
  | _, _ => None
  end.

Inductive action := Thread (tid : nat) | Sync (warp : nat).

Definition advance (width : nat) (input : nat -> nat) (a : action) (s : state)
    : option (option observation * state) :=
  match a with
  | Sync warp =>
      match synchronize width warp s with
      | Some s' => Some (None, s')
      | None => None
      end
  | Thread tid =>
      match nth_error (threads s) tid with
      | Some code =>
          match thread_step tid input (memory s) code with
          | Some (event, m', code') =>
              Some (event, State m' (replace_thread tid code' (threads s)))
          | None => None
          end
      | None => None
      end
  end.

Definition emit (event : option observation) (trace : list observation) :=
  match event with
  | Some e => e :: trace
  | None => trace
  end.

(* Ordinary instructions interleave; a barrier releases one complete warp. *)
Inductive execution (width : nat) (input : nat -> nat)
    : state -> list observation -> state -> Prop :=
| execution_refl :
    forall s, execution width input s [] s
| execution_step :
    forall a s event s' trace s'',
    advance width input a s = Some (event, s') ->
    execution width input s' trace s'' ->
    execution width input s (emit event trace) s''.

Fixpoint run (width : nat) (input : nat -> nat) (schedule : list action) (s : state)
    : option (list observation * state) :=
  match schedule with
  | [] => Some ([], s)
  | a :: rest =>
      match advance width input a s with
      | Some (event, s') =>
          match run width input rest s' with
          | Some (trace, s'') => Some (emit event trace, s'')
          | None => None
          end
      | None => None
      end
  end.

Lemma run_sound :
  forall width input schedule s trace s',
  run width input schedule s = Some (trace, s') ->
  execution width input s trace s'.
Proof.
  intros width input schedule.
  induction schedule as [|a rest IH]; intros s trace s' Hrun; simpl in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (advance width input a s) as [[event next]|] eqn:Hstep;
      try discriminate.
    destruct (run width input rest next) as [[events last]|] eqn:Hrest;
      try discriminate.
    inversion Hrun; subst.
    econstructor.
    + exact Hstep.
    + eapply IH; exact Hrest.
Qed.

Lemma run_complete :
  forall width input s trace s',
  execution width input s trace s' ->
  exists schedule, run width input schedule s = Some (trace, s').
Proof.
  intros width input s trace s' Hexec.
  induction Hexec as [s|a s event next trace last Hstep Hexec [schedule Hrun]].
  - exists []; reflexivity.
  - exists (a :: schedule).
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

Lemma thread_preserves_thread_count :
  forall width input tid s event s',
  advance width input (Thread tid) s = Some (event, s') ->
  length (threads s') = length (threads s).
Proof.
  intros width input tid [m programs] event s' Hstep.
  unfold advance in Hstep; simpl in Hstep.
  destruct (nth_error programs tid) as [code|]; try discriminate.
  destruct (thread_step tid input m code) as [[[e m'] code']|]; try discriminate.
  inversion Hstep; subst. simpl. apply replace_thread_length.
Qed.

Lemma thread_preserves_other_threads :
  forall width input tid s event s' other,
  advance width input (Thread tid) s = Some (event, s') ->
  other <> tid ->
  nth_error (threads s') other = nth_error (threads s) other.
Proof.
  intros width input tid [m programs] event s' other Hstep Hneq.
  unfold advance in Hstep; simpl in Hstep.
  destruct (nth_error programs tid) as [code|]; try discriminate.
  destruct (thread_step tid input m code) as [[[e m'] code']|]; try discriminate.
  inversion Hstep; subst. simpl. now apply replace_thread_other.
Qed.

Lemma finished_thread_cannot_advance :
  forall width input s tid,
  finished s -> advance width input (Thread tid) s = None.
Proof.
  intros width input [m programs] tid Hfinished.
  unfold finished in Hfinished; simpl in Hfinished.
  unfold advance; simpl.
  destruct (nth_error programs tid) as [code|] eqn:Hcode; auto.
  apply nth_error_In in Hcode.
  rewrite Forall_forall in Hfinished.
  specialize (Hfinished code Hcode). subst code. reflexivity.
Qed.

Lemma release_length :
  forall site programs programs',
  release site programs = Some programs' -> length programs' = length programs.
Proof.
  intros site programs.
  induction programs as [|code rest IH]; intros programs' Hrelease; simpl in Hrelease.
  - inversion Hrelease; reflexivity.
  - destruct (at_barrier code) as [[site' code']|]; try discriminate.
    destruct (release site rest) as [rest'|] eqn:Hrest; try discriminate.
    destruct (Nat.eqb site site'); try discriminate.
    inversion Hrelease; subst. simpl. f_equal. now apply IH.
Qed.

Lemma release_participants :
  forall site programs programs',
  release site programs = Some programs' ->
  Forall2 (fun code code' => at_barrier code = Some (site, code')) programs programs'.
Proof.
  intros site programs.
  induction programs as [|code rest IH]; intros programs' Hrelease; simpl in Hrelease.
  - inversion Hrelease; constructor.
  - destruct (at_barrier code) as [[site' code']|] eqn:Hcode; try discriminate.
    destruct (release site rest) as [rest'|] eqn:Hrest; try discriminate.
    destruct (Nat.eqb site site') eqn:Hsite; try discriminate.
    apply Nat.eqb_eq in Hsite. subst site'.
    inversion Hrelease; subst. constructor; auto.
Qed.

Lemma synchronize_spec :
  forall width warp s s',
  synchronize width warp s = Some s' ->
  width <> 0 /\ exists site group',
  length group' = width /\
  Forall2 (fun code code' => at_barrier code = Some (site, code'))
    (firstn width (skipn (warp * width) (threads s))) group' /\
  threads s' = firstn (warp * width) (threads s) ++ group' ++
    skipn (warp * width + width) (threads s) /\
  memory s' = memory s.
Proof.
  intros [|width] warp s s' Hsync; [discriminate|].
  unfold synchronize in Hsync.
  destruct (firstn (S width) (skipn (warp * S width) (threads s)))
    as [|first rest] eqn:Hgroup; try discriminate.
  destruct (at_barrier first) as [[site next]|]; try discriminate.
  destruct (Nat.eqb (length (first :: rest)) (S width)) eqn:Hlength;
    try discriminate.
  apply Nat.eqb_eq in Hlength.
  destruct (release site (first :: rest)) as [group'|] eqn:Hrelease;
    try discriminate.
  inversion Hsync; subst.
  split; [discriminate|]. exists site, group'.
  split; [rewrite (release_length _ _ _ Hrelease); exact Hlength|].
  split; [now apply release_participants in Hrelease|].
  split; reflexivity.
Qed.

Lemma synchronize_preserves_memory :
  forall width warp s s',
  synchronize width warp s = Some s' -> memory s' = memory s.
Proof.
  intros width warp s s' Hsync.
  apply synchronize_spec in Hsync as [_ [site [group' [_ [_ [_ Hmemory]]]]]].
  exact Hmemory.
Qed.

Lemma synchronize_preserves_thread_count :
  forall width warp s s',
  synchronize width warp s = Some s' -> length (threads s') = length (threads s).
Proof.
  intros width warp s s' Hsync.
  apply synchronize_spec in Hsync as [_ [site [group' [_ [Hgroup [Hthreads _]]]]]].
  apply Forall2_length in Hgroup.
  rewrite Hthreads, !length_app, <- Hgroup.
  pose proof (f_equal (@length Lang.t)
    (firstn_skipn (warp * width) (threads s))) as Houter.
  pose proof (f_equal (@length Lang.t)
    (firstn_skipn width (skipn (warp * width) (threads s)))) as Hinner.
  rewrite length_app in Houter, Hinner.
  rewrite skipn_skipn, (Nat.add_comm width (warp * width)) in Hinner.
  rewrite <- Houter, <- Hinner. reflexivity.
Qed.
