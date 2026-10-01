From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import Var.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code.

Import ListNotations.

(* The SSO model of one warp. A collective's dynamic block, its instance, is
   its site together with the iteration counts of the loops around it,
   outermost first. A collective after a loop drops that loop's count, so
   threads leaving the loop in different iterations meet there.

   The unknown set is computed from the code. reach c s v says whether a
   thread with remaining code c may still execute site s at iteration vector
   v: inside iteration k it may reach k :: v' through the rest of the
   iteration, and any j > k through the loop body. Steps only shrink reach,
   so a thread that has left an instance behind never comes back to it. *)

(* A site names one primitive in the code by its label, and records whether
   the primitive orders memory and whether it requires the whole warp. *)
Inductive site := Site (n : nat) (sync full : bool).

Definition site_eq_dec (a b : site) : {a = b} + {a <> b}.
Proof. decide equality; first [apply Nat.eq_dec|apply Bool.bool_dec]. Defined.

Definition site_sync (s : site) : bool := match s with Site _ sync _ => sync end.
Definition site_full (s : site) : bool := match s with Site _ _ full => full end.

(* The sites of Barrier n and AddZero n. *)
Definition BarrierSite (n : nat) : site := Site n true false.
Definition AddSite (n : nat) : site := Site n true false.

Definition site_eqb (a b : site) : bool := if site_eq_dec a b then true else false.

Lemma site_eqb_true : forall a b, site_eqb a b = true <-> a = b.
Proof. intros a b. unfold site_eqb. destruct (site_eq_dec a b); split; congruence. Qed.

Definition instance := (site * list nat)%type.

Definition instance_eq_dec (a b : instance) : {a = b} + {a <> b}.
Proof. decide equality; [apply (list_eq_dec Nat.eq_dec)|apply site_eq_dec]. Defined.

Definition instance_eqb (a b : instance) : bool :=
  if instance_eq_dec a b then true else false.

Lemma instance_eqb_true : forall a b, instance_eqb a b = true <-> a = b.
Proof. intros a b. unfold instance_eqb. destruct (instance_eq_dec a b); split; congruence. Qed.

Lemma instance_eqb_false : forall a b, instance_eqb a b = false <-> a <> b.
Proof. intros a b. unfold instance_eqb. destruct (instance_eq_dec a b); split; congruence. Qed.

Definition is_nil (v : list nat) : bool := match v with [] => true | _ => false end.

Fixpoint reach (c : code) (s : site) (v : list nat) : bool :=
  match c with
  | Read _ _ body => reach body s v
  | Seq first rest => reach first s v || reach rest s v
  | Cond _ yes no => reach yes s v || reach no s v
  | Loop body => match v with [] => false | _ :: v' => reach body s v' end
  | Iter k rest body =>
      match v with
      | [] => false
      | j :: v' => (Nat.eqb j k && reach rest s v') || (Nat.ltb k j && reach body s v')
      end
  | Prim n sync full _ _ _ body | Wait n sync full _ _ _ body =>
      (site_eqb s (Site n sync full) && is_nil v) || reach body s v
  | Local _ _ _ body => reach body s v
  | Write _ _ | Break | Continue | Skip | Return => false
  end.

Lemma reach_subst : forall c x value s w, reach (subst x value c) s w = reach c s w.
Proof.
  induction c; intros x value s w; cbn; try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - destruct w; [reflexivity|apply IHc].
  - destruct w; [reflexivity|now rewrite IHc1, IHc2].
  - destruct (VAR.eq_dec x v); [reflexivity|now rewrite IHc].
  - destruct (VAR.eq_dec x v); [reflexivity|now rewrite IHc].
  - destruct (VAR.eq_dec x v); [reflexivity|now rewrite IHc].
Qed.

(* A thread waits at a collective when it is its next instruction. The
   instance records the iterations it is in; the thread also supplies a value
   and its result function. *)
Fixpoint at_collective (c : code)
    : option (instance * list nat * (list (nat * list nat) -> nat -> nat)) :=
  match c with
  | Wait n sync full fn values _ _ => Some ((Site n sync full, []), values, fn)
  | Seq first _ => at_collective first
  | Iter k rest _ =>
      match at_collective rest with
      | Some ((s, v), value, fn) => Some ((s, k :: v), value, fn)
      | None => None
      end
  | _ => None
  end.

(* After a release, the waiting primitive gives way to its body with the
   result bound, behind a Skip, so the thread is not at a collective. *)
Fixpoint resume (c : code) (r : nat) : code :=
  match c with
  | Wait _ _ _ _ _ x body => Seq Skip (subst x (NNum r) body)
  | Seq first rest => Seq (resume first r) rest
  | Iter k rest body => Iter k (resume rest r) body
  | _ => c
  end.

Lemma at_collective_reach : forall c s w value fn,
  at_collective c = Some ((s, w), value, fn) -> reach c s w = true.
Proof.
  induction c; intros s w value fn H; cbn in H; try discriminate.
  - cbn. now rewrite (IHc1 _ _ _ _ H).
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    inversion H; subst. cbn. rewrite Nat.eqb_refl. now rewrite (IHc1 _ _ _ _ eq_refl).
  - inversion H; subst. cbn. unfold site_eqb.
    match goal with |- context [site_eq_dec ?a ?b] =>
      destruct (site_eq_dec a b); [reflexivity|congruence] end.
Qed.

Lemma resume_not_waiting : forall c r x,
  at_collective c = Some x -> at_collective (resume c r) = None.
Proof.
  induction c; intros r x H; cbn in H; try discriminate.
  - cbn. exact (IHc1 _ _ H).
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    cbn. now rewrite (IHc1 r _ eq_refl).
  - reflexivity.
Qed.

Lemma at_collective_not_ender : forall c x, at_collective c = Some x -> ender c = false.
Proof. intros [] x H; cbn in H; try discriminate; reflexivity. Qed.

Lemma at_collective_blocks : forall c x tid input m,
  at_collective c = Some x -> step tid input m c = None.
Proof.
  induction c; intros x tid input m H; cbn in H; try discriminate.
  - rewrite step_seq_other by (eapply at_collective_not_ender; eauto).
    now rewrite (IHc1 _ tid input m H).
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    rewrite step_iter_other by (eapply at_collective_not_ender; eauto).
    now rewrite (IHc1 _ tid input m eq_refl).
  - reflexivity.
Qed.

(* Steps never enlarge reach: a branch or a finished part is dropped, an
   iteration ends, or a loop exits. *)
Lemma step_reach : forall c tid input m e m' c' s w,
  step tid input m c = Some (e, m', c') -> reach c' s w = true -> reach c s w = true.
Proof.
  induction c; intros tid input m e m' c' s w H Hr.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn. now rewrite reach_subst in Hr.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. discriminate.
  - apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|
       [first' [Hfirst ->]]]]]].
    + cbn. now rewrite Hr.
    + discriminate.
    + discriminate.
    + discriminate.
    + cbn [reach] in Hr |- *. apply orb_true_iff in Hr as [Hr|Hr].
      * now rewrite (IHc1 _ _ _ _ _ _ _ _ Hfirst Hr).
      * now rewrite Hr, orb_true_r.
  - cbn in H. destruct (b_step tid b) as [[]|]; try discriminate;
      inversion H; subst; cbn; now rewrite Hr, ?orb_true_r.
  - cbn in H. inversion H; subst. cbn [reach] in Hr |- *.
    destruct w as [|j w']; [discriminate|].
    apply orb_true_iff in Hr as [Hr|Hr]; apply andb_true_iff in Hr as [_ Hr]; exact Hr.
  - apply step_iter_view in H as
      [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]]].
    + cbn [reach] in Hr |- *. destruct w as [|j w']; [discriminate|].
      apply orb_true_iff. right. apply andb_true_iff.
      apply orb_true_iff in Hr as [Hr|Hr]; apply andb_true_iff in Hr as [Hj Hr];
        split; try exact Hr.
      * apply Nat.eqb_eq in Hj. apply Nat.ltb_lt. lia.
      * apply Nat.ltb_lt in Hj. apply Nat.ltb_lt. lia.
    + discriminate.
    + discriminate.
    + cbn [reach] in Hr |- *. destruct w as [|j w']; [discriminate|].
      apply orb_true_iff in Hr as [Hr|Hr]; apply andb_true_iff in Hr as [Hj Hr];
        apply orb_true_iff.
      * left. apply andb_true_iff. split; [exact Hj|]. eapply IHc1; eauto.
      * right. apply andb_true_iff. split; [exact Hj|exact Hr].
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H. match type of H with context [eval_all ?t ?a] =>
      destruct (eval_all t a) eqn:Harg end; try discriminate.
    inversion H; subst. exact Hr.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H. match type of H with context [eval_all ?t ?a] =>
      destruct (eval_all t a) eqn:Harg end; try discriminate.
    inversion H; subst. cbn. now rewrite reach_subst in Hr.
  - cbn in H; discriminate.
Qed.

(* Releasing a collective drops only the collective itself. *)
Lemma resume_reach : forall c r x s w,
  at_collective c = Some x -> reach (resume c r) s w = true -> reach c s w = true.
Proof.
  induction c; intros r x s w H Hr; cbn in H; try discriminate.
  - cbn [resume reach] in Hr |- *. apply orb_true_iff in Hr as [Hr|Hr].
    + now rewrite (IHc1 _ _ _ _ H Hr).
    + now rewrite Hr, orb_true_r.
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hrest; try discriminate.
    cbn [resume reach] in Hr |- *. destruct w as [|j w']; [discriminate|].
    apply orb_true_iff in Hr as [Hr|Hr]; apply andb_true_iff in Hr as [Hj Hr];
      apply orb_true_iff.
    + left. apply andb_true_iff. split; [exact Hj|]. exact (IHc1 _ _ _ _ eq_refl Hr).
    + right. apply andb_true_iff. split; [exact Hj|exact Hr].
  - cbn in Hr. rewrite reach_subst in Hr. cbn [reach]. now rewrite Hr, orb_true_r.
Qed.

Record state := State {
  memory : Mem.t;
  threads : list code;
}.

Definition initial (programs : list code) : state := State Mem.empty programs.

(* A thread is done when it has run out of code or returned. *)
Definition finished (st : state) : Prop :=
  Forall (fun c => c = Skip \/ c = Return) (threads st).

Inductive action := Thread (tid : nat) | Release (i : instance).

Inductive event :=
| Memory (access : observation)
| Sync (i : instance) (group : list nat).

Definition waits_at (i : instance) (c : code) : bool :=
  match at_collective c with
  | Some (i', _, _) => instance_eqb i i'
  | None => false
  end.

Definition may_reach (i : instance) (c : code) : bool := reach c (fst i) (snd i).

Definition select (p : code -> bool) (codes : list code) : list nat :=
  filter (fun tid =>
    match nth_error codes tid with Some c => p c | None => false end)
    (seq 0 (length codes)).

(* The group of a release: the threads waiting at the instance. *)
Definition arrived (i : instance) (codes : list code) := select (waits_at i) codes.

(* SIMT-Step's unknown set: threads that may still reach the instance but
   have not arrived. A release waits until it is empty. *)
Definition unknown (i : instance) (codes : list code) :=
  select (fun c => may_reach i c && negb (waits_at i c)) codes.

(* The values the waiting threads supply, with their threads. *)
Definition supply (i : instance) (tid : nat) (c : code) : list (nat * list nat) :=
  match at_collective c with
  | Some (i', value, _) => if instance_eqb i i' then [(tid, value)] else []
  | None => []
  end.

Definition supplied (i : instance) (codes : list code) : list (nat * list nat) :=
  flat_map (fun tid =>
    match nth_error codes tid with Some c => supply i tid c | None => [] end)
    (seq 0 (length codes)).

(* A release gives each waiting thread its result, computed from the values
   the whole group supplied, and resumes it. *)
Definition release_one (i : instance) (values : list (nat * list nat)) (tid : nat)
    (c : code) : code :=
  match at_collective c with
  | Some (i', _, fn) => if instance_eqb i i' then resume c (fn values tid) else c
  | None => c
  end.

Fixpoint release_from (i : instance) (values : list (nat * list nat)) (tid : nat)
    (codes : list code) : list code :=
  match codes with
  | [] => []
  | c :: rest => release_one i values tid c :: release_from i values (S tid) rest
  end.

Definition release (i : instance) (codes : list code) :=
  release_from i (supplied i codes) 0 codes.

Definition advance input (a : action) (st : state) : option (option event * state) :=
  match a with
  | Thread tid =>
      match nth_error (threads st) tid with
      | Some c =>
          match step tid input (memory st) c with
          | Some (o, m', c') =>
              Some (option_map Memory o, State m' (replace_thread tid c' (threads st)))
          | None => None
          end
      | None => None
      end
  | Release i =>
      match arrived i (threads st), unknown i (threads st) with
      | (_ :: _) as group, [] =>
          Some (Some (Sync i group), State (memory st) (release i (threads st)))
      | _, _ => None
      end
  end.

Definition emit_event (e : option event) (trace : list event) :=
  match e with Some e' => e' :: trace | None => trace end.

Inductive execution input : state -> list event -> state -> Prop :=
| execution_refl : forall s, execution input s [] s
| execution_step : forall a s e s' trace last,
    advance input a s = Some (e, s') ->
    execution input s' trace last ->
    execution input s (emit_event e trace) last.

(* Views of the two kinds of step. *)

Lemma thread_view : forall input tid st e st',
  advance input (Thread tid) st = Some (e, st') ->
  exists c o m' c',
    nth_error (threads st) tid = Some c /\
    step tid input (memory st) c = Some (o, m', c') /\
    e = option_map Memory o /\
    st' = State m' (replace_thread tid c' (threads st)).
Proof.
  intros input tid st e st' H. cbn [advance] in H.
  destruct (nth_error (threads st) tid) as [c|] eqn:Hc; try discriminate.
  destruct (step tid input (memory st) c) as [[[o m'] c']|] eqn:Hstep; try discriminate.
  inversion H; subst. do 4 eexists. repeat split; eauto.
Qed.

Lemma thread_build : forall input tid st c o m' c',
  nth_error (threads st) tid = Some c ->
  step tid input (memory st) c = Some (o, m', c') ->
  advance input (Thread tid) st =
    Some (option_map Memory o, State m' (replace_thread tid c' (threads st))).
Proof. intros input tid st c o m' c' Hc Hstep. cbn. now rewrite Hc, Hstep. Qed.

Lemma release_view : forall input i st e st',
  advance input (Release i) st = Some (e, st') ->
  arrived i (threads st) <> [] /\ unknown i (threads st) = [] /\
  e = Some (Sync i (arrived i (threads st))) /\
  st' = State (memory st) (release i (threads st)).
Proof.
  intros input i st e st' H. cbn [advance] in H.
  destruct (arrived i (threads st)) as [|t group] eqn:Harrived; try discriminate.
  destruct (unknown i (threads st)) eqn:Hunknown; try discriminate.
  inversion H; subst. repeat split; congruence.
Qed.

Lemma release_build : forall input i st,
  arrived i (threads st) <> [] -> unknown i (threads st) = [] ->
  advance input (Release i) st =
    Some (Some (Sync i (arrived i (threads st))),
      State (memory st) (release i (threads st))).
Proof.
  intros input i st Harrived Hunknown. cbn [advance]. rewrite Hunknown.
  destruct (arrived i (threads st)); [contradiction|reflexivity].
Qed.

(* Selecting threads. *)

Lemma select_spec : forall p codes tid,
  In tid (select p codes) <->
  exists c, nth_error codes tid = Some c /\ p c = true.
Proof.
  intros p codes tid. unfold select. rewrite filter_In, in_seq. split.
  - intros [_ Hp]. destruct (nth_error codes tid) as [c|]; [eauto|discriminate].
  - intros [c [Hc Hp]]. rewrite Hc. split; [|exact Hp].
    split; [lia|]. cbn. apply (proj1 (nth_error_Some codes tid)). congruence.
Qed.

Lemma select_nil : forall p codes,
  select p codes = [] <-> forall tid c, nth_error codes tid = Some c -> p c = false.
Proof.
  intros p codes. split.
  - intros Hnil tid c Hc. destruct (p c) eqn:Hp; [|reflexivity].
    assert (Hin : In tid (select p codes)) by (apply select_spec; eauto).
    rewrite Hnil in Hin. contradiction.
  - intros Hnone. destruct (select p codes) as [|tid rest] eqn:Hselect; [reflexivity|].
    assert (Hin : In tid (select p codes)) by (rewrite Hselect; left; reflexivity).
    apply select_spec in Hin as [c [Hc Hp]].
    rewrite (Hnone _ _ Hc) in Hp. discriminate.
Qed.

Lemma select_ext : forall p q codes codes',
  length codes = length codes' ->
  (forall tid c c', nth_error codes tid = Some c ->
    nth_error codes' tid = Some c' -> p c = q c') ->
  select p codes = select q codes'.
Proof.
  intros p q codes codes' Hlength Hext. unfold select. rewrite <- Hlength.
  apply filter_ext_in. intros tid Htid. apply in_seq in Htid.
  destruct (nth_error codes tid) as [c|] eqn:Hc, (nth_error codes' tid) as [c'|] eqn:Hc'.
  - eauto.
  - apply nth_error_None in Hc'. lia.
  - apply nth_error_None in Hc. lia.
  - reflexivity.
Qed.

Lemma select_nodup : forall p codes, NoDup (select p codes).
Proof. intros p codes. apply NoDup_filter, seq_NoDup. Qed.

Lemma nth_error_Some_lt : forall {A} (l : list A) i x,
  nth_error l i = Some x -> i < length l.
Proof. intros A l i x H. apply (proj1 (nth_error_Some l i)). congruence. Qed.

Lemma select_bound : forall p codes tid, In tid (select p codes) -> tid < length codes.
Proof.
  intros p codes tid Hin. apply select_spec in Hin as [c [Hc _]].
  eapply nth_error_Some_lt; exact Hc.
Qed.

(* Waiting and reaching. *)

Lemma waits_at_true : forall i c,
  waits_at i c = true <-> exists value fn, at_collective c = Some (i, value, fn).
Proof.
  intros i c. unfold waits_at. destruct (at_collective c) as [[[i' value] fn]|]; split.
  - intros H. apply instance_eqb_true in H. subst. eauto.
  - intros [value' [fn' H]]. inversion H; subst. now apply instance_eqb_true.
  - discriminate.
  - intros [value' [fn' H]]. discriminate.
Qed.

Lemma waits_at_reaches : forall i c, waits_at i c = true -> may_reach i c = true.
Proof.
  intros [s v] c H. apply waits_at_true in H as [value [fn H]].
  exact (at_collective_reach _ _ _ _ _ H).
Qed.

Lemma unknown_nil_waits : forall i codes tid c,
  unknown i codes = [] -> nth_error codes tid = Some c ->
  may_reach i c = true -> waits_at i c = true.
Proof.
  intros i codes tid c Hnil Hc Hreach.
  apply select_nil with (tid := tid) (c := c) in Hnil; [|exact Hc].
  rewrite Hreach in Hnil. cbn in Hnil. now apply negb_false_iff in Hnil.
Qed.

(* A thread outside the group of an enabled release cannot reach it. *)
Lemma enabled_release_excludes : forall i codes tid c,
  unknown i codes = [] -> nth_error codes tid = Some c ->
  waits_at i c = false -> may_reach i c = false.
Proof.
  intros i codes tid c Hnil Hc Hwait. destruct (may_reach i c) eqn:Hreach; [|reflexivity].
  rewrite (unknown_nil_waits _ _ _ _ Hnil Hc Hreach) in Hwait. discriminate.
Qed.

Lemma step_not_waiting : forall i c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> waits_at i c = false.
Proof.
  intros i c tid input m e m' c' Hstep. unfold waits_at.
  destruct (at_collective c) as [[[i' value] fn]|] eqn:Hat; [|reflexivity].
  rewrite (at_collective_blocks _ _ tid input m Hat) in Hstep. discriminate.
Qed.

Lemma step_may_reach : forall i c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> may_reach i c' = true -> may_reach i c = true.
Proof. intros [s v] c tid input m e m' c' H. apply (step_reach _ _ _ _ _ _ _ _ _ H). Qed.

Lemma release_one_other : forall i values tid c,
  waits_at i c = false -> release_one i values tid c = c.
Proof.
  intros i values tid c H. unfold release_one, waits_at in *.
  destruct (at_collective c) as [[[i' value] fn]|]; [now rewrite H|reflexivity].
Qed.

Lemma release_one_waiting : forall i values tid c value fn,
  at_collective c = Some (i, value, fn) ->
  release_one i values tid c = resume c (fn values tid).
Proof.
  intros i values tid c value fn H. unfold release_one. rewrite H.
  now rewrite (proj2 (instance_eqb_true i i) eq_refl).
Qed.

Lemma release_one_may_reach : forall i values tid j c,
  may_reach j (release_one i values tid c) = true -> may_reach j c = true.
Proof.
  intros i values tid [s v] c H. unfold release_one in H.
  destruct (at_collective c) as [[[i' value] fn]|] eqn:Hat; [|exact H].
  destruct (instance_eqb i i'); [|exact H].
  exact (resume_reach _ _ _ _ _ Hat H).
Qed.

Lemma release_from_nth : forall i values codes k tid,
  nth_error (release_from i values k codes) tid =
  option_map (release_one i values (k + tid)) (nth_error codes tid).
Proof.
  intros i values codes. induction codes as [|c codes IH]; intros k [|tid]; cbn;
    try reflexivity.
  - now rewrite Nat.add_0_r.
  - rewrite IH. now replace (S k + tid) with (k + S tid) by lia.
Qed.

Lemma release_nth : forall i codes tid,
  nth_error (release i codes) tid =
  option_map (release_one i (supplied i codes) tid) (nth_error codes tid).
Proof. intros i codes tid. unfold release. apply release_from_nth. Qed.

Lemma release_from_length : forall i values codes k,
  length (release_from i values k codes) = length codes.
Proof.
  intros i values codes. induction codes as [|c codes IH]; intros k; cbn; auto.
Qed.

Lemma release_length : forall i codes, length (release i codes) = length codes.
Proof. intros i codes. apply release_from_length. Qed.
