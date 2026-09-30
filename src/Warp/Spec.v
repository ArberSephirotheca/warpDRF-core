From Stdlib Require Import Lists.List Strings.String Arith.PeanoNat Bool.Bool Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Agree.

Import ListNotations.
Open Scope string_scope.

(* Spec releases a collective as soon as some thread waits at it, like
   __activemask(), which reports whichever threads have arrived: it does not
   wait for the unknown set to empty. Each instance is released at most once,
   so a thread that arrives after the release waits forever. Thread steps are
   the SSO thread steps. *)

Record spec_state := SpecState {
  base : state;
  released : list instance;
}.

Definition spec_initial (programs : list code) := SpecState (initial programs) [].

Definition spec_advance input (a : action) (s : spec_state)
    : option (option event * spec_state) :=
  match a with
  | Thread _ =>
      match advance input a (base s) with
      | Some (e, st') => Some (e, SpecState st' (released s))
      | None => None
      end
  | Release i =>
      if existsb (instance_eqb i) (released s) then None else
      match arrived i (threads (base s)) with
      | [] => None
      | group =>
          Some (Some (Sync i group),
            SpecState (State (memory (base s)) (release i (threads (base s))))
              (i :: released s))
      end
  end.

Inductive spec_execution input : spec_state -> list event -> spec_state -> Prop :=
| spec_refl : forall s, spec_execution input s [] s
| spec_step : forall a s e s' trace last,
    spec_advance input a s = Some (e, s') ->
    spec_execution input s' trace last ->
    spec_execution input s (emit_event e trace) last.

(* Run a schedule; fails if an action is not enabled. *)
Fixpoint spec_run input (schedule : list action) (s : spec_state)
    : option (list event * spec_state) :=
  match schedule with
  | [] => Some ([], s)
  | a :: rest =>
      match spec_advance input a s with
      | Some (e, s') =>
          match spec_run input rest s' with
          | Some (trace, last) => Some (emit_event e trace, last)
          | None => None
          end
      | None => None
      end
  end.

Lemma spec_run_sound : forall input schedule s trace last,
  spec_run input schedule s = Some (trace, last) -> spec_execution input s trace last.
Proof.
  intros input schedule. induction schedule as [|a rest IH]; intros s trace last Hrun;
    cbn in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (spec_advance input a s) as [[e s']|] eqn:Hstep; try discriminate.
    destruct (spec_run input rest s') as [[tail final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. econstructor; [exact Hstep|]. now apply IH.
Qed.

Lemma spec_thread_view : forall input tid s e s',
  spec_advance input (Thread tid) s = Some (e, s') ->
  advance input (Thread tid) (base s) = Some (e, base s') /\ released s' = released s.
Proof.
  intros input tid s e s' H. cbn [spec_advance] in H.
  destruct (advance input (Thread tid) (base s)) as [[e' st']|]; try discriminate.
  inversion H; subst. split; reflexivity.
Qed.

Lemma spec_release_view : forall input i s e s',
  spec_advance input (Release i) s = Some (e, s') ->
  ~ In i (released s) /\ arrived i (threads (base s)) <> [] /\
  e = Some (Sync i (arrived i (threads (base s)))) /\
  base s' = State (memory (base s)) (release i (threads (base s))) /\
  released s' = i :: released s.
Proof.
  intros input i s e s' H. cbn [spec_advance] in H.
  destruct (existsb (instance_eqb i) (released s)) eqn:Hdone; [discriminate|].
  split.
  { intros Hin. assert (Hex : existsb (instance_eqb i) (released s) = true).
    { apply existsb_exists. exists i. split; [exact Hin|now apply instance_eqb_true]. }
    congruence. }
  destruct (arrived i (threads (base s))) as [|t group] eqn:Harrived; [discriminate|].
  inversion H; subst. split; [discriminate|]. repeat split.
Qed.

Lemma spec_advance_released : forall input a s e s',
  spec_advance input a s = Some (e, s') -> incl (released s) (released s').
Proof.
  intros input [tid|i] s e s' H.
  - apply spec_thread_view in H as [_ ->]. apply incl_refl.
  - apply spec_release_view in H as [_ [_ [_ [_ ->]]]]. intros j Hj. right. exact Hj.
Qed.

(* A thread that reaches an instance after its release never finishes. *)
Lemma late_arrival_stuck : forall input s trace last u i c,
  spec_execution input s trace last ->
  nth_error (threads (base s)) u = Some c -> waits_at i c = true -> In i (released s) ->
  ~ finished (base last).
Proof.
  intros input s trace last u i c Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH];
    intros Hc Hwait Hdone Hfinished.
  - unfold finished in Hfinished. rewrite Forall_forall in Hfinished.
    rewrite (Hfinished c (nth_error_In _ _ Hc)) in Hwait. discriminate.
  - assert (Hkeep : In i (released s'))
      by exact (spec_advance_released _ _ _ _ _ Hstep i Hdone).
    apply IH; [|exact Hwait|exact Hkeep|exact Hfinished].
    destruct a as [tid|j].
    + apply spec_thread_view in Hstep as [Hadv _].
      apply thread_view in Hadv as [d [o [m' [d' [Hd [Hthread [_ Hs']]]]]]].
      rewrite Hs'. cbn [threads]. destruct (Nat.eq_dec tid u) as [->|Hne].
      * rewrite Hc in Hd. inversion Hd; subst d.
        apply waits_at_true in Hwait as [c'' Hat].
        rewrite (at_collective_blocks _ _ _ u input (memory (base s)) Hat) in Hthread.
        discriminate.
      * rewrite replace_thread_other by congruence. exact Hc.
    + apply spec_release_view in Hstep as [Hnot [_ [_ [Hs' _]]]].
      rewrite Hs'. cbn [threads]. rewrite release_nth, Hc. cbn [option_map]. f_equal.
      apply release_one_other. destruct (waits_at j c) eqn:Hj; [|reflexivity].
      exfalso. apply Hnot.
      apply waits_at_true in Hj as [c1 H1]. apply waits_at_true in Hwait as [c2 H2].
      rewrite H1 in H2. inversion H2; subst. exact Hdone.
Qed.

(* Closed tests. *)

Lemma closed_nexp_step : forall e tid, closed_nexp e = true -> n_step tid e = n_step 0 e.
Proof.
  induction e as [| n | x | o e1 IH1 e2 IH2]; intros tid H; cbn in H |- *;
    try discriminate; try reflexivity.
  apply andb_true_iff in H as [H1 H2]. now rewrite (IH1 tid H1), (IH2 tid H2).
Qed.

Lemma closed_bexp_step : forall e tid, closed_bexp e = true -> b_step tid e = b_step 0 e.
Proof.
  induction e as [b | o e1 e2 | o e1 IH1 e2 IH2 | e IH]; intros tid H; cbn in H |- *.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    now rewrite (closed_nexp_step _ tid H1), (closed_nexp_step _ tid H2).
  - apply andb_true_iff in H as [H1 H2]. now rewrite (IH1 tid H1), (IH2 tid H2).
  - now rewrite (IH tid H).
Qed.

Lemma closed_nexp_subst : forall e x v, closed_nexp e = true -> n_subst x v e = e.
Proof.
  induction e as [| n | y | o e1 IH1 e2 IH2]; intros x v H; cbn in H |- *;
    try discriminate; try reflexivity.
  apply andb_true_iff in H as [H1 H2]. now rewrite (IH1 x v H1), (IH2 x v H2).
Qed.

Lemma closed_bexp_subst : forall e x v, closed_bexp e = true -> b_subst x v e = e.
Proof.
  induction e as [b | o e1 e2 | o e1 IH1 e2 IH2 | e IH]; intros x v H; cbn in H |- *.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    now rewrite (closed_nexp_subst _ x v H1), (closed_nexp_subst _ x v H2).
  - apply andb_true_iff in H as [H1 H2]. now rewrite (IH1 x v H1), (IH2 x v H2).
  - now rewrite (IH x v H).
Qed.

(* Placement is kept by steps and releases. *)

Lemma has_primitive_subst : forall c x value,
  has_primitive (subst x value c) = has_primitive c.
Proof.
  induction c; intros x value; cbn; try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - apply IHc.
  - now rewrite IHc1, IHc2.
Qed.

Lemma has_jump_subst : forall c x value, has_jump (subst x value c) = has_jump c.
Proof.
  induction c; intros x value; cbn; try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
Qed.

Lemma placed_subst : forall c lp x value,
  placed lp c = true -> placed lp (subst x value c) = true.
Proof.
  induction c; intros lp x value H; cbn in H |- *; try reflexivity.
  - destruct (VAR.eq_dec x v); [exact H|now apply IHc].
  - apply andb_true_iff in H as [H1 H2]. now rewrite IHc1, IHc2.
  - rewrite !has_primitive_subst, !has_jump_subst.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H H2].
    rewrite (IHc1 _ _ _ H2), (IHc2 _ _ _ H3), !andb_true_r.
    apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left; exact H|right].
    now rewrite closed_bexp_subst.
  - rewrite has_primitive_subst. now apply IHc.
  - rewrite has_primitive_subst. apply andb_true_iff in H as [H1 H2].
    now rewrite IHc1, IHc2.
Qed.

(* A running loop's remaining iteration has a collective only if its body
   does. Source programs have no running loops. *)
Fixpoint loops_ok (c : code) : Prop :=
  match c with
  | Read _ _ body | Loop body => loops_ok body
  | Seq first rest | Cond _ first rest => loops_ok first /\ loops_ok rest
  | Iter _ rest body =>
      (has_primitive rest = true -> has_primitive body = true) /\
      loops_ok rest /\ loops_ok body
  | _ => True
  end.

Lemma loops_ok_subst : forall c x value, loops_ok c -> loops_ok (subst x value c).
Proof.
  induction c; intros x value H; cbn in H |- *; try exact I.
  - destruct (VAR.eq_dec x v); [exact H|now apply IHc].
  - destruct H as [H1 H2]. split; [apply IHc1|apply IHc2]; assumption.
  - destruct H as [H1 H2]. split; [apply IHc1|apply IHc2]; assumption.
  - now apply IHc.
  - rewrite !has_primitive_subst. destruct H as [H0 [H1 H2]].
    split; [exact H0|split; [apply IHc1|apply IHc2]; assumption].
Qed.

Lemma static_loops_ok : forall c, static c = true -> loops_ok c.
Proof.
  induction c; intros H; cbn in H |- *; try exact I; try discriminate.
  - now apply IHc.
  - apply andb_true_iff in H as [H1 H2]. split; auto.
  - apply andb_true_iff in H as [H1 H2]. split; auto.
  - now apply IHc.
Qed.

Lemma step_has_primitive : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> has_primitive c' = true -> has_primitive c = true.
Proof.
  induction c; intros tid input m e m' c' H Hp.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn. now rewrite has_primitive_subst in Hp.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. discriminate.
  - apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + exact Hp.
    + discriminate.
    + discriminate.
    + cbn in Hp |- *. apply orb_true_iff in Hp as [Hp|Hp].
      * now rewrite (IHc1 _ _ _ _ _ _ Hfirst Hp).
      * now rewrite Hp, orb_true_r.
  - cbn in H. destruct (b_step tid b) as [[]|]; try discriminate;
      inversion H; subst; cbn; now rewrite Hp, ?orb_true_r.
  - cbn in H. inversion H; subst. cbn in Hp |- *. now rewrite orb_diag in Hp.
  - apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]].
    + cbn in Hp |- *. rewrite orb_diag in Hp. now rewrite Hp, orb_true_r.
    + discriminate.
    + cbn in Hp |- *. apply orb_true_iff in Hp as [Hp|Hp].
      * now rewrite (IHc1 _ _ _ _ _ _ Hrest Hp).
      * now rewrite Hp, orb_true_r.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma step_placed : forall c lp tid input m e m' c',
  step tid input m c = Some (e, m', c') -> placed lp c = true -> placed lp c' = true.
Proof.
  induction c; intros lp tid input m e m' c' H Hp.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn in Hp. now apply placed_subst.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. reflexivity.
  - cbn in Hp. apply andb_true_iff in Hp as [Hp1 Hp2].
    apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + exact Hp2.
    + reflexivity.
    + reflexivity.
    + cbn. rewrite (IHc1 _ _ _ _ _ _ _ Hfirst Hp1). exact Hp2.
  - cbn in H, Hp. apply andb_true_iff in Hp as [Hp Hno].
    apply andb_true_iff in Hp as [_ Hyes].
    destruct (b_step tid b) as [[]|]; try discriminate; inversion H; subst; assumption.
  - cbn in H. inversion H; subst. cbn in Hp |- *. now rewrite Hp.
  - cbn in Hp. apply andb_true_iff in Hp as [Hp1 Hp2].
    apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]].
    + cbn. now rewrite Hp2.
    + reflexivity.
    + cbn. rewrite (IHc1 _ _ _ _ _ _ _ Hrest Hp1). exact Hp2.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma step_has_jump : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> has_jump c = false -> has_jump c' = false.
Proof.
  induction c; intros tid input m e m' c' H Hj.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn in Hj. now rewrite has_jump_subst.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. reflexivity.
  - apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]];
      cbn in Hj; try discriminate.
    + exact Hj.
    + apply orb_false_iff in Hj as [Hj1 Hj2].
      cbn. rewrite (IHc1 _ _ _ _ _ _ Hfirst Hj1). exact Hj2.
  - cbn in H, Hj. apply orb_false_iff in Hj as [Hyes Hno].
    destruct (b_step tid b) as [[]|]; try discriminate; inversion H; subst; assumption.
  - cbn in H. inversion H; subst. reflexivity.
  - apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]];
      reflexivity.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma step_loops_ok : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> loops_ok c -> loops_ok c'.
Proof.
  induction c; intros tid input m e m' c' H Hok.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn in Hok. now apply loops_ok_subst.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. exact I.
  - cbn in Hok. destruct Hok as [Hok1 Hok2].
    apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + exact Hok2.
    + exact I.
    + exact I.
    + split; [eapply IHc1; eauto|exact Hok2].
  - cbn in H, Hok. destruct Hok as [Hyes Hno].
    destruct (b_step tid b) as [[]|]; try discriminate; inversion H; subst; assumption.
  - cbn in H. inversion H; subst. cbn in Hok |- *.
    split; [intros Hp; exact Hp|split; exact Hok].
  - cbn in Hok. destruct Hok as [Hprim [Hok1 Hok2]].
    apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]].
    + cbn. split; [intros Hp; exact Hp|split; exact Hok2].
    + exact I.
    + cbn. split; [|split; [eapply IHc1; eauto|exact Hok2]].
      intros Hp. apply Hprim. eapply step_has_primitive; eauto.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma at_collective_primitive : forall c i c',
  at_collective c = Some (i, c') -> has_primitive c = true.
Proof.
  induction c; intros i c' H; cbn in H; try discriminate.
  - destruct (at_collective c1) as [[[s1 v1] f]|] eqn:Hf; try discriminate.
    cbn. now rewrite (IHc1 _ _ eq_refl).
  - destruct (at_collective c1) as [[[s1 v1] r]|] eqn:Hr; try discriminate.
    cbn. now rewrite (IHc1 _ _ eq_refl).
  - reflexivity.
  - reflexivity.
Qed.

Lemma release_placed : forall c lp i c',
  at_collective c = Some (i, c') -> placed lp c = true -> placed lp c' = true.
Proof.
  induction c; intros lp i c' H Hp; cbn in H; try discriminate.
  - destruct (at_collective c1) as [[[s1 v1] f]|] eqn:Hf; try discriminate.
    inversion H; subst. cbn in Hp |- *. apply andb_true_iff in Hp as [Hp1 Hp2].
    now rewrite (IHc1 _ _ _ eq_refl Hp1), Hp2.
  - destruct (at_collective c1) as [[[s1 v1] r]|] eqn:Hr; try discriminate.
    inversion H; subst. cbn in Hp |- *. apply andb_true_iff in Hp as [Hp1 Hp2].
    now rewrite (IHc1 _ _ _ eq_refl Hp1), Hp2.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
Qed.

Lemma release_has_jump : forall c i c',
  at_collective c = Some (i, c') -> has_jump c' = has_jump c.
Proof.
  induction c; intros i c' H; cbn in H; try discriminate.
  - destruct (at_collective c1) as [[[s1 v1] f]|] eqn:Hf; try discriminate.
    inversion H; subst. cbn. now rewrite (IHc1 _ _ eq_refl).
  - destruct (at_collective c1) as [[[s1 v1] r]|] eqn:Hr; try discriminate.
    inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
Qed.

Lemma release_loops_ok : forall c i c',
  at_collective c = Some (i, c') -> loops_ok c -> loops_ok c'.
Proof.
  induction c; intros i c' H Hok; cbn in H; try discriminate.
  - destruct (at_collective c1) as [[[s1 v1] f]|] eqn:Hf; try discriminate.
    inversion H; subst. cbn in Hok |- *. destruct Hok as [Hok1 Hok2].
    split; [eapply IHc1; eauto|exact Hok2].
  - destruct (at_collective c1) as [[[s1 v1] r]|] eqn:Hr; try discriminate.
    inversion H; subst. cbn in Hok |- *. destruct Hok as [Hprim [Hok1 Hok2]].
    split; [|split; [eapply IHc1; eauto|exact Hok2]].
    intros _. apply Hprim. eapply at_collective_primitive; eauto.
  - inversion H; subst. exact I.
  - inversion H; subst. exact I.
Qed.

(* The shape of a thread's code keeps what decides its collectives: the
   collectives, the loops that contain them, and the jumps that end their
   iterations. Primitive-free code becomes Skip, and a conditional around a
   collective is resolved by its closed test. Reads and resolved conditionals
   leave a Skip in front, so a thread whose next step is not a collective is
   never at a collective in its shape. *)

Definition mkseq (a b : code) : code :=
  match a, b with
  | Skip, Skip => Skip
  | _, _ => Seq a b
  end.

Definition test_value (test : bexp) : bool :=
  match b_step 0 test with Some b => b | None => false end.

Fixpoint shape (c : code) : code :=
  match c with
  | Read _ _ body => mkseq Skip (shape body)
  | Write _ _ | Skip => Skip
  | Seq first rest => mkseq (shape first) (shape rest)
  | Cond test yes no =>
      if test_value test then mkseq Skip (shape yes) else mkseq Skip (shape no)
  | Loop body => if has_primitive body then Loop (shape body) else Skip
  | Iter k rest body => if has_primitive body then Iter k (shape rest) (shape body) else Skip
  | Break => Break
  | Continue => Continue
  | Barrier n => Barrier n
  | AddZero => AddZero
  end.

(* One step of a shape, for every thread alike: drop a finished part, take a
   jump, start or end an iteration, or pass a collective. *)
Fixpoint astep (a : code) : code :=
  match a with
  | Seq first rest =>
      match first with
      | Skip => rest
      | Break => Break
      | Continue => Continue
      | _ => mkseq (astep first) rest
      end
  | Loop body => Iter 0 body body
  | Iter k rest body =>
      match rest with
      | Skip | Continue => Iter (S k) body body
      | Break => Skip
      | _ => Iter k (astep rest) body
      end
  | Barrier _ | AddZero => Skip
  | _ => a
  end.

Lemma skip_dec : forall c : code, c = Skip \/ c <> Skip.
Proof. intros []; first [left; reflexivity|right; discriminate]. Qed.

Lemma mkseq_cases : forall a b, mkseq a b = Skip \/ mkseq a b = Seq a b.
Proof.
  intros a b. destruct a; try (right; reflexivity).
  destruct b; try (right; reflexivity). left; reflexivity.
Qed.

Lemma mkseq_other : forall a b, a <> Skip -> mkseq a b = Seq a b.
Proof. intros a b H. destruct a; try reflexivity. contradiction. Qed.

Lemma astep_mkseq_skip : forall b, astep (mkseq Skip b) = b.
Proof. intros []; reflexivity. Qed.

Lemma astep_seq_other : forall first rest,
  ender first = false -> astep (Seq first rest) = mkseq (astep first) rest.
Proof. intros first rest H. destruct first; try discriminate; reflexivity. Qed.

Lemma astep_iter_other : forall k rest body,
  ender rest = false -> astep (Iter k rest body) = Iter k (astep rest) body.
Proof. intros k rest body H. destruct rest; try discriminate; reflexivity. Qed.

(* A shape ends a sequence or an iteration only when the code does. *)
Lemma ender_shape : forall c, ender c = false -> shape c <> Skip -> ender (shape c) = false.
Proof.
  intros c Hc Hs. destruct c; cbn [shape ender] in *; try discriminate; try reflexivity.
  - destruct (mkseq_cases Skip (shape c)) as [E|E]; rewrite E in *;
      [contradiction|reflexivity].
  - contradiction.
  - destruct (mkseq_cases (shape c1) (shape c2)) as [E|E]; rewrite E in *;
      [contradiction|reflexivity].
  - destruct (test_value b);
      [destruct (mkseq_cases Skip (shape c1)) as [E|E]
      |destruct (mkseq_cases Skip (shape c2)) as [E|E]];
      rewrite E in *; first [contradiction|reflexivity].
  - destruct (has_primitive c); [reflexivity|contradiction].
  - destruct (has_primitive c2); [reflexivity|contradiction].
Qed.

Lemma shape_idle : forall c,
  has_primitive c = false -> has_jump c = false -> shape c = Skip.
Proof.
  induction c; intros Hp Hj; cbn [shape has_primitive has_jump] in *;
    try discriminate; try reflexivity.
  - now rewrite IHc.
  - apply orb_false_iff in Hp as [Hp1 Hp2]. apply orb_false_iff in Hj as [Hj1 Hj2].
    now rewrite IHc1, IHc2.
  - apply orb_false_iff in Hp as [Hp1 Hp2]. apply orb_false_iff in Hj as [Hj1 Hj2].
    rewrite IHc1, IHc2 by assumption. now destruct (test_value b).
  - now rewrite Hp.
  - apply orb_false_iff in Hp as [_ Hp2]. now rewrite Hp2.
Qed.

Lemma jump_parts : forall lp a b,
  (lp = false -> has_jump a || has_jump b = false) ->
  (lp = false -> has_jump a = false) /\ (lp = false -> has_jump b = false).
Proof.
  intros lp a b H. split; intros E; specialize (H E); apply orb_false_iff in H; tauto.
Qed.

(* A conditional whose test is not closed has idle branches. *)
Lemma open_branches_idle : forall lp yes no,
  negb (has_primitive yes || has_primitive no || lp && (has_jump yes || has_jump no)) = true ->
  (lp = false -> has_jump yes || has_jump no = false) ->
  shape yes = Skip /\ shape no = Skip.
Proof.
  intros lp yes no Hopen Hj. apply negb_true_iff in Hopen.
  apply orb_false_iff in Hopen as [Hprim Hjump].
  apply orb_false_iff in Hprim as [Hyes Hno].
  assert (Hjumps : has_jump yes || has_jump no = false).
  { destruct lp; [exact Hjump|exact (Hj eq_refl)]. }
  apply orb_false_iff in Hjumps as [Hjyes Hjno].
  split; apply shape_idle; assumption.
Qed.

Lemma shape_subst : forall c lp x value,
  placed lp c = true -> (lp = false -> has_jump c = false) ->
  shape (subst x value c) = shape c.
Proof.
  induction c; intros lp x value Hp Hj; cbn [Code.subst shape placed has_jump] in *;
    try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|]. now rewrite (IHc lp).
  - apply andb_true_iff in Hp as [Hp1 Hp2]. destruct (jump_parts _ _ _ Hj) as [Hj1 Hj2].
    now rewrite (IHc1 lp x value Hp1 Hj1), (IHc2 lp x value Hp2 Hj2).
  - apply andb_true_iff in Hp as [Hp Hp2]. apply andb_true_iff in Hp as [Hp Hp1].
    destruct (jump_parts _ _ _ Hj) as [Hj1 Hj2].
    rewrite (IHc1 lp x value Hp1 Hj1), (IHc2 lp x value Hp2 Hj2).
    apply orb_true_iff in Hp as [Hopen|Hclosed].
    + destruct (open_branches_idle _ _ _ Hopen Hj) as [-> ->].
      now destruct (test_value (b_subst x value b)), (test_value b).
    + now rewrite closed_bexp_subst.
  - rewrite has_primitive_subst. destruct (has_primitive c) eqn:Hc; [|reflexivity].
    rewrite ?Hc in Hp. now rewrite (IHc true).
  - rewrite has_primitive_subst. apply andb_true_iff in Hp as [Hp1 Hp2].
    destruct (has_primitive c2) eqn:Hc; [|reflexivity].
    rewrite ?Hc in Hp1, Hp2. now rewrite (IHc1 true), (IHc2 true).
Qed.

(* A thread step leaves the shape alone or takes its one abstract step. *)
Lemma step_shape : forall c lp tid input m e m' c',
  step tid input m c = Some (e, m', c') ->
  placed lp c = true -> (lp = false -> has_jump c = false) -> loops_ok c ->
  shape c' = shape c \/ shape c' = astep (shape c).
Proof.
  induction c; intros lp tid input m e m' c' H Hp Hj Hok.
  - cbn in H. destruct (n_step tid n); try discriminate. inversion H; subst.
    right. cbn [shape]. rewrite astep_mkseq_skip. now apply (shape_subst _ lp).
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. left. reflexivity.
  - cbn [placed has_jump loops_ok] in Hp, Hj, Hok.
    apply andb_true_iff in Hp as [Hp1 Hp2]. destruct (jump_parts _ _ _ Hj) as [Hj1 Hj2].
    destruct Hok as [Hok1 Hok2].
    apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + right. cbn [shape]. now rewrite astep_mkseq_skip.
    + right. reflexivity.
    + right. reflexivity.
    + cbn [shape]. destruct (IHc1 _ _ _ _ _ _ _ Hfirst Hp1 Hj1 Hok1) as [Hsame|Hnext].
      * left. now rewrite Hsame.
      * destruct (skip_dec (shape c1)) as [Hs|Hs].
        -- left. rewrite Hs in Hnext |- *. cbn in Hnext. now rewrite Hnext.
        -- right. rewrite (mkseq_other _ _ Hs).
           rewrite astep_seq_other
             by (apply ender_shape; [eapply step_not_ender; eauto|exact Hs]).
           now rewrite Hnext.
  - cbn in H. cbn [placed has_jump] in Hp, Hj.
    apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [Htest _].
    destruct (b_step tid b) as [value|] eqn:Hstep; [|discriminate].
    inversion H; subst. right. cbn [shape].
    apply orb_true_iff in Htest as [Hopen|Hclosed].
    + destruct (open_branches_idle _ _ _ Hopen Hj) as [Hyes Hno].
      rewrite Hyes, Hno. now destruct value, (test_value b).
    + assert (Hvalue : test_value b = value).
      { unfold test_value. now rewrite <- (closed_bexp_step _ tid Hclosed), Hstep. }
      rewrite Hvalue. destruct value; symmetry; apply astep_mkseq_skip.
  - cbn in H. inversion H; subst. cbn [shape].
    destruct (has_primitive c); [right|left]; reflexivity.
  - cbn [placed loops_ok] in Hp, Hok. apply andb_true_iff in Hp as [Hp1 Hp2].
    destruct Hok as [Hprim [Hok1 Hok2]].
    apply step_iter_view in H as
      [[[-> | ->] [_ [_ ->]]]|[[-> [_ [_ ->]]]|[rest' [Hrest ->]]]];
      cbn [shape]; destruct (has_primitive c2) eqn:Hc2; try (left; reflexivity).
    + right. reflexivity.
    + right. reflexivity.
    + right. reflexivity.
    + rewrite ?Hc2 in Hp1.
      destruct (IHc1 true _ _ _ _ _ _ Hrest Hp1 (fun E => ltac:(discriminate E)) Hok1)
        as [Hsame|Hnext].
      * left. now rewrite Hsame.
      * destruct (skip_dec (shape c1)) as [Hs|Hs].
        -- left. rewrite Hs in Hnext |- *. cbn in Hnext. now rewrite Hnext.
        -- right. rewrite astep_iter_other
             by (apply ender_shape; [eapply step_not_ender; eauto|exact Hs]).
           now rewrite Hnext.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

(* The instance a code waits at. *)
Definition pending (c : code) : option instance := option_map fst (at_collective c).

Lemma pending_seq : forall a b, pending (Seq a b) = pending a.
Proof.
  intros a b. unfold pending. cbn [at_collective].
  destruct (at_collective a) as [[[s v] a']|]; reflexivity.
Qed.

Lemma pending_mkseq : forall a b, pending (mkseq a b) = pending a.
Proof.
  intros a b. destruct (skip_dec a) as [->|Ha].
  - destruct (mkseq_cases Skip b) as [E|E]; rewrite E; [reflexivity|apply pending_seq].
  - rewrite (mkseq_other _ _ Ha). apply pending_seq.
Qed.

Lemma pending_iter : forall k rest body,
  pending (Iter k rest body) =
    match pending rest with Some (s, v) => Some (s, k :: v) | None => None end.
Proof.
  intros k rest body. unfold pending. cbn [at_collective].
  destruct (at_collective rest) as [[[s v] r]|]; reflexivity.
Qed.

Lemma pending_ender : forall a j, pending a = Some j -> ender a = false.
Proof. intros [] j H; cbn in H; try discriminate; reflexivity. Qed.

Lemma pending_waits : forall i c, pending c = Some i -> waits_at i c = true.
Proof.
  intros i c H. apply waits_at_true. unfold pending in H.
  destruct (at_collective c) as [[i' c']|]; cbn in H; inversion H; subst. eauto.
Qed.

Lemma waits_pending : forall i c, waits_at i c = true -> pending c = Some i.
Proof.
  intros i c H. apply waits_at_true in H as [c' H]. unfold pending. now rewrite H.
Qed.

(* A shape waits where its code waits. *)
Lemma pending_shape : forall c, loops_ok c -> pending (shape c) = pending c.
Proof.
  induction c; intros Hok; cbn [shape loops_ok] in *.
  - now rewrite pending_mkseq.
  - reflexivity.
  - destruct Hok as [Hok1 Hok2]. rewrite pending_mkseq, pending_seq. now apply IHc1.
  - destruct (test_value b); now rewrite pending_mkseq.
  - destruct (has_primitive c); reflexivity.
  - destruct Hok as [Hprim [Hok1 Hok2]]. destruct (has_primitive c2) eqn:Hc2.
    + rewrite !pending_iter. now rewrite IHc1.
    + rewrite pending_iter. destruct (pending c1) as [[s v]|] eqn:Hp; [|reflexivity].
      exfalso. unfold pending in Hp.
      destruct (at_collective c1) as [[i r]|] eqn:Hat; [|discriminate].
      pose proof (Hprim (at_collective_primitive _ _ _ Hat)). congruence.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Passing a collective is the shape's abstract step. *)
Lemma release_shape : forall c i c',
  at_collective c = Some (i, c') -> loops_ok c -> shape c' = astep (shape c).
Proof.
  induction c; intros i c' H Hok; cbn in H; try discriminate.
  - destruct (at_collective c1) as [[[s1 v1] f]|] eqn:Hf; try discriminate.
    inversion H; subst. cbn [loops_ok] in Hok. destruct Hok as [Hok1 Hok2].
    assert (Hpend : pending (shape c1) = Some (s1, v1)).
    { rewrite pending_shape by exact Hok1. unfold pending. now rewrite Hf. }
    assert (Hs : shape c1 <> Skip) by (intros E; rewrite E in Hpend; discriminate).
    cbn [shape]. rewrite (mkseq_other _ _ Hs).
    rewrite astep_seq_other by (eapply pending_ender; eauto).
    now rewrite (IHc1 _ _ eq_refl Hok1).
  - destruct (at_collective c1) as [[[s1 v1] r]|] eqn:Hr; try discriminate.
    inversion H; subst. cbn [loops_ok] in Hok. destruct Hok as [Hprim [Hok1 Hok2]].
    assert (Hc2 : has_primitive c2 = true)
      by (apply Hprim; eapply at_collective_primitive; eauto).
    assert (Hpend : pending (shape c1) = Some (s1, v1)).
    { rewrite pending_shape by exact Hok1. unfold pending. now rewrite Hr. }
    cbn [shape]. rewrite Hc2.
    rewrite astep_iter_other by (eapply pending_ender; eauto).
    now rewrite (IHc1 _ _ eq_refl Hok1).
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
Qed.

(* Every thread of a full-warp kernel starts at the same shape and moves
   along the same path of abstract steps. *)
Definition path (start : code) (n : nat) : code := Nat.iter n astep start.

Lemma path_skip : forall start n m, path start n = Skip -> n <= m -> path start m = Skip.
Proof.
  intros start n m H Hle. induction Hle as [|m Hle IH]; [exact H|].
  change (astep (path start m) = Skip). now rewrite IH.
Qed.

Definition good (c : code) : Prop :=
  placed false c = true /\ has_jump c = false /\ loops_ok c.

Lemma step_good : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> good c -> good c'.
Proof.
  intros c tid input m e m' c' H [Hp [Hj Hok]]. split; [|split].
  - eapply step_placed; eauto.
  - eapply step_has_jump; eauto.
  - eapply step_loops_ok; eauto.
Qed.

Lemma release_good : forall c i c', at_collective c = Some (i, c') -> good c -> good c'.
Proof.
  intros c i c' H [Hp [Hj Hok]]. split; [|split].
  - eapply release_placed; eauto.
  - now rewrite (release_has_jump _ _ _ H).
  - eapply release_loops_ok; eauto.
Qed.

Lemma good_step_shape : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> good c ->
  shape c' = shape c \/ shape c' = astep (shape c).
Proof.
  intros c tid input m e m' c' H [Hp [Hj Hok]].
  eapply step_shape; eauto.
Qed.

(* A thread is on the path at position n when its shape is the nth code of
   the path, and every instance the path passed before n has been released. *)
Definition on_path (start : code) (done : list instance) (c : code) : Prop :=
  good c /\ exists n, shape c = path start n /\
    forall k j, k < n -> pending (path start k) = Some j -> In j done.

Definition spec_inv (start : code) (s : spec_state) : Prop :=
  Forall (on_path start (released s)) (threads (base s)).

Lemma on_path_mono : forall start done done' c,
  incl done done' -> on_path start done c -> on_path start done' c.
Proof.
  intros start done done' c Hincl [Hgood [n [Hn Hdone]]].
  split; [exact Hgood|]. exists n. split; [exact Hn|].
  intros k j Hk Hj. apply Hincl. eapply Hdone; eauto.
Qed.

Lemma Forall_replace_thread : forall (P : code -> Prop) codes tid c,
  Forall P codes -> P c -> Forall P (replace_thread tid c codes).
Proof.
  intros P codes. induction codes as [|d codes IH]; intros [|tid] c Hall Hc; cbn;
    inversion Hall; subst; try constructor; auto.
Qed.

Lemma spec_advance_inv : forall start input a s e s',
  spec_inv start s -> spec_advance input a s = Some (e, s') -> spec_inv start s'.
Proof.
  intros start input [tid|i] s e s' Hinv Hstep; unfold spec_inv in *.
  - apply spec_thread_view in Hstep as [Hadv Hdone].
    apply thread_view in Hadv as [c [o [m' [c' [Hc [Hthread [_ Hs']]]]]]].
    rewrite Hs', Hdone. cbn [threads].
    apply Forall_replace_thread; [exact Hinv|].
    rewrite Forall_forall in Hinv.
    destruct (Hinv c (nth_error_In _ _ Hc)) as [Hgood [n [Hn Hpast]]].
    split; [eapply step_good; eauto|].
    destruct (good_step_shape _ _ _ _ _ _ _ Hthread Hgood) as [Hsame|Hnext].
    + exists n. split; [now rewrite Hsame|exact Hpast].
    + exists (S n). split; [rewrite Hnext, Hn; reflexivity|].
      intros k j Hk Hj. destruct (Nat.eq_dec k n) as [->|Hne];
        [|apply (Hpast k j); [lia|exact Hj]].
      exfalso. rewrite <- Hn, (pending_shape _ (proj2 (proj2 Hgood))) in Hj.
      unfold pending in Hj. destruct (at_collective c) as [[x c'']|] eqn:Hat;
        [|discriminate].
      rewrite (at_collective_blocks _ _ _ tid input (memory (base s)) Hat) in Hthread.
      discriminate.
  - apply spec_release_view in Hstep as [Hnot [Harrived [He [Hbase Hdone]]]].
    rewrite Hbase, Hdone. cbn [threads]. unfold release.
    rewrite Forall_forall in Hinv |- *. intros c' Hin.
    apply in_map_iff in Hin as [c [<- Hc]]. specialize (Hinv c Hc).
    unfold release_one. destruct (at_collective c) as [[i' c'']|] eqn:Hat.
    + destruct (instance_eqb i i') eqn:Heq.
      * apply instance_eqb_true in Heq. subst i'.
        destruct Hinv as [Hgood [n [Hn Hpast]]].
        split; [eapply release_good; eauto|].
        exists (S n). split.
        -- rewrite (release_shape _ _ _ Hat (proj2 (proj2 Hgood))), Hn. reflexivity.
        -- intros k j Hk Hj. destruct (Nat.eq_dec k n) as [->|Hne].
           ++ left. rewrite <- Hn, (pending_shape _ (proj2 (proj2 Hgood))) in Hj.
              unfold pending in Hj. rewrite Hat in Hj. cbn in Hj. congruence.
           ++ right. apply (Hpast k j); [lia|exact Hj].
      * eapply on_path_mono; [|exact Hinv]. intros x Hx; right; exact Hx.
    + eapply on_path_mono; [|exact Hinv]. intros x Hx; right; exact Hx.
Qed.

(* A thread at or before a released instance on the path stays there. *)
Definition behind (start : code) (u limit : nat) (s : spec_state) : Prop :=
  exists c n, nth_error (threads (base s)) u = Some c /\ shape c = path start n /\
    n <= limit.

Lemma behind_advance : forall start input a s e s' u limit i,
  spec_inv start s -> spec_advance input a s = Some (e, s') ->
  pending (path start limit) = Some i -> In i (released s) ->
  behind start u limit s -> behind start u limit s'.
Proof.
  intros start input [tid|j] s e s' u limit i Hinv Hstep Hlimit Hi [c [n [Hc [Hn Hle]]]];
    unfold spec_inv in Hinv; rewrite Forall_forall in Hinv; unfold behind.
  - apply spec_thread_view in Hstep as [Hadv _].
    apply thread_view in Hadv as [d [o [m' [d' [Hd [Hthread [_ Hs']]]]]]].
    rewrite Hs'. cbn [threads]. destruct (Nat.eq_dec tid u) as [->|Hne].
    + rewrite Hc in Hd. inversion Hd; subst d.
      destruct (Hinv c (nth_error_In _ _ Hc)) as [Hgood _].
      exists d'. rewrite replace_thread_same by (eapply nth_error_Some_lt; eauto).
      destruct (good_step_shape _ _ _ _ _ _ _ Hthread Hgood) as [Hsame|Hnext].
      * exists n. split; [reflexivity|]. split; [now rewrite Hsame|exact Hle].
      * exists (S n). split; [reflexivity|]. split; [rewrite Hnext, Hn; reflexivity|].
        destruct (Nat.eq_dec n limit) as [->|Hne]; [|lia].
        exfalso. rewrite <- Hn, (pending_shape _ (proj2 (proj2 Hgood))) in Hlimit.
        unfold pending in Hlimit.
        destruct (at_collective c) as [[x c'']|] eqn:Hat; [|discriminate].
        rewrite (at_collective_blocks _ _ _ u input (memory (base s)) Hat) in Hthread.
        discriminate.
    + exists c, n. rewrite replace_thread_other by congruence. auto.
  - apply spec_release_view in Hstep as [Hnot [_ [_ [Hbase _]]]].
    rewrite Hbase. cbn [threads]. rewrite release_nth, Hc. cbn [option_map].
    destruct (waits_at j c) eqn:Hw.
    + apply waits_at_true in Hw as [c'' Hat].
      rewrite (release_one_waiting _ _ _ Hat).
      destruct (Hinv c (nth_error_In _ _ Hc)) as [Hgood _].
      exists c'', (S n). split; [reflexivity|]. split.
      * rewrite (release_shape _ _ _ Hat (proj2 (proj2 Hgood))), Hn. reflexivity.
      * destruct (Nat.eq_dec n limit) as [->|Hne]; [|lia].
        exfalso. rewrite <- Hn, (pending_shape _ (proj2 (proj2 Hgood))) in Hlimit.
        unfold pending in Hlimit. rewrite Hat in Hlimit. cbn in Hlimit.
        inversion Hlimit; subst. contradiction.
    + rewrite (release_one_other _ _ Hw). exists c, n. auto.
Qed.

Lemma behind_never_finishes : forall start input s trace last u limit i,
  spec_execution input s trace last -> spec_inv start s ->
  pending (path start limit) = Some i -> In i (released s) ->
  behind start u limit s -> ~ finished (base last).
Proof.
  intros start input s trace last u limit i Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH];
    intros Hinv Hlimit Hi Hbehind Hdone.
  - destruct Hbehind as [c [n [Hc [Hn Hle]]]].
    unfold finished in Hdone. rewrite Forall_forall in Hdone.
    rewrite (Hdone c (nth_error_In _ _ Hc)) in Hn. cbn in Hn. symmetry in Hn.
    rewrite (path_skip _ _ _ Hn Hle) in Hlimit. discriminate.
  - apply (IH (spec_advance_inv _ _ _ _ _ _ Hinv Hstep) Hlimit).
    + exact (spec_advance_released _ _ _ _ _ Hstep i Hi).
    + eapply behind_advance; eauto.
    + exact Hdone.
Qed.

(* In a completed run, Spec releases an instance only when every thread
   waits at it: a thread ahead on the path passed the instance, which is
   released once, and a thread behind would arrive after the release and
   never finish. So the release is SSO-enabled. *)
Lemma completed_spec_is_sso : forall start input s trace last,
  spec_execution input s trace last -> finished (base last) -> spec_inv start s ->
  execution input (base s) trace (base last).
Proof.
  intros start input s trace last Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; intros Hdone Hinv;
    [constructor|].
  pose proof (spec_advance_inv _ _ _ _ _ _ Hinv Hstep) as Hinv'.
  apply (execution_step input a (base s) e (base s') trace (base last));
    [|exact (IH Hdone Hinv')].
  destruct a as [tid|i]; [exact (proj1 (spec_thread_view _ _ _ _ _ Hstep))|].
  pose proof Hstep as Hview.
  apply spec_release_view in Hview as [Hnot [Harrived [-> [Hbase Hreleased]]]].
  rewrite Hbase. apply release_build; [exact Harrived|].
  apply select_nil. intros u cu Hu.
  enough (Hw : waits_at i cu = true) by (cbv beta; rewrite Hw; apply andb_false_r).
  destruct (arrived i (threads (base s))) as [|t rest] eqn:Harr; [congruence|].
  assert (Ht : In t (arrived i (threads (base s)))) by (rewrite Harr; left; reflexivity).
  apply select_spec in Ht as [ct [Hct Hwt]].
  unfold spec_inv in Hinv. rewrite Forall_forall in Hinv.
  destruct (Hinv ct (nth_error_In _ _ Hct)) as [Hgood_t [nt [Hnt _]]].
  destruct (Hinv cu (nth_error_In _ _ Hu)) as [Hgood_u [nu [Hnu Hpast_u]]].
  assert (Hpt : pending (path start nt) = Some i).
  { rewrite <- Hnt, (pending_shape _ (proj2 (proj2 Hgood_t))). now apply waits_pending. }
  destruct (Nat.lt_total nu nt) as [Hlt|[Heq|Hgt]].
  - destruct (waits_at i cu) eqn:Hw; [reflexivity|exfalso].
    apply (behind_never_finishes start input s' trace last u nt i Hexec Hinv' Hpt);
      [rewrite Hreleased; left; reflexivity| |exact Hdone].
    exists cu, nu. rewrite Hbase. cbn [threads]. rewrite release_nth, Hu.
    cbn [option_map]. rewrite (release_one_other _ _ Hw).
    split; [reflexivity|]. split; [exact Hnu|lia].
  - subst nu. apply pending_waits.
    rewrite <- (pending_shape _ (proj2 (proj2 Hgood_u))), Hnu. exact Hpt.
  - exfalso. apply Hnot. exact (Hpast_u nt i Hgt Hpt).
Qed.

Lemma spec_inv_initial : forall p programs,
  placed false p = true -> has_jump p = false ->
  Forall (fun c => c = p) programs -> well_sited programs ->
  spec_inv (shape p) (spec_initial programs).
Proof.
  intros p programs Hplaced Hjump Hsame Hsited.
  unfold spec_inv, spec_initial, initial. cbn [base released threads].
  unfold well_sited in Hsited. rewrite Forall_forall in Hsame, Hsited |- *.
  intros c Hin. destruct (Hsited c Hin) as [Hstatic _]. rewrite (Hsame c Hin) in *.
  split; [split; [exact Hplaced|split; [exact Hjump|now apply static_loops_ok]]|].
  exists 0. split; [reflexivity|]. intros k j Hk. lia.
Qed.

(* Spec conforms to the full-warp configuration: its completed runs of a
   full-warp kernel are SSO runs, so sso_agreement covers them. *)
Theorem completed_full_warp_spec_is_sso : forall programs input trace last,
  well_sited programs -> warp_uniform programs ->
  spec_execution input (spec_initial programs) trace last -> finished (base last) ->
  execution input (initial programs) trace (base last).
Proof.
  intros programs input trace last Hsited [p [Hplaced [Hjump Hsame]]] Hexec Hdone.
  exact (completed_spec_is_sso (shape p) _ _ _ _ Hexec Hdone
    (spec_inv_initial _ _ Hplaced Hjump Hsame Hsited)).
Qed.

Theorem spec_full_warp_agreement : forall programs fuel input reference_trace
    reference_last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  conditions FullWarp programs reference_trace ->
  forall trace last,
  spec_execution input (spec_initial programs) trace last -> finished (base last) ->
  same_observations input reference_trace reference_last trace (base last).
Proof.
  intros programs fuel input reference_trace reference_last Hrun Hconditions
    trace last Hexec Hdone.
  pose proof Hconditions as [_ [Hplacement _]].
  pose proof Hrun as Hsound. apply run_sound in Hsound as [Hsited _].
  apply (sso_agreement FullWarp _ _ _ _ _ Hrun Hconditions); [|exact Hdone].
  exact (completed_full_warp_spec_is_sso _ _ _ _ Hsited Hplacement Hexec Hdone).
Qed.

(* Examples. *)

Definition zero_input (_ : nat) := 0.

(* Spec can release early in warp-uniform code, but the thread it left out
   arrives after the release and waits forever. *)
Definition late := Seq (Write NTid (NNum 1)) AddZero.

Example early_release_gets_stuck :
  exists s,
  spec_run zero_input [Thread 0; Thread 0; Release (AddSite, []); Thread 1; Thread 1]
    (spec_initial [late; late]) =
    Some ([Memory (Observe (av_write 0 0) 1); Sync (AddSite, []) [0];
           Memory (Observe (av_write 1 1) 1)], s) /\
  forall trace last, spec_execution zero_input s trace last -> ~ finished (base last).
Proof.
  eexists. split; [vm_compute; reflexivity|].
  intros trace last Hexec.
  apply (late_arrival_stuck _ _ _ _ 1 (AddSite, []) AddZero Hexec);
    [reflexivity|reflexivity|left; reflexivity].
Qed.

(* Condition 2 is needed. Both threads read a flag and, when it is zero,
   meet at AddZero; afterwards thread 0 sets the flag. The reference orders
   thread 1's read before thread 0's write through the collective, so the
   kernel is memory-DRF. The collective sits under a test of a value read
   from memory, which the full-warp configuration does not permit, and Spec
   runs thread 0 alone through it. *)
Definition flag := variable "flag".

Definition single_writer :=
  Read flag (NNum 0)
    (Cond (NRel NEquals (NVar flag) (NNum 0))
      (Seq AddZero
        (Cond (NRel NEquals NTid (NNum 0)) (Write (NNum 0) (NNum 1)) Skip))
      Skip).

Definition single_writer_reference_trace :=
  [Memory (Observe (av_read 0 0) 0); Memory (Observe (av_read 1 0) 0);
   Sync (AddSite, []) [0; 1]; Memory (Observe (av_write 0 0) 1)].

Example single_writer_reference :
  exists last,
  run 100 zero_input [single_writer; single_writer] =
    Some (single_writer_reference_trace, last) /\ finished last.
Proof. eexists; split; [vm_compute; reflexivity|unfold finished; repeat constructor]. Qed.

Ltac hb_link t :=
  split; [lia|]; do 2 eexists; exists t;
  split; [reflexivity|]; split; [reflexivity|]; cbn; split; auto.

Theorem single_writer_memory_drf : MemDRF single_writer_reference_trace.
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace i)). rewrite He.
    discriminate. }
  assert (Hj : j < 4).
  { apply (proj1 (nth_error_Some single_writer_reference_trace j)). rewrite Hf.
    discriminate. }
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; cbn in *; congruence].
  - left. apply t_trans with 2; apply t_step; [hb_link 1|hb_link 0].
  - right. apply t_trans with 2; apply t_step; [hb_link 1|hb_link 0].
Qed.

Lemma single_writer_not_full_warp :
  ~ UnambiguousParticipation FullWarp [single_writer; single_writer]
      single_writer_reference_trace.
Proof.
  intros [[p [Hplaced [_ Hsame]]] _].
  inversion Hsame as [|c l Hc _]; subst. vm_compute in Hplaced. discriminate.
Qed.

Definition speculative_trace :=
  [Memory (Observe (av_read 0 0) 0); Sync (AddSite, []) [0];
   Memory (Observe (av_write 0 0) 1); Memory (Observe (av_read 1 0) 1)].

Example single_writer_speculative :
  exists last,
  spec_run zero_input
    [Thread 0; Thread 0; Release (AddSite, []); Thread 0; Thread 0; Thread 0;
     Thread 1; Thread 1]
    (spec_initial [single_writer; single_writer]) = Some (speculative_trace, last) /\
  finished (base last).
Proof. eexists; split; [vm_compute; reflexivity|unfold finished; repeat constructor]. Qed.

Theorem participation_condition_needed :
  exists programs fuel input reference_trace reference_last trace last,
    run fuel input programs = Some (reference_trace, reference_last) /\
    MemDRF reference_trace /\
    ~ UnambiguousParticipation FullWarp programs reference_trace /\
    spec_execution input (spec_initial programs) trace last /\ finished (base last) /\
    ~ same_observations input reference_trace reference_last trace (base last).
Proof.
  destruct single_writer_reference as [reference_last [Hrun _]].
  destruct single_writer_speculative as [last [Hspec Hdone]].
  exists [single_writer; single_writer], 100, zero_input, single_writer_reference_trace,
    reference_last, speculative_trace, last.
  split; [exact Hrun|]. split; [exact single_writer_memory_drf|].
  split; [exact single_writer_not_full_warp|].
  split; [eapply spec_run_sound; exact Hspec|]. split; [exact Hdone|].
  intros [Hgroups _]. specialize (Hgroups (AddSite, [])).
  vm_compute in Hgroups. discriminate.
Qed.

(* So memory DRF alone does not give agreement on a conforming target. *)
Corollary memory_drf_alone_insufficient :
  ~ (forall programs fuel input reference_trace reference_last,
       run fuel input programs = Some (reference_trace, reference_last) ->
       MemDRF reference_trace ->
       forall trace last,
       spec_execution input (spec_initial programs) trace last -> finished (base last) ->
       same_observations input reference_trace reference_last trace (base last)).
Proof.
  intros Hagree.
  destruct participation_condition_needed
    as [programs [fuel [input [reference_trace [reference_last [trace [last
      [Hrun [Hdrf [_ [Hexec [Hdone Hdiffer]]]]]]]]]]]].
  exact (Hdiffer (Hagree _ _ _ _ _ Hrun Hdrf _ _ Hexec Hdone)).
Qed.

(* Spec does not conform to the structured partial configuration: the same
   kernel meets both of its conditions. *)
Theorem spec_not_structured_partial :
  exists programs fuel input reference_trace reference_last trace last,
    run fuel input programs = Some (reference_trace, reference_last) /\
    conditions StructuredPartial programs reference_trace /\
    spec_execution input (spec_initial programs) trace last /\ finished (base last) /\
    ~ same_observations input reference_trace reference_last trace (base last).
Proof.
  destruct participation_condition_needed
    as [programs [fuel [input [reference_trace [reference_last [trace [last
      [Hrun [Hdrf [_ [Hexec [Hdone Hdiffer]]]]]]]]]]]].
  exists programs, fuel, input, reference_trace, reference_last, trace, last.
  split; [exact Hrun|].
  split; [split; [exact Hdrf|eapply reference_structured_partial; eauto]|].
  split; [exact Hexec|]. split; [exact Hdone|exact Hdiffer].
Qed.
