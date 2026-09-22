From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import NatUtil AVal.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation Contract TraceOrder.
From Faial.Warp Require Lang.

Import ListNotations.

(* Replay an observed write; reads and control steps leave memory unchanged. *)
Definition effect (e : option observation) (m : Mem.t) : Mem.t :=
  match e with
  | Some (Observe a v) =>
      match av_mode a with
      | m_read => m
      | m_write => Map_NAT.add (av_index a) v m
      end
  | None => m
  end.

Definition readable input m (e : option observation) : Prop :=
  match e with
  | Some (Observe a v) =>
      match av_mode a with
      | m_read => load input m (av_index a) = v
      | m_write => True
      end
  | None => True
  end.

(* A thread's next operation depends on its code. Only a read's result depends
   on shared memory; replaying that value also preserves the continuation. *)
Lemma thread_step_replay : forall code tid input m e m' code',
  thread_step tid input m code = Some (e, m', code') ->
  m' = effect e m /\ readable input m e /\
  (forall o, e = Some o -> av_owner (access o) = tid) /\
  (forall n, readable input n e ->
    thread_step tid input n code = Some (e, effect e n, code')).
Proof.
  induction code; intros tid input m e m' code' Hstep; cbn in Hstep;
    try discriminate.
  - destruct (n_step tid n) eqn:Haddress; try discriminate.
    inversion Hstep; subst. repeat split; try reflexivity.
    + intros o Ho; inversion Ho; reflexivity.
    + intros other Hread. cbn in Hread. cbn. rewrite Haddress, Hread. reflexivity.
  - destruct (n_step tid n) eqn:Haddress, (n_step tid n0) eqn:Hvalue;
      try discriminate.
    inversion Hstep; subst. repeat split; try reflexivity.
    + intros o Ho; inversion Ho; reflexivity.
    + intros other _. cbn. rewrite Haddress, Hvalue. reflexivity.
  - destruct code1; cbn -[thread_step] in Hstep.
    all: try solve [inversion Hstep; subst; repeat split;
      try reflexivity; intros o Ho; discriminate].
    all: match type of Hstep with
    | context [thread_step ?owner ?base ?mem ?first] =>
        destruct (thread_step owner base mem first)
          as [[[event next_mem] next_code]|] eqn:Hfirst; try discriminate;
        inversion Hstep; subst;
        destruct (IHcode1 _ _ _ _ _ _ Hfirst) as [Hmem [Hread [Howner Hreplay]]];
        repeat split; try assumption;
        intros other Hread';
        change (match thread_step owner base other first with
          | Some (ev, mem', first') => Some (ev, mem', Lang.Seq first' code2)
          | None => None end = Some (e, effect e other, Lang.Seq next_code code2));
        rewrite (Hreplay other Hread');
        reflexivity
    end.
  - destruct (b_step tid b) eqn:Htest; try discriminate.
    inversion Hstep; subst. repeat split; try reflexivity.
    + intros o Ho; discriminate.
    + intros other _. cbn. rewrite Htest. reflexivity.
Qed.

Lemma effect_equiv : forall input m n e,
  (forall address, load input m address = load input n address) ->
  forall address, load input (effect e m) address = load input (effect e n) address.
Proof.
  intros input m n [[[t index mode] v]|] Heq address; cbn; auto.
  destruct mode; cbn; auto.
  unfold load in *. destruct (Nat.eq_dec index address); subst;
    [rewrite !Map_NAT_Facts.add_eq_o by reflexivity|
     rewrite !Map_NAT_Facts.add_neq_o by assumption]; auto.
Qed.

Lemma readable_equiv : forall input m n e,
  (forall address, load input m address = load input n address) ->
  readable input m e -> readable input n e.
Proof.
  intros input m n [[[t index mode] v]|] Heq Hr; cbn in *; auto.
  destruct mode; cbn in *; auto. now rewrite <- Heq.
Qed.

Lemma thread_step_equiv : forall tid input m n code e m' code',
  (forall address, load input m address = load input n address) ->
  thread_step tid input m code = Some (e, m', code') ->
  exists n', thread_step tid input n code = Some (e, n', code') /\
    (forall address, load input m' address = load input n' address).
Proof.
  intros tid input m n code e m' code' Heq Hstep.
  apply thread_step_replay in Hstep as [-> [Hr [_ Hreplay]]].
  exists (effect e n). split.
  - apply Hreplay. eapply readable_equiv; eauto.
  - now apply effect_equiv.
Qed.

Definition state_equiv input (s t : state) :=
  threads (machine s) = threads (machine t) /\
  decisions s = decisions t /\ participants s = participants t /\
  (forall address, load input (memory (machine s)) address =
                   load input (memory (machine t)) address).

Lemma state_equiv_refl : forall input s, state_equiv input s s.
Proof. intros; repeat split; reflexivity. Qed.

Lemma state_equiv_trans : forall input s t u,
  state_equiv input s t -> state_equiv input t u -> state_equiv input s u.
Proof.
  intros input s t u [Hc [Hd [Hp Hm]]] [Hc' [Hd' [Hp' Hm']]].
  repeat split; congruence.
Qed.

Lemma finished_equiv : forall input s t,
  state_equiv input s t -> finished s -> finished t.
Proof.
  intros input s t [Hc [Hd _]] [Hc' Hd'].
  unfold finished, Semantics.finished in *. now rewrite <- Hc, <- Hd.
Qed.

Lemma advance_equiv : forall input p a s t e s',
  state_equiv input s t -> advance p input a s = Some (e, s') ->
  exists t', advance p input a t = Some (e, t') /\ state_equiv input s' t'.
Proof.
  intros input p [tid|] [[m codes] ds group] [[n codes'] ds' group'] e s'
    [Hcodes [Hds [Hgroup Hmem]]] Hstep;
    cbn in Hcodes, Hds, Hgroup, Hmem; subst codes' ds' group'.
  - cbn [advance machine decisions participants Semantics.threads Semantics.memory] in *.
    destruct (nth_error codes tid) as [code|] eqn:Hcode; try discriminate.
    destruct (branch_decision tid code) as [b|];
      [destruct (nth_error ds tid) as [[]|];
        destruct group; destruct b; try discriminate|].
    all: destruct (thread_step tid input m code) as [[[ev m'] code']|] eqn:Hthread;
      try discriminate.
    all: destruct (thread_step_equiv _ _ _ _ _ _ _ _ Hmem Hthread)
      as [n' [Hother Hmem']]; rewrite Hother;
      inversion Hstep; subst; eexists; split; [reflexivity|];
      repeat split; try reflexivity; exact Hmem'.
  - cbn [advance machine decisions participants Semantics.threads Semantics.memory] in *.
    destruct group; try discriminate.
    destruct (entered_threads ds); try discriminate.
    destruct (match p with SSO => all_decided ds | Spec => true end); try discriminate.
    destruct (release_collective ds codes); try discriminate.
    inversion Hstep; subst; eexists; split; [reflexivity|].
    repeat split; try reflexivity; exact Hmem.
Qed.

Lemma execution_equiv : forall p input s trace last,
  execution p input s trace last -> forall t,
  state_equiv input s t -> exists final,
  execution p input t trace final /\ state_equiv input last final.
Proof.
  intros p input s trace last Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; intros t Heq.
  - exists t; split; [constructor|assumption].
  - destruct (advance_equiv _ _ _ _ _ _ _ Heq Hstep) as [t' [Hstep' Heq']].
    destruct (IH _ Heq') as [final [Hrun Hfinal]].
    exists final; split; [econstructor; eauto|assumption].
Qed.

Definition compatible (e f : option observation) : Prop :=
  forall x y, e = Some x -> f = Some y ->
  av_index (access x) <> av_index (access y) \/
  (av_mode (access x) = m_read /\ av_mode (access y) = m_read).

Lemma compatible_sym : forall e f, compatible e f -> compatible f e.
Proof.
  intros e f H y x Hy Hx. specialize (H x y Hx Hy). intuition congruence.
Qed.

Lemma nonconflicting_compatible : forall t u e f,
  t <> u ->
  (forall x, e = Some x -> av_owner (access x) = t) ->
  (forall y, f = Some y -> av_owner (access y) = u) ->
  (forall x y, e = Some x -> f = Some y -> ~ Conflict (access x) (access y)) ->
  compatible e f.
Proof.
  intros t u e f Hneq He Hf Hsafe x y Hx Hy.
  specialize (He _ Hx). specialize (Hf _ Hy). specialize (Hsafe _ _ Hx Hy).
  apply safe_not_conflict_rw in Hsafe. inversion Hsafe; intuition congruence.
Qed.

Lemma load_effect_other : forall input m e address,
  (forall o, e = Some o -> av_mode (access o) = m_write ->
    address <> av_index (access o)) ->
  load input (effect e m) address = load input m address.
Proof.
  intros input m [[[owner index mode] v]|] address H; cbn; auto.
  destruct mode; cbn; auto.
  unfold load. rewrite Map_NAT_Facts.add_neq_o; [reflexivity|].
  specialize (H (Observe (av_write owner index) v) eq_refl eq_refl).
  cbn in H. congruence.
Qed.

Lemma readable_effect : forall input m e f,
  compatible e f -> (readable input (effect e m) f <-> readable input m f).
Proof.
  intros input m e [[[owner index mode] v]|] H; cbn; try tauto.
  destruct mode; cbn; try tauto.
  rewrite load_effect_other; [tauto|].
  intros o Ho Hwrite.
  specialize (H o (Observe (av_read owner index) v) Ho eq_refl).
  cbn in H. intuition congruence.
Qed.

Lemma effects_commute : forall input m e f,
  compatible e f -> forall address,
  load input (effect e (effect f m)) address =
  load input (effect f (effect e m)) address.
Proof.
  intros input m [[[t x xm] v]|] [[[u y ym] w]|] H address; cbn; auto.
  destruct xm, ym; cbn; auto.
  assert (Hxy : x <> y).
  { specialize (H (Observe (av_write t x) v) (Observe (av_write u y) w)
      eq_refl eq_refl). cbn in H. intuition discriminate. }
  unfold load. destruct (Nat.eq_dec x address), (Nat.eq_dec y address);
    subst; try congruence;
    repeat first [rewrite Map_NAT_Facts.add_eq_o by reflexivity |
                  rewrite Map_NAT_Facts.add_neq_o by congruence];
    reflexivity.
Qed.

Theorem thread_steps_swap : forall input t u m left right e m1 left' f m2 right',
  t <> u ->
  thread_step t input m left = Some (e, m1, left') ->
  thread_step u input m1 right = Some (f, m2, right') ->
  (forall x y, e = Some x -> f = Some y -> ~ Conflict (access x) (access y)) ->
  exists n1 n2,
  thread_step u input m right = Some (f, n1, right') /\
  thread_step t input n1 left = Some (e, n2, left') /\
  (forall address, load input n2 address = load input m2 address).
Proof.
  intros input t u m left right e m1 left' f m2 right' Hneq Hleft Hright Hsafe.
  apply thread_step_replay in Hleft as [Hm1 [He [Howner Hleft]]].
  apply thread_step_replay in Hright as [Hm2 [Hf [Howner' Hright]]].
  assert (Hcompat : compatible e f) by (eapply nonconflicting_compatible; eauto).
  subst m1 m2.
  exists (effect f m), (effect e (effect f m)). repeat split.
  - apply Hright. now apply (proj1 (readable_effect _ _ _ _ Hcompat)).
  - apply Hleft. apply (proj2 (readable_effect _ _ _ _ (compatible_sym _ _ Hcompat))).
    exact He.
  - apply effects_commute. exact Hcompat.
Qed.

Local Definition decide (group : option (list nat)) tid branch (ds : list decision) :=
  match branch with
  | None => Some ds
  | Some b =>
      match nth_error ds tid, group, b with
      | Some Unresolved, None, _ | Some Unresolved, Some _, false =>
          Some (firstn tid ds ++ [if b then Entered else Skipped] ++ skipn (S tid) ds)
      | _, _, _ => None
      end
  end.

Local Lemma decision_other : forall (ds : list decision) t u d,
  t <> u -> t < length ds ->
  nth_error (firstn t ds ++ [d] ++ skipn (S t) ds) u = nth_error ds u.
Proof.
  induction ds as [|head ds IH]; intros [|t] [|u] d Hneq Hbound;
    cbn in *; try lia; auto.
  apply IH; lia.
Qed.

Local Lemma decisions_commute : forall (ds : list decision) t u d e,
  t <> u -> t < length ds -> u < length ds ->
  firstn u (firstn t ds ++ [d] ++ skipn (S t) ds) ++ [e] ++
    skipn (S u) (firstn t ds ++ [d] ++ skipn (S t) ds) =
  firstn t (firstn u ds ++ [e] ++ skipn (S u) ds) ++ [d] ++
    skipn (S t) (firstn u ds ++ [e] ++ skipn (S u) ds).
Proof.
  induction ds as [|head ds IH]; intros [|t] [|u] d e Hneq Ht Hu;
    cbn in *; try lia; auto.
  f_equal. apply IH; lia.
Qed.

Local Lemma decide_other : forall group t u b ds ds',
  decide group t b ds = Some ds' -> t <> u ->
  nth_error ds' u = nth_error ds u.
Proof.
  intros group t u [b|] ds ds' H Hneq; cbn [decide] in H.
  - destruct (nth_error ds t) as [[]|] eqn:Ht; try discriminate.
    assert (Hbound : t < length ds).
    { apply (proj1 (nth_error_Some ds t)); rewrite Ht; discriminate. }
    destruct group, b; try discriminate; inversion H; subst.
    all: apply decision_other; assumption.
  - inversion H; subst; auto.
Qed.

Local Lemma decide_swap : forall group t u b c ds ds1 ds2,
  t <> u -> decide group t b ds = Some ds1 ->
  decide group u c ds1 = Some ds2 ->
  exists ds1', decide group u c ds = Some ds1' /\
    decide group t b ds1' = Some ds2.
Proof.
  intros group t u [b|] [c|] ds ds1 ds2 Hneq Hfirst Hsecond.
  - pose proof (decide_other _ _ _ _ _ _ Hfirst Hneq) as Hu.
    cbn [decide] in Hfirst, Hsecond. rewrite Hu in Hsecond.
    destruct (nth_error ds t) as [[]|] eqn:Ht; try discriminate.
    destruct (nth_error ds u) as [[]|] eqn:Hu'; try discriminate.
    assert (Hbt : t < length ds).
    { apply (proj1 (nth_error_Some ds t)); rewrite Ht; discriminate. }
    assert (Hbu : u < length ds).
    { apply (proj1 (nth_error_Some ds u)); rewrite Hu'; discriminate. }
    destruct group, b, c; try discriminate; inversion Hfirst; subst ds1;
      inversion Hsecond; subst ds2.
    all: eexists; split; [cbn [decide]; rewrite Hu'; reflexivity|];
      cbn [decide]; rewrite decision_other by lia; rewrite Ht;
      f_equal; apply decisions_commute; lia.
  - cbn [decide] in Hsecond. inversion Hsecond; subst.
    exists ds; split; [reflexivity|assumption].
  - cbn [decide] in Hfirst. inversion Hfirst; subst.
    exists ds2; split; [assumption|reflexivity].
  - cbn [decide] in Hfirst, Hsecond. inversion Hfirst; inversion Hsecond; subst.
    eauto.
Qed.

Lemma thread_advance_view : forall p input tid s e s',
  advance p input (Thread tid) s = Some (e, s') ->
  exists code o m' code' ds',
    nth_error (threads (machine s)) tid = Some code /\
    thread_step tid input (memory (machine s)) code = Some (o, m', code') /\
    decide (participants s) tid (branch_decision tid code) (decisions s) = Some ds' /\
    e = option_map Memory o /\
    s' = State (Semantics.State m' (replace_thread tid code' (threads (machine s))))
      ds' (participants s).
Proof.
  intros p input tid s e s' Hstep. unfold advance in Hstep.
  destruct (nth_error (threads (machine s)) tid) as [code|] eqn:Hcode;
    try discriminate.
  fold (decide (participants s) tid (branch_decision tid code) (decisions s)) in Hstep.
  destruct (decide (participants s) tid (branch_decision tid code) (decisions s))
    as [ds'|] eqn:Hdecide; try discriminate.
  destruct (thread_step tid input (memory (machine s)) code)
    as [[[o m'] code']|] eqn:Hthread; try discriminate.
  inversion Hstep; subst. do 5 eexists. repeat split; eauto.
Qed.

Local Lemma thread_advance_build : forall p input tid s code o m' code' ds',
  nth_error (threads (machine s)) tid = Some code ->
  thread_step tid input (memory (machine s)) code = Some (o, m', code') ->
  decide (participants s) tid (branch_decision tid code) (decisions s) = Some ds' ->
  advance p input (Thread tid) s =
    Some (option_map Memory o,
      State (Semantics.State m' (replace_thread tid code' (threads (machine s))))
        ds' (participants s)).
Proof.
  intros p input tid s code o m' code' ds' Hcode Hthread Hdecide.
  unfold advance. rewrite Hcode.
  fold (decide (participants s) tid (branch_decision tid code) (decisions s)).
  now rewrite Hdecide, Hthread.
Qed.

Lemma replace_threads_commute : forall programs t u c d,
  t <> u ->
  replace_thread u d (replace_thread t c programs) =
  replace_thread t c (replace_thread u d programs).
Proof.
  induction programs as [|head rest IH]; intros [|t] [|u] c d Hneq;
    cbn; try congruence.
  f_equal. apply IH. congruence.
Qed.

Theorem ordinary_steps_swap : forall p input t u s e s1 f s2,
  t <> u ->
  advance p input (Thread t) s = Some (e, s1) ->
  advance p input (Thread u) s1 = Some (f, s2) ->
  (forall x y, e = Some (Memory x) -> f = Some (Memory y) ->
    ~ Conflict (access x) (access y)) ->
  exists s1' s2',
    advance p input (Thread u) s = Some (f, s1') /\
    advance p input (Thread t) s1' = Some (e, s2') /\ state_equiv input s2 s2'.
Proof.
  intros p input t u [[m codes] ds group] e s1 f s2 Hneq Hfirst Hsecond Hsafe.
  apply thread_advance_view in Hfirst as
    [c [o [m1 [c' [ds1 [Hc [Hstep [Hdecide [-> ->]]]]]]]]].
  apply thread_advance_view in Hsecond as
    [d [o' [m2 [d' [ds2 [Hd [Hstep' [Hdecide' [-> ->]]]]]]]]].
  cbn in Hc, Hstep, Hdecide, Hd, Hstep', Hdecide', Hsafe.
  rewrite replace_thread_other in Hd by congruence.
  destruct (thread_steps_swap input t u m c d o m1 c' o' m2 d')
    as [n1 [n2 [Hu [Ht Hmem]]]]; try assumption.
  { intros x y Hx Hy. apply Hsafe; now rewrite ?Hx, ?Hy. }
  destruct (decide_swap _ _ _ _ _ _ _ _ Hneq Hdecide Hdecide')
    as [ds1' [Hdu Hdt]].
  exists (State (Semantics.State n1 (replace_thread u d' codes)) ds1' group),
    (State (Semantics.State n2 (replace_thread t c' (replace_thread u d' codes))) ds2 group).
  split; [eapply thread_advance_build; eauto|]. split.
  - eapply thread_advance_build; cbn; eauto.
    now rewrite replace_thread_other by congruence.
  - repeat split; cbn; auto using replace_threads_commute.
Qed.

Lemma waiting_thread_cannot_step : forall code code' tid input m,
  at_add_zero code = Some code' -> thread_step tid input m code = None.
Proof.
  induction code; intros code' tid input m Hwait; cbn in Hwait; try discriminate.
  - destruct (at_add_zero code1) as [first'|] eqn:Hfirst; try discriminate.
    specialize (IHcode1 _ tid input m eq_refl).
    destruct code1; try discriminate; try reflexivity.
    change (match thread_step tid input m (Lang.Seq code1_1 code1_2) with
        | Some (e, m', c') => Some (e, m', Lang.Seq c' code2)
        | None => None end = None); now rewrite IHcode1.
  - reflexivity.
Qed.

Local Lemma all_decided_not_unresolved : forall ds tid,
  all_decided ds = true -> nth_error ds tid = Some Unresolved -> False.
Proof.
  intros ds tid Hall Hnth. unfold all_decided in Hall.
  apply forallb_forall with (x := Unresolved) in Hall; [discriminate|].
  now apply nth_error_In in Hnth.
Qed.

Local Lemma decided_no_update : forall ds tid branch group ds',
  all_decided ds = true -> decide group tid branch ds = Some ds' ->
  branch = None /\ ds' = ds.
Proof.
  intros ds tid [b|] group ds' Hall Hstep; cbn [decide] in Hstep.
  - destruct (nth_error ds tid) as [[]|] eqn:Htid; try discriminate.
    exfalso. eapply all_decided_not_unresolved; eauto.
  - inversion Hstep; auto.
Qed.

Lemma release_collective_at : forall ds codes codes' tid d code,
  release_collective ds codes = Some codes' ->
  nth_error ds tid = Some d -> nth_error codes tid = Some code ->
  exists code', nth_error codes' tid = Some code' /\
    match d with
    | Entered => at_add_zero code = Some code'
    | _ => code' = code
    end.
Proof.
  induction ds as [|head ds IH]; intros [|first codes] codes' [|tid] d code Hr Hd Hc;
    cbn in *; try discriminate.
  all: destruct (release_collective ds codes) as [rest'|] eqn:Hrest; try discriminate.
  - inversion Hd; inversion Hc; subst. destruct d;
      try (inversion Hr; subst; eexists; split; reflexivity).
    destruct (at_add_zero code) as [code'|] eqn:Hcode; try discriminate.
    inversion Hr; subst; eauto.
  - destruct head; try (inversion Hr; subst; eapply IH; eauto).
    destruct (at_add_zero first) as [first'|]; try discriminate.
    inversion Hr; subst; eapply IH; eauto.
Qed.

Lemma release_collective_length : forall ds codes codes',
  release_collective ds codes = Some codes' ->
  length ds = length codes.
Proof.
  induction ds as [|d ds IH]; intros [|c codes] codes' Hr; cbn in Hr; try discriminate.
  - inversion Hr; auto.
  - destruct (release_collective ds codes) as [rest'|] eqn:Hrest; try discriminate.
    specialize (IH _ _ Hrest). destruct d;
      try (destruct (at_add_zero c); try discriminate);
      inversion Hr; subst; cbn; lia.
Qed.

Local Lemma release_replace_skipped : forall ds codes codes' tid code,
  release_collective ds codes = Some codes' -> nth_error ds tid = Some Skipped ->
  release_collective ds (replace_thread tid code codes) =
    Some (replace_thread tid code codes').
Proof.
  induction ds as [|d ds IH]; intros [|c codes] codes' [|tid] code Hr Hd;
    cbn in *; try discriminate.
  all: destruct (release_collective ds codes) as [rest'|] eqn:Hrest; try discriminate.
  - inversion Hd; subst. inversion Hr; subst. reflexivity.
  - rewrite (IH _ _ _ code Hrest Hd).
    destruct d; try (inversion Hr; subst; reflexivity).
    destruct (at_add_zero c); try discriminate. inversion Hr; subst; reflexivity.
Qed.

Lemma collective_advance_view : forall input s e s',
  advance SSO input Collective s = Some (e, s') ->
  participants s = None /\ all_decided (decisions s) = true /\
  exists group codes',
    entered_threads (decisions s) = group /\ group <> [] /\
    release_collective (decisions s) (threads (machine s)) = Some codes' /\
    e = Some (Synchronize group) /\
    s' = State (Semantics.State (memory (machine s)) codes') (decisions s) (Some group).
Proof.
  intros input s e s' Hstep. cbn [advance] in Hstep.
  destruct (participants s) eqn:Hgroup; try discriminate.
  destruct (entered_threads (decisions s)) as [|t group] eqn:Hentered; try discriminate.
  destruct (all_decided (decisions s)) eqn:Hall; try discriminate.
  destruct (release_collective (decisions s) (threads (machine s))) as [codes'|]
    eqn:Hrelease; try discriminate.
  inversion Hstep; subst. repeat split; auto.
  exists (t :: group), codes'. repeat split; auto; discriminate.
Qed.

Theorem collective_thread_diamond : forall input s sync sc tid e st,
  advance SSO input Collective s = Some (sync, sc) ->
  advance SSO input (Thread tid) s = Some (e, st) ->
  exists last,
    advance SSO input (Thread tid) sc = Some (e, last) /\
    advance SSO input Collective st = Some (sync, last) /\
    (forall o group, e = Some (Memory o) -> sync = Some (Synchronize group) ->
      ~ In (av_owner (access o)) group).
Proof.
  intros input [[m codes] ds oldgroup] sync sc tid e st Hsync Hthread.
  apply collective_advance_view in Hsync as
    [Hnone [Hall [group [codes' [Hgroup [Hnonempty [Hrelease [-> ->]]]]]]]].
  cbn in Hnone, Hall, Hgroup, Hrelease. subst oldgroup.
  change (all_decided ds = true) in Hall.
  change (entered_threads ds = group) in Hgroup.
  apply thread_advance_view in Hthread as
    [code [o [m' [code' [ds' [Hcode [Hstep [Hdecide [-> ->]]]]]]]]].
  cbn in Hcode, Hstep, Hdecide.
  destruct (decided_no_update _ _ _ _ _ Hall Hdecide) as [Hbranch ->].
  assert (Htid : tid < length ds).
  { apply release_collective_length in Hrelease. rewrite Hrelease.
    apply (proj1 (nth_error_Some codes tid)); rewrite Hcode; discriminate. }
  destruct (nth_error ds tid) as [d|] eqn:Hd.
  2: { apply nth_error_None in Hd. lia. }
  destruct (release_collective_at _ _ _ _ _ _ Hrelease Hd Hcode)
    as [next [Hnext Hwait]].
  assert (Hskip : d = Skipped).
  { destruct d; auto.
    - exfalso; eapply all_decided_not_unresolved; eauto.
    - rewrite (waiting_thread_cannot_step _ _ _ _ _ Hwait) in Hstep. discriminate. }
  subst d. cbn in Hwait. subst next.
  exists (State (Semantics.State m' (replace_thread tid code' codes')) ds (Some group)).
  split.
  - eapply thread_advance_build; cbn; eauto. now rewrite Hbranch.
  - split.
    + cbn [advance machine decisions participants Semantics.memory Semantics.threads].
      rewrite Hgroup, Hall, (release_replace_skipped _ _ _ _ _ Hrelease Hd).
      destruct group; [contradiction|reflexivity].
    + intros obs g Hobs Hg. inversion Hg; subst g.
      pose proof (thread_step_replay _ _ _ _ _ _ _ Hstep) as [_ [_ [Howner _]]].
      destruct o as [obs'|]; try discriminate. inversion Hobs; subst obs'.
      rewrite (Howner _ eq_refl), <- Hgroup.
      unfold entered_threads. rewrite filter_In. intros [_ Hin]. rewrite Hd in Hin.
      discriminate.
Qed.

Lemma thread_step_enabled_memory : forall code tid input m e m' code' n,
  thread_step tid input m code = Some (e, m', code') ->
  exists f n' next, thread_step tid input n code = Some (f, n', next).
Proof.
  induction code; intros tid input m e m' code' other Hstep; cbn in Hstep;
    try discriminate.
  - destruct (n_step tid n) eqn:Haddress; try discriminate.
    cbn. rewrite Haddress. eauto.
  - destruct (n_step tid n) eqn:Haddress, (n_step tid n0) eqn:Hvalue;
      try discriminate.
    cbn. rewrite Haddress, Hvalue. eauto.
  - destruct code1; cbn -[thread_step] in Hstep.
    all: try solve [inversion Hstep; subst; do 3 eexists; reflexivity].
    all: match type of Hstep with
    | context [thread_step ?owner ?base ?mem ?first] =>
        destruct (thread_step owner base mem first)
          as [[[ev next_mem] next_code]|] eqn:Hfirst; try discriminate;
        destruct (IHcode1 _ _ _ _ _ _ other Hfirst) as [f [n' [next Hnext]]];
        exists f, n', (Lang.Seq next code2);
        change (match thread_step owner base other first with
          | Some (ev, mem', first') => Some (ev, mem', Lang.Seq first' code2)
          | None => None end = Some (f, n', Lang.Seq next code2)); now rewrite Hnext
    end.
  - destruct (b_step tid b) eqn:Htest; try discriminate.
    cbn. rewrite Htest. eauto.
Qed.

Definition enabled input a s := exists e s', advance SSO input a s = Some (e, s').

Lemma ordinary_enabled_after_other : forall input t u s e s',
  t <> u -> advance SSO input (Thread t) s = Some (e, s') ->
  enabled input (Thread u) s -> enabled input (Thread u) s'.
Proof.
  intros input t u [[m codes] ds group] e s' Hneq Hstep [f [other Hother]].
  apply thread_advance_view in Hstep as
    [c [o [m1 [c' [ds1 [Hc [Hthread [Hdecide [-> ->]]]]]]]]].
  apply thread_advance_view in Hother as
    [d [o' [m2 [d' [ds2 [Hd [Hthread' [Hdecide' _]]]]]]]].
  cbn in Hc, Hthread, Hdecide, Hd, Hthread', Hdecide'.
  destruct (thread_step_enabled_memory _ _ _ _ _ _ _ m1 Hthread')
    as [ev [mem [next Hnext]]].
  assert (Hcan : exists ds', decide group u (branch_decision u d) ds1 = Some ds').
  { pose proof (decide_other _ _ _ _ _ _ Hdecide Hneq) as Hnth.
    unfold decide in *.
    destruct (branch_decision u d) as [b|]; [rewrite Hnth|eauto].
    destruct (nth_error ds u) as [[]|], group, b; try discriminate; eauto. }
  destruct Hcan as [ds' Hcan].
  exists (option_map Memory ev),
    (State (Semantics.State mem (replace_thread u next (replace_thread t c' codes))) ds' group).
  eapply thread_advance_build; cbn; eauto.
  now rewrite replace_thread_other by congruence.
Qed.

Lemma enabled_after_distinct : forall input a b s e s',
  a <> b -> enabled input a s -> advance SSO input b s = Some (e, s') ->
  enabled input a s'.
Proof.
  intros input [t|] [u|] s e s' Hneq Ha Hb; try congruence.
  - eapply ordinary_enabled_after_other with (t := u); eauto.
  - destruct Ha as [f [st Ht]].
    destruct (collective_thread_diamond _ _ _ _ _ _ _ Hb Ht) as [last [H _]].
    exists f, last; exact H.
  - destruct Ha as [f [sc Hc]].
    destruct (collective_thread_diamond _ _ _ _ _ _ _ Hc Hb) as [last [_ [H _]]].
    exists f, last; exact H.
Qed.

Lemma finished_not_enabled : forall input s a, finished s -> ~ enabled input a s.
Proof.
  intros input s [tid|] [Hcodes Hall] [e [s' Hstep]].
  - apply thread_advance_view in Hstep as
      [code [o [m' [code' [ds' [Hcode [Hthread _]]]]]]].
    unfold Semantics.finished in Hcodes. rewrite Forall_forall in Hcodes.
    apply nth_error_In in Hcode. specialize (Hcodes _ Hcode). subst code. discriminate.
  - apply collective_advance_view in Hstep as
      [_ [_ [group [codes' [Hgroup [Hnonempty [Hrelease _]]]]]]].
    destruct group as [|tid rest]; [contradiction|].
    assert (Hin : In tid (entered_threads (decisions s))) by (rewrite Hgroup; cbn; auto).
    unfold entered_threads in Hin. apply filter_In in Hin as [Hbound Hin].
    destruct (nth_error (decisions s) tid) as [[]|] eqn:Hd; try discriminate.
    apply in_seq in Hbound.
    pose proof (release_collective_length _ _ _ Hrelease) as Hlength.
    assert (Htid : tid < length (threads (machine s))) by lia.
    destruct (nth_error (threads (machine s)) tid) as [code|] eqn:Hcode.
    2: { apply nth_error_None in Hcode; lia. }
    destruct (release_collective_at _ _ _ _ _ _ Hrelease Hd Hcode) as [next [_ Hwait]].
    unfold Semantics.finished in Hcodes. rewrite Forall_forall in Hcodes.
    apply nth_error_In in Hcode. specialize (Hcodes _ Hcode). subst code. discriminate.
Qed.

Lemma thread_event_owner : forall p input tid s e s',
  advance p input (Thread tid) s = Some (e, s') ->
  e = None \/ exists o, e = Some (Memory o) /\ av_owner (access o) = tid.
Proof.
  intros p input tid s e s' H.
  apply thread_advance_view in H as [c [o [m' [c' [ds' [_ [Hstep [_ [-> _]]]]]]]]].
  pose proof (thread_step_replay _ _ _ _ _ _ _ Hstep) as [_ [_ [Howner _]]].
  destruct o as [o|].
  - right; exists o; split; [reflexivity|now apply Howner].
  - left; reflexivity.
Qed.

Theorem steps_swap : forall input a b s e s1 f s2 trace,
  a <> b -> advance SSO input a s = Some (e, s1) ->
  advance SSO input b s1 = Some (f, s2) -> enabled input b s ->
  MemDRF (emit_event e (emit_event f trace)) ->
  exists s1' s2',
    advance SSO input b s = Some (f, s1') /\
    advance SSO input a s1' = Some (e, s2') /\ state_equiv input s2 s2' /\
    reorders (emit_event e (emit_event f trace)) (emit_event f (emit_event e trace)).
Proof.
  intros input [t|] [u|] s e s1 f s2 trace Hneq Ha Hb Henabled Hdrf; try congruence.
  - destruct (ordinary_steps_swap SSO input t u s e s1 f s2)
      as [s1' [s2' [Hu [Ht Heq]]]]; try assumption; try congruence.
    { intros x y -> -> Hconflict.
      exact (conflicting_adjacent_accesses_reject_memory_drf
        (Memory x :: Memory y :: trace) 0 x y eq_refl eq_refl Hconflict Hdrf). }
    exists s1', s2'; split; [exact Hu|]. split; [exact Ht|]. split; [exact Heq|].
    destruct (thread_event_owner _ _ _ _ _ _ Ha) as [->|[x [-> Hx]]],
      (thread_event_owner _ _ _ _ _ _ Hb) as [->|[y [-> Hy]]];
      try apply reorders_refl.
    apply (reorders_swap [] _ _ trace). cbn. congruence.
  - destruct Henabled as [sync [sc Hsync]].
    destruct (collective_thread_diamond _ _ _ _ _ _ _ Hsync Ha)
      as [last [Ht [Hc Houtside]]].
    rewrite Hb in Hc; inversion Hc; subst sync last.
    exists sc, s2; split; [assumption|]. split; [assumption|].
    split; [apply state_equiv_refl|].
    destruct (collective_advance_view _ _ _ _ Hsync)
      as [_ [_ [group [codes [_ [_ [_ [-> _]]]]]]]].
    destruct (thread_event_owner _ _ _ _ _ _ Ha) as [->|[x [-> Hx]]].
    + constructor.
    + apply (reorders_swap [] _ _ trace). cbn. eapply Houtside; reflexivity.
  - destruct Henabled as [ev [st Hthread]].
    destruct (collective_thread_diamond _ _ _ _ _ _ _ Ha Hthread)
      as [last [Ht [Hc Houtside]]].
    rewrite Hb in Ht; inversion Ht; subst ev last.
    exists st, s2; split; [assumption|]. split; [assumption|].
    split; [apply state_equiv_refl|].
    destruct (collective_advance_view _ _ _ _ Ha)
      as [_ [_ [group [codes [_ [_ [_ [-> _]]]]]]]].
    destruct (thread_event_owner _ _ _ _ _ _ Hthread) as [->|[x [-> Hx]]].
    + constructor.
    + apply (reorders_swap [] _ _ trace). cbn. eapply Houtside; reflexivity.
Qed.
