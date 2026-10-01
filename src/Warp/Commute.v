From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import AVal.
From Faial.Warp Require Import Store Code Model Order.

Import ListNotations.

(* Two states are interchangeable when every thread has the same code and
   memory holds the same values. *)
Definition state_equiv input (s t : state) :=
  threads s = threads t /\
  (forall address, load input (memory s) address =
                   load input (memory t) address).

Lemma state_equiv_refl : forall input s, state_equiv input s s.
Proof. intros; split; reflexivity. Qed.

Lemma state_equiv_trans : forall input s t u,
  state_equiv input s t -> state_equiv input t u -> state_equiv input s u.
Proof.
  intros input s t u [Hc Hm] [Hc' Hm'].
  split; [congruence|intros address; now rewrite Hm, Hm'].
Qed.

Lemma finished_equiv : forall input s t,
  state_equiv input s t -> finished s -> finished t.
Proof. intros input s t [Hc _] Hdone. unfold finished in *. now rewrite <- Hc. Qed.

Lemma advance_equiv : forall input a s t e s',
  state_equiv input s t -> advance input a s = Some (e, s') ->
  exists t', advance input a t = Some (e, t') /\ state_equiv input s' t'.
Proof.
  intros input [tid|i] [m codes] [n codes'] e s' [Hcodes Hmem] Hstep;
    cbn [threads memory] in Hcodes, Hmem; subst codes'.
  - apply thread_view in Hstep as [c [o [m' [c' [Hc [Hthread [-> ->]]]]]]].
    cbn [threads memory] in Hc, Hthread.
    destruct (step_equiv _ _ _ _ _ _ _ _ Hmem Hthread) as [n' [Hother Hmem']].
    exists (State n' (replace_thread tid c' codes)).
    split; [apply (thread_build input tid (State n codes) c); assumption|].
    split; [reflexivity|exact Hmem'].
  - apply release_view in Hstep as [Harrived [Hunknown [-> ->]]].
    cbn [threads memory] in *.
    exists (State n (release i codes)).
    split; [apply (release_build input i (State n codes)); assumption|].
    split; [reflexivity|exact Hmem].
Qed.

Lemma execution_equiv : forall input s trace last,
  execution input s trace last -> forall t,
  state_equiv input s t -> exists final,
  execution input t trace final /\ state_equiv input last final.
Proof.
  intros input s trace last Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; intros t Heq.
  - exists t; split; [constructor|assumption].
  - destruct (advance_equiv _ _ _ _ _ _ Heq Hstep) as [t' [Hstep' Heq']].
    destruct (IH _ Heq') as [final [Hrun Hfinal]].
    exists final; split; [econstructor; eauto|assumption].
Qed.

Lemma select_replace : forall p codes tid c c',
  nth_error codes tid = Some c -> p c' = p c ->
  select p (replace_thread tid c' codes) = select p codes.
Proof.
  intros p codes tid c c' Hc Hp.
  apply select_ext; [apply replace_thread_length|].
  intros i d d' Hd Hd'. destruct (Nat.eq_dec i tid) as [->|Hne].
  - rewrite replace_thread_same in Hd by (eapply nth_error_Some_lt; eauto).
    rewrite Hc in Hd'. inversion Hd; inversion Hd'; subst. exact Hp.
  - rewrite replace_thread_other in Hd by assumption.
    rewrite Hd in Hd'. now inversion Hd'.
Qed.

Lemma select_release : forall p i codes,
  (forall tid c, nth_error codes tid = Some c ->
    p (release_one i (supplied i codes) tid c) = p c) ->
  select p (release i codes) = select p codes.
Proof.
  intros p i codes H. apply select_ext; [apply release_length|].
  intros tid c c' Hc Hc'. rewrite release_nth, Hc' in Hc. cbn in Hc.
  inversion Hc; subst. eauto.
Qed.

Lemma flat_map_ext_in : forall {A B} (f g : A -> list B) l,
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H. induction l as [|a l IH]; cbn; [reflexivity|].
  rewrite H by (left; reflexivity). f_equal. apply IH.
  intros b Hb. apply H. right. exact Hb.
Qed.

Lemma supply_other : forall i tid c, waits_at i c = false -> supply i tid c = [].
Proof.
  intros i tid c H. unfold supply, waits_at in *.
  destruct (at_collective c) as [[[i' value] fn]|]; [now rewrite H|reflexivity].
Qed.

Lemma supplied_ext : forall i codes codes',
  length codes = length codes' ->
  (forall tid c c', nth_error codes tid = Some c ->
    nth_error codes' tid = Some c' -> supply i tid c = supply i tid c') ->
  supplied i codes = supplied i codes'.
Proof.
  intros i codes codes' Hlength Hext. unfold supplied. rewrite <- Hlength.
  apply flat_map_ext_in. intros tid Htid. apply in_seq in Htid.
  destruct (nth_error codes tid) as [c|] eqn:Hc, (nth_error codes' tid) as [c'|] eqn:Hc'.
  - eauto.
  - apply nth_error_None in Hc'. lia.
  - apply nth_error_None in Hc. lia.
  - reflexivity.
Qed.

Lemma supplied_release : forall i j codes,
  (forall tid c, nth_error codes tid = Some c ->
    supply j tid (release_one i (supplied i codes) tid c) = supply j tid c) ->
  supplied j (release i codes) = supplied j codes.
Proof.
  intros i j codes H. apply supplied_ext; [apply release_length|].
  intros tid c c' Hc Hc'. rewrite release_nth, Hc' in Hc. cbn in Hc.
  inversion Hc; subst. eauto.
Qed.

Lemma release_one_commute : forall i j vi vj tid c, i <> j ->
  release_one j vj tid (release_one i vi tid c) =
  release_one i vi tid (release_one j vj tid c).
Proof.
  intros i j vi vj tid c Hneq.
  destruct (at_collective c) as [[[i0 value] fn]|] eqn:Hat.
  - assert (Hfixed : forall x vx r, release_one x vx tid (resume c r) = resume c r)
      by (intros x vx r; unfold release_one; now rewrite (resume_not_waiting _ r _ Hat)).
    assert (Hother : forall x vx, x <> i0 -> release_one x vx tid c = c).
    { intros x vx Hx. apply release_one_other. unfold waits_at. rewrite Hat.
      now apply instance_eqb_false. }
    destruct (instance_eq_dec i0 i) as [->|Hi].
    + rewrite (release_one_waiting _ _ _ _ _ _ Hat), Hfixed.
      rewrite (Hother j vj) by congruence.
      now rewrite (release_one_waiting _ _ _ _ _ _ Hat).
    + destruct (instance_eq_dec i0 j) as [->|Hj].
      * rewrite (Hother i vi) by congruence. rewrite (release_one_waiting _ _ _ _ _ _ Hat).
        now rewrite Hfixed.
      * repeat first [rewrite (Hother i vi) by congruence|rewrite (Hother j vj) by congruence].
        reflexivity.
  - assert (Hfixed : forall x vx, release_one x vx tid c = c)
      by (intros x vx; unfold release_one; now rewrite Hat).
    now rewrite !Hfixed.
Qed.

(* A release and a thread step commute. The stepping thread is not waiting at
   the instance, and an enabled release leaves no thread outside its group
   that may still reach it; steps never make it reachable again. The values
   the group supplied do not change, so neither do the results. *)
Theorem thread_release_diamond : forall input i st sync sr tid e stt,
  advance input (Release i) st = Some (sync, sr) ->
  advance input (Thread tid) st = Some (e, stt) ->
  exists last,
    advance input (Thread tid) sr = Some (e, last) /\
    advance input (Release i) stt = Some (sync, last) /\
    (forall o group, e = Some (Memory o) -> sync = Some (Sync i group) ->
      ~ In (av_owner (access o)) group).
Proof.
  intros input i [m codes] sync sr tid e stt Hrelease Hthread.
  apply release_view in Hrelease as [Harrived [Hunknown [-> ->]]].
  apply thread_view in Hthread as [c [o [m' [c' [Hc [Hstep [-> ->]]]]]]].
  cbn [threads memory] in *.
  assert (Hwait : waits_at i c = false) by (eapply step_not_waiting; eauto).
  assert (Hfar : may_reach i c = false) by (eapply enabled_release_excludes; eauto).
  assert (Hfar' : may_reach i c' = false).
  { destruct (may_reach i c') eqn:Hr; [|reflexivity].
    rewrite (step_may_reach _ _ _ _ _ _ _ _ Hstep Hr) in Hfar. discriminate. }
  assert (Hwait' : waits_at i c' = false).
  { destruct (waits_at i c') eqn:Hw; [|reflexivity].
    rewrite (waits_at_reaches _ _ Hw) in Hfar'. discriminate. }
  assert (Hlt : tid < length codes) by (eapply nth_error_Some_lt; eauto).
  assert (Harrived' : arrived i (replace_thread tid c' codes) = arrived i codes).
  { apply select_replace with (c := c); [exact Hc|congruence]. }
  assert (Hunknown' : unknown i (replace_thread tid c' codes) = unknown i codes).
  { apply select_replace with (c := c); [exact Hc|]. now rewrite Hfar, Hfar'. }
  assert (Hsupplied : supplied i (replace_thread tid c' codes) = supplied i codes).
  { apply supplied_ext; [apply replace_thread_length|].
    intros t d d' Hd Hd'. destruct (Nat.eq_dec t tid) as [->|Hne].
    - rewrite replace_thread_same in Hd by exact Hlt.
      rewrite Hc in Hd'. inversion Hd; inversion Hd'; subst.
      now rewrite (supply_other _ _ _ Hwait), (supply_other _ _ _ Hwait').
    - rewrite replace_thread_other in Hd by exact Hne. rewrite Hd in Hd'.
      now inversion Hd'. }
  assert (Hcodes : release i (replace_thread tid c' codes) =
                   replace_thread tid c' (release i codes)).
  { apply nth_error_ext. intros t. rewrite release_nth, Hsupplied.
    destruct (Nat.eq_dec t tid) as [->|Hne].
    - rewrite !replace_thread_same by (rewrite ?release_length; exact Hlt). cbn.
      now rewrite (release_one_other _ _ _ _ Hwait').
    - rewrite !replace_thread_other by exact Hne. now rewrite release_nth. }
  exists (State m' (replace_thread tid c' (release i codes))).
  split; [|split].
  - apply (thread_build input tid (State m (release i codes)) c); cbn.
    + rewrite release_nth, Hc. cbn. now rewrite (release_one_other _ _ _ _ Hwait).
    + exact Hstep.
  - rewrite (release_build input i (State m' (replace_thread tid c' codes)));
      cbn [threads memory]; [|congruence|congruence].
    now rewrite Harrived', Hcodes.
  - intros obs group Hobs Hgroup Hin. inversion Hgroup; subst group.
    destruct o as [obs'|]; [|discriminate]. inversion Hobs; subst obs'.
    pose proof (step_replay _ _ _ _ _ _ _ Hstep) as [_ [_ [Howner _]]].
    rewrite (Howner _ eq_refl) in Hin.
    apply select_spec in Hin as [d [Hd Hw]]. rewrite Hc in Hd. inversion Hd; subst d.
    congruence.
Qed.

(* Releases of different instances commute: no thread waits at both, a thread
   waiting at one cannot also be unknown for the other, and neither release
   changes the values the other group supplies. *)
Theorem release_release_diamond : forall input i j st e st1 f st2,
  i <> j ->
  advance input (Release i) st = Some (e, st1) ->
  advance input (Release j) st = Some (f, st2) ->
  exists last,
    advance input (Release j) st1 = Some (f, last) /\
    advance input (Release i) st2 = Some (e, last) /\
    (forall g g', e = Some (Sync i g) -> f = Some (Sync j g') ->
      forall t, In t g -> In t g' -> False).
Proof.
  intros input i j [m codes] e st1 f st2 Hneq Hfirst Hsecond.
  apply release_view in Hfirst as [Harrived [Hunknown [-> ->]]].
  apply release_view in Hsecond as [Harrived' [Hunknown' [-> ->]]].
  cbn [threads memory] in *.
  assert (Hkeep : forall x y vx, x <> y -> unknown y codes = [] ->
    forall tid c, nth_error codes tid = Some c ->
    waits_at y (release_one x vx tid c) = waits_at y c /\
    may_reach y (release_one x vx tid c) = may_reach y c /\
    supply y tid (release_one x vx tid c) = supply y tid c).
  { intros x y vx Hxy Hunk tid c Hc.
    destruct (waits_at x c) eqn:Hx.
    - apply waits_at_true in Hx as [value [fn Hat]].
      assert (Hy : waits_at y c = false).
      { unfold waits_at. rewrite Hat. apply instance_eqb_false. congruence. }
      assert (Hfar : may_reach y c = false) by (eapply enabled_release_excludes; eauto).
      assert (Hfar' : may_reach y (release_one x vx tid c) = false).
      { destruct (may_reach y (release_one x vx tid c)) eqn:Hr; [|reflexivity].
        rewrite (release_one_may_reach _ _ _ _ _ Hr) in Hfar. discriminate. }
      assert (Hy' : waits_at y (release_one x vx tid c) = false).
      { rewrite (release_one_waiting _ _ _ _ _ _ Hat). unfold waits_at.
        now rewrite (resume_not_waiting _ _ _ Hat). }
      rewrite Hy, Hfar, Hfar', Hy'. split; [reflexivity|]. split; [reflexivity|].
      now rewrite (supply_other _ _ _ Hy), (supply_other _ _ _ Hy').
    - rewrite (release_one_other _ _ _ _ Hx). split; [reflexivity|split; reflexivity]. }
  assert (Hsame : forall x y, x <> y -> unknown y codes = [] ->
    arrived y (release x codes) = arrived y codes /\
    unknown y (release x codes) = unknown y codes /\
    supplied y (release x codes) = supplied y codes).
  { intros x y Hxy Hunk. split; [|split].
    - apply select_release. intros tid c Hc.
      exact (proj1 (Hkeep x y _ Hxy Hunk tid c Hc)).
    - apply select_release. intros tid c Hc.
      destruct (Hkeep x y (supplied x codes) Hxy Hunk tid c Hc) as [Hw [Hr _]].
      now rewrite Hw, Hr.
    - apply supplied_release. intros tid c Hc.
      exact (proj2 (proj2 (Hkeep x y _ Hxy Hunk tid c Hc))). }
  destruct (Hsame i j Hneq Hunknown') as [Ha1 [Hu1 Hs1]].
  destruct (Hsame j i (not_eq_sym Hneq) Hunknown) as [Ha2 [Hu2 Hs2]].
  assert (Hcodes : release i (release j codes) = release j (release i codes)).
  { apply nth_error_ext. intros tid. rewrite !release_nth, Hs1, Hs2.
    destruct (nth_error codes tid) as [c|]; cbn; [|reflexivity].
    f_equal. symmetry. apply release_one_commute. exact Hneq. }
  exists (State m (release j (release i codes))). split; [|split].
  - rewrite (release_build input j (State m (release i codes)));
      cbn [threads memory]; [|congruence|congruence].
    now rewrite Ha1.
  - rewrite (release_build input i (State m (release j codes)));
      cbn [threads memory]; [|congruence|congruence].
    now rewrite Ha2, Hcodes.
  - intros g g' Hg Hg' t Hin Hin'. inversion Hg; inversion Hg'; subst g g'.
    apply select_spec in Hin as [c [Hc Hw]]. apply select_spec in Hin' as [c' [Hc' Hw']].
    rewrite Hc in Hc'. inversion Hc'; subst c'.
    apply waits_at_true in Hw as [v1 [f1 Hk]]. apply waits_at_true in Hw' as [v2 [f2 Hk']].
    rewrite Hk in Hk'. inversion Hk'. congruence.
Qed.

Definition enabled input a s := exists e s', advance input a s = Some (e, s').

Lemma thread_enabled_after_thread : forall input t u s e s',
  t <> u -> advance input (Thread t) s = Some (e, s') ->
  enabled input (Thread u) s -> enabled input (Thread u) s'.
Proof.
  intros input t u [m codes] e s' Hneq Hstep [f [other Hother]].
  apply thread_view in Hstep as [c [o [m1 [c' [Hc [Hthread [-> ->]]]]]]].
  apply thread_view in Hother as [d [o' [m2 [d' [Hd [Hthread' _]]]]]].
  cbn [threads memory] in *.
  destruct (step_enabled_memory _ _ _ _ _ _ _ m1 Hthread') as [ev [mem [next Hnext]]].
  do 2 eexists. apply (thread_build input u (State m1 (replace_thread t c' codes)) d); cbn.
  - now rewrite replace_thread_other by congruence.
  - exact Hnext.
Qed.

Lemma enabled_after_distinct : forall input a b s e s',
  a <> b -> enabled input a s -> advance input b s = Some (e, s') ->
  enabled input a s'.
Proof.
  intros input [t|x] [u|y] s e s' Hneq Ha Hb.
  - eapply thread_enabled_after_thread with (t := u); eauto; congruence.
  - destruct Ha as [f [st Ht]].
    destruct (thread_release_diamond _ _ _ _ _ _ _ _ Hb Ht) as [last [H _]].
    exists f, last; exact H.
  - destruct Ha as [f [sr Hr]].
    destruct (thread_release_diamond _ _ _ _ _ _ _ _ Hr Hb) as [last [_ [H _]]].
    exists f, last; exact H.
  - destruct Ha as [f [sr Hr]].
    assert (Hyx : y <> x) by congruence.
    destruct (release_release_diamond _ _ _ _ _ _ _ _ Hyx Hb Hr) as [last [H _]].
    exists f, last; exact H.
Qed.

Lemma finished_not_enabled : forall input s a, finished s -> ~ enabled input a s.
Proof.
  intros input [m codes] [tid|x] Hdone [e [s' Hstep]];
    unfold finished in Hdone; cbn in Hdone; rewrite Forall_forall in Hdone.
  - apply thread_view in Hstep as [c [o [m' [c' [Hc [Hthread _]]]]]].
    cbn in Hc. apply nth_error_In in Hc.
    destruct (Hdone _ Hc) as [-> | ->]; discriminate.
  - apply release_view in Hstep as [Harrived _]. apply Harrived. cbn.
    apply select_nil. intros tid c Hc. apply nth_error_In in Hc.
    now destruct (Hdone _ Hc) as [-> | ->].
Qed.

Lemma thread_event_owner : forall input tid s e s',
  advance input (Thread tid) s = Some (e, s') ->
  e = None \/ exists o, e = Some (Memory o) /\ av_owner (access o) = tid.
Proof.
  intros input tid s e s' H.
  apply thread_view in H as [c [o [m' [c' [_ [Hstep [-> _]]]]]]].
  pose proof (step_replay _ _ _ _ _ _ _ Hstep) as [_ [_ [Howner _]]].
  destruct o as [o|]; [right; exists o; split; [reflexivity|now apply Howner]|left; reflexivity].
Qed.

Theorem thread_steps_swap : forall input t u s e s1 f s2,
  t <> u ->
  advance input (Thread t) s = Some (e, s1) ->
  advance input (Thread u) s1 = Some (f, s2) ->
  (forall x y, e = Some (Memory x) -> f = Some (Memory y) ->
    ~ Conflict (access x) (access y)) ->
  exists s1' s2',
    advance input (Thread u) s = Some (f, s1') /\
    advance input (Thread t) s1' = Some (e, s2') /\ state_equiv input s2 s2'.
Proof.
  intros input t u [m codes] e s1 f s2 Hneq Hfirst Hsecond Hsafe.
  apply thread_view in Hfirst as [c [o [m1 [c' [Hc [Hstep [-> ->]]]]]]].
  apply thread_view in Hsecond as [d [o' [m2 [d' [Hd [Hstep' [-> ->]]]]]]].
  cbn [threads memory] in *.
  rewrite replace_thread_other in Hd by congruence.
  destruct (steps_swap input t u m c d o m1 c' o' m2 d')
    as [n1 [n2 [Hu [Ht Hmem]]]]; try assumption.
  { intros x y Hx Hy. apply Hsafe; now rewrite ?Hx, ?Hy. }
  exists (State n1 (replace_thread u d' codes)),
    (State n2 (replace_thread t c' (replace_thread u d' codes))).
  split; [apply (thread_build input u (State m codes) d); assumption|].
  split.
  - apply (thread_build input t (State n1 (replace_thread u d' codes)) c); cbn; [|exact Ht].
    now rewrite replace_thread_other by congruence.
  - split; cbn [threads memory].
    + apply replace_threads_commute. exact Hneq.
    + intros address. symmetry. apply Hmem.
Qed.

Theorem steps_swap_actions : forall input a b s e s1 f s2 trace,
  a <> b -> advance input a s = Some (e, s1) ->
  advance input b s1 = Some (f, s2) -> enabled input b s ->
  MemDRF (emit_event e (emit_event f trace)) ->
  exists s1' s2',
    advance input b s = Some (f, s1') /\
    advance input a s1' = Some (e, s2') /\ state_equiv input s2 s2' /\
    reorders (emit_event e (emit_event f trace)) (emit_event f (emit_event e trace)).
Proof.
  intros input [t|x] [u|y] s e s1 f s2 trace Hneq Ha Hb Henabled Hdrf.
  - assert (Htu : t <> u) by congruence.
    destruct (thread_steps_swap input t u s e s1 f s2) as [s1' [s2' [Hu [Ht Heq]]]];
      try assumption.
    { intros x y -> -> Hconflict.
      exact (adjacent_conflict_not_drf (Memory x :: Memory y :: trace) 0 x y
        eq_refl eq_refl Hconflict Hdrf). }
    exists s1', s2'. split; [exact Hu|]. split; [exact Ht|]. split; [exact Heq|].
    destruct (thread_event_owner _ _ _ _ _ Ha) as [->|[x [-> Hx]]],
      (thread_event_owner _ _ _ _ _ Hb) as [->|[y [-> Hy]]];
      try apply reorders_refl.
    apply (reorders_swap [] _ _ trace). split.
    + intros w Hw Hw'. cbn in Hw, Hw'. congruence.
    + intros Hconflict.
      exact (adjacent_conflict_not_drf (Memory x :: Memory y :: trace) 0 x y
        eq_refl eq_refl Hconflict Hdrf).
  - destruct Henabled as [sync [sr Hsync]].
    destruct (thread_release_diamond _ _ _ _ _ _ _ _ Hsync Ha)
      as [last [Ht [Hr Houtside]]].
    rewrite Hb in Hr. inversion Hr; subst sync last.
    exists sr, s2. split; [exact Hsync|]. split; [exact Ht|].
    split; [apply state_equiv_refl|].
    apply release_view in Hsync as [_ [_ [-> _]]].
    destruct (thread_event_owner _ _ _ _ _ Ha) as [->|[o [-> Ho]]]; [constructor|].
    apply (reorders_swap [] _ _ trace). split; [|exact I].
    intros w Hw [_ Hw']. cbn in Hw. subst w.
    exact (Houtside o _ eq_refl eq_refl Hw').
  - destruct Henabled as [ev [st Hthread]].
    destruct (thread_release_diamond _ _ _ _ _ _ _ _ Ha Hthread)
      as [last [Ht [Hr Houtside]]].
    rewrite Hb in Ht. inversion Ht; subst ev last.
    exists st, s2. split; [exact Hthread|]. split; [exact Hr|].
    split; [apply state_equiv_refl|].
    apply release_view in Ha as [_ [_ [-> _]]].
    destruct (thread_event_owner _ _ _ _ _ Hthread) as [->|[o [-> Ho]]]; [constructor|].
    apply (reorders_swap [] _ _ trace). split; [|exact I].
    intros w [_ Hw] Hw'. cbn in Hw'. subst w.
    exact (Houtside o _ eq_refl eq_refl Hw).
  - assert (Hxy : x <> y) by congruence.
    destruct Henabled as [g [sy Hy]].
    destruct (release_release_diamond _ _ _ _ _ _ _ _ Hxy Ha Hy)
      as [last [H1 [H2 Hdisjoint]]].
    rewrite Hb in H1. inversion H1; subst g last.
    exists sy, s2. split; [exact Hy|]. split; [exact H2|].
    split; [apply state_equiv_refl|].
    apply release_view in Ha as [_ [_ [-> _]]].
    apply release_view in Hy as [_ [_ [-> _]]].
    apply (reorders_swap [] _ _ trace). split; [|exact Hxy].
    intros w [_ Hw] [_ Hw']. exact (Hdisjoint _ _ eq_refl eq_refl w Hw Hw').
Qed.
