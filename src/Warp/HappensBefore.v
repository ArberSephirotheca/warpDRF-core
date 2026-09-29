From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Faial.Core Require Import AVal.
From Faial.Warp Require Import Semantics Participation Contract Commutation Agreement.
From Faial.Warp Require Reference.

Import ListNotations.

(* The paper orders memory with a transitive happens-before: each thread's
   program order, in which a collective belongs to every participant. MemDRF
   instead asks for one collective between a conflicting pair. The two agree on
   every trace of this model, because a trace contains at most one collective. *)
Definition owner_at (trace : list event) i t :=
  exists e, nth_error trace i = Some (Memory e) /\ av_owner (access e) = t.

Inductive hb_step (trace : list event) : nat -> nat -> Prop :=
| hb_program : forall i j t,
    i < j -> owner_at trace i t -> owner_at trace j t -> hb_step trace i j
| hb_arrive : forall i k t group,
    i < k -> owner_at trace i t -> nth_error trace k = Some (Synchronize group) ->
    In t group -> hb_step trace i k
| hb_leave : forall k j t group,
    k < j -> nth_error trace k = Some (Synchronize group) -> owner_at trace j t ->
    In t group -> hb_step trace k j
| hb_collectives : forall k l t group group',
    k < l -> nth_error trace k = Some (Synchronize group) ->
    nth_error trace l = Some (Synchronize group') ->
    In t group -> In t group' -> hb_step trace k l.

Definition hb trace := clos_trans nat (hb_step trace).

Definition HbDRF (trace : list event) :=
  forall i j e f,
  nth_error trace i = Some (Memory e) ->
  nth_error trace j = Some (Memory f) ->
  Conflict (access e) (access f) -> hb trace i j \/ hb trace j i.

Definition at_most_one_collective (trace : list event) :=
  forall k l group group',
  nth_error trace k = Some (Synchronize group) ->
  nth_error trace l = Some (Synchronize group') -> k = l.

Lemma owner_at_unique : forall trace i t u,
  owner_at trace i t -> owner_at trace i u -> t = u.
Proof.
  intros trace i t u [e [He <-]] [f [Hf <-]].
  rewrite He in Hf. now inversion Hf.
Qed.

Lemma owner_at_not_collective : forall trace i t group,
  owner_at trace i t -> nth_error trace i <> Some (Synchronize group).
Proof. intros trace i t group [e [He _]]. rewrite He. discriminate. Qed.

(* Leaving an access of t, a path stays within t's accesses until it reaches a
   collective in which t participates. *)
Lemma hb_from_access : forall trace i j t,
  hb trace i j -> owner_at trace i t ->
  owner_at trace j t \/
  exists k group, nth_error trace k = Some (Synchronize group) /\ In t group /\
    i < k /\ (k = j \/ hb trace k j).
Proof.
  intros trace i j t Hhb. apply clos_trans_t1n in Hhb.
  induction Hhb as [i j Hstep|i m j Hstep Hrest IH]; intros Hi.
  - destruct Hstep as [a b u Hlt Hu Hb|a k u group Hlt Hu Hk Hin|
      k b u group _ Hk _ _|k l u group group' _ Hk _ _ _].
    + left. now rewrite (owner_at_unique _ _ _ _ Hi Hu).
    + right. exists k, group. rewrite (owner_at_unique _ _ _ _ Hi Hu).
      repeat split; auto.
    + exfalso. eapply owner_at_not_collective; eauto.
    + exfalso. eapply owner_at_not_collective; eauto.
  - destruct Hstep as [a b u Hlt Hu Hb|a k u group Hlt Hu Hk Hin|
      k b u group _ Hk _ _|k l u group group' _ Hk _ _ _].
    + rewrite <- (owner_at_unique _ _ _ _ Hi Hu) in Hb.
      destruct (IH Hb) as [Hj|[k [group [Hk [Hin [Hbk Hkj]]]]]]; [now left|].
      right. exists k, group. repeat split; auto; lia.
    + right. exists k, group. rewrite (owner_at_unique _ _ _ _ Hi Hu).
      repeat split; auto. right. now apply clos_t1n_trans.
    + exfalso. eapply owner_at_not_collective; eauto.
    + exfalso. eapply owner_at_not_collective; eauto.
Qed.

(* Arriving at an access of u, a path comes from u's own accesses or from a
   collective in which u participates. *)
Lemma hb_to_access : forall trace i j u,
  hb trace i j -> owner_at trace j u ->
  owner_at trace i u \/
  exists k group, nth_error trace k = Some (Synchronize group) /\ In u group /\
    k < j /\ (k = i \/ hb trace i k).
Proof.
  intros trace i j u Hhb. apply clos_trans_tn1 in Hhb.
  induction Hhb as [j Hstep|m j Hstep Hrest IH]; intros Hj.
  - destruct Hstep as [a b t Hlt Ha Ht|a k t group _ _ Hk _|
      k b t group Hlt Hk Ht Hin|k l t group group' _ _ Hl _ _].
    + left. now rewrite (owner_at_unique _ _ _ _ Hj Ht).
    + exfalso. eapply owner_at_not_collective; eauto.
    + right. exists k, group. rewrite (owner_at_unique _ _ _ _ Hj Ht).
      repeat split; auto.
    + exfalso. eapply owner_at_not_collective; eauto.
  - destruct Hstep as [a b t Hlt Ha Ht|a k t group _ _ Hk _|
      k b t group Hlt Hk Ht Hin|k l t group group' _ _ Hl _ _].
    + rewrite <- (owner_at_unique _ _ _ _ Hj Ht) in Ha.
      destruct (IH Ha) as [Hi|[k [group [Hk [Hin [Hka Hik]]]]]]; [now left|].
      right. exists k, group. repeat split; auto; lia.
    + exfalso. eapply owner_at_not_collective; eauto.
    + right. exists k, group. rewrite (owner_at_unique _ _ _ _ Hj Ht).
      repeat split; auto. right. now apply clos_tn1_trans.
    + exfalso. eapply owner_at_not_collective; eauto.
Qed.

(* With one collective, the first and last collectives on a path coincide. *)
Lemma hb_collective_orders : forall trace i j t u,
  at_most_one_collective trace -> hb trace i j ->
  owner_at trace i t -> owner_at trace j u -> t <> u ->
  collective_orders trace i j t u.
Proof.
  intros trace i j t u Hone Hhb Hi Hj Hneq.
  destruct (hb_from_access _ _ _ _ Hhb Hi) as [Hsame|[k [group [Hk [Ht [Hik Hkj]]]]]].
  { exfalso. apply Hneq. eapply owner_at_unique; eauto. }
  destruct Hkj as [->|Hkj].
  { exfalso. eapply owner_at_not_collective; eauto. }
  destruct (hb_to_access _ _ _ _ Hkj Hj) as [Hbad|[l [group' [Hl [Hu [Hlj _]]]]]].
  { exfalso. eapply owner_at_not_collective; eauto. }
  assert (l = k) by (eapply Hone; eauto). subst l.
  rewrite Hk in Hl. injection Hl as Hgroup. subst group'.
  exists k, group. repeat split; assumption.
Qed.

Lemma memory_drf_hb : forall trace, MemDRF trace -> HbDRF trace.
Proof.
  intros trace Hdrf i j e f He Hf Hconflict.
  destruct (Hdrf _ _ _ _ He Hf Hconflict)
    as [[k [group [Hk [Hik [Hkj [Hine Hinf]]]]]]|[k [group [Hk [Hjk [Hki [Hinf Hine]]]]]]];
    [left|right]; apply t_trans with (y := k); apply t_step.
  - apply hb_arrive with (t := av_owner (access e)) (group := group); auto.
    exists e; auto.
  - apply hb_leave with (t := av_owner (access f)) (group := group); auto.
    exists f; auto.
  - apply hb_arrive with (t := av_owner (access f)) (group := group); auto.
    exists f; auto.
  - apply hb_leave with (t := av_owner (access e)) (group := group); auto.
    exists e; auto.
Qed.

Lemma hb_memory_drf : forall trace,
  at_most_one_collective trace -> HbDRF trace -> MemDRF trace.
Proof.
  intros trace Hone Hdrf i j e f He Hf Hconflict.
  assert (Hneq : av_owner (access e) <> av_owner (access f))
    by (destruct Hconflict; assumption).
  assert (Hi : owner_at trace i (av_owner (access e))) by (exists e; auto).
  assert (Hj : owner_at trace j (av_owner (access f))) by (exists f; auto).
  destruct (Hdrf _ _ _ _ He Hf Hconflict) as [Hhb|Hhb]; [left|right];
    apply hb_collective_orders; auto; congruence.
Qed.

Lemma collective_advance_group : forall p input s e s',
  advance p input Collective s = Some (e, s') ->
  participants s = None /\
  exists group, e = Some (Synchronize group) /\ participants s' = Some group.
Proof.
  intros p input s e s' Hstep. unfold advance in Hstep.
  destruct (participants s); try discriminate.
  destruct (entered_threads (decisions s)) as [|t rest]; try discriminate.
  destruct (match p with SSO => all_decided (decisions s) | Spec => true end);
    try discriminate.
  destruct (release_collective (decisions s) (threads (machine s))); try discriminate.
  inversion Hstep; subst. split; [reflexivity|]. eexists; split; reflexivity.
Qed.

(* A collective records its participants, and a later collective requires none. *)
Lemma execution_one_collective : forall p input s trace last,
  execution p input s trace last ->
  at_most_one_collective trace /\
  (participants s <> None -> forall k group, nth_error trace k <> Some (Synchronize group)).
Proof.
  intros p input s trace last Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec [Hone Hnone]].
  - split; [intros [|k] ? ? ? Hk; discriminate|intros _ [|k] ?; discriminate].
  - destruct a as [tid|].
    + apply thread_advance_view in Hstep
        as [code [o [m' [code' [ds' [_ [_ [_ [-> ->]]]]]]]]].
      cbn [participants] in Hnone.
      destruct o as [o|]; cbn [option_map emit_event]; [|split; assumption].
      split.
      * intros [|k] [|l] group group' Hk Hl; cbn in Hk, Hl; try discriminate.
        f_equal. eapply Hone; eauto.
      * intros Hsome [|k] group; cbn; [discriminate|]. now apply Hnone.
    + destruct (collective_advance_group _ _ _ _ _ Hstep) as [Hs [group [-> Hs']]].
      assert (Hempty : forall k g, nth_error trace k <> Some (Synchronize g)).
      { apply Hnone. rewrite Hs'. discriminate. }
      split; [|intros Hsome; contradiction].
      intros [|k] [|l] g g' Hk Hl; cbn in Hk, Hl; try reflexivity;
        exfalso; eapply Hempty; eauto.
Qed.

Corollary memory_drf_iff_hb : forall p input s trace last,
  execution p input s trace last -> (MemDRF trace <-> HbDRF trace).
Proof.
  intros p input s trace last Hexec. split; [apply memory_drf_hb|].
  apply hb_memory_drf. exact (proj1 (execution_one_collective _ _ _ _ _ Hexec)).
Qed.

(* The agreement theorem, with memory DRF stated over the transitive order. *)
Theorem sso_agreement_hb : forall programs input reference_trace reference_last,
  Reference.run input programs = Some (reference_trace, reference_last) ->
  HbDRF reference_trace ->
  forall trace last,
  execution SSO input (initial programs) trace last -> finished last ->
  same_observations input reference_trace reference_last trace last /\ HbDRF trace.
Proof.
  intros programs input reference_trace reference_last Hrun Hhb trace last Htarget Hdone.
  pose proof Hrun as Hsound.
  apply Reference.run_sound in Hsound as [_ [Hreference _]].
  assert (Hdrf : MemDRF reference_trace)
    by (apply (proj2 (memory_drf_iff_hb _ _ _ _ _ Hreference)); exact Hhb).
  split; [eapply sso_agreement_from_drf; eauto|].
  apply memory_drf_hb. eapply sso_memory_drf; eauto.
Qed.

(* Repeated collectives are outside this model. Across two of them, ordering can
   pass through a third thread, which only the transitive definition accepts. *)
Definition chained_trace :=
  [Memory (Observe (av_write 0 0) 1); Synchronize [0; 1];
   Synchronize [1; 2]; Memory (Observe (av_read 2 0) 1)].

Example chained_collectives : HbDRF chained_trace /\ ~ MemDRF chained_trace.
Proof.
  split.
  - intros i j e f He Hf Hconflict.
    assert (Hhb : hb chained_trace 0 3).
    { apply t_trans with (y := 1); [apply t_step|apply t_trans with (y := 2); apply t_step].
      - apply hb_arrive with (t := 0) (group := [0; 1]); cbn; auto.
        exists (Observe (av_write 0 0) 1); auto.
      - apply hb_collectives with (t := 1) (group := [0; 1]) (group' := [1; 2]); cbn; auto.
      - apply hb_leave with (t := 2) (group := [1; 2]); cbn; auto.
        exists (Observe (av_read 2 0) 1); auto. }
    assert (Hi : i < 4).
    { apply (proj1 (nth_error_Some chained_trace i)). rewrite He. discriminate. }
    assert (Hj : j < 4).
    { apply (proj1 (nth_error_Some chained_trace j)). rewrite Hf. discriminate. }
    destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
      cbn in He, Hf; try discriminate;
      inversion He; inversion Hf; subst; clear He Hf;
      try solve [inversion Hconflict; cbn in *; congruence]; auto.
  - intros Hdrf.
    assert (Hconflict : Conflict (av_write 0 0) (av_read 2 0))
      by (apply conflict_l; cbn; congruence).
    destruct (Hdrf 0 3 (Observe (av_write 0 0) 1) (Observe (av_read 2 0) 1)
      eq_refl eq_refl Hconflict) as [[k [group [Hk [Hlo [Hhi [Ht Hu]]]]]]|Horder].
    + destruct k as [|[|[|k]]]; try lia; cbn in Hk; inversion Hk; subst;
        cbn in Ht, Hu; intuition congruence.
    + apply collective_orders_forward in Horder. lia.
Qed.
