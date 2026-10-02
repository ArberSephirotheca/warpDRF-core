From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Faial.Core Require Import AVal.
From Faial.Warp Require Import Store Model.

Import ListNotations.

(* A memory event belongs to its owner. A collective that orders memory
   belongs to each participant; one that does not belongs to no thread, so it
   adds no ordering between threads. *)
Definition involves (e : event) (t : nat) : Prop :=
  match e with
  | Memory o => av_owner (access o) = t
  | Sync i group => site_sync (fst i) = true /\ In t group
  end.

(* The paper's happens-before is the transitive closure of each thread's
   program order, in which a collective that orders memory belongs to every
   participant. One step
   relates two events that share a thread. With several collectives, the
   closure matters: a relay thread can order two threads that never meet. *)
Definition hb_step (trace : list event) (i j : nat) : Prop :=
  i < j /\ exists e f t,
    nth_error trace i = Some e /\ nth_error trace j = Some f /\
    involves e t /\ involves f t.

Definition hb trace := clos_trans nat (hb_step trace).

Definition MemDRF (trace : list event) :=
  forall i j e f,
  nth_error trace i = Some (Memory e) ->
  nth_error trace j = Some (Memory f) ->
  Conflict (access e) (access f) ->
  hb trace i j \/ hb trace j i.

Lemma hb_lt : forall trace i j, hb trace i j -> i < j.
Proof.
  intros trace i j H. induction H as [i j [Hlt _]|i k j _ IH1 _ IH2]; lia.
Qed.

Lemma conflict_owners : forall a b, Conflict a b -> av_owner a <> av_owner b.
Proof. intros a b H. inversion H; assumption. Qed.

Lemma adjacent_conflict_not_drf : forall trace i e f,
  nth_error trace i = Some (Memory e) ->
  nth_error trace (S i) = Some (Memory f) ->
  Conflict (access e) (access f) -> ~ MemDRF trace.
Proof.
  intros trace i e f He Hf Hconflict Hdrf.
  destruct (Hdrf i (S i) e f He Hf Hconflict) as [Hhb|Hhb].
  - apply clos_trans_t1n in Hhb.
    inversion Hhb as [y Hstep|y z Hstep Hrest]; subst.
    + destruct Hstep as [_ [x [x' [t [Hx [Hx' [Ht Ht']]]]]]].
      rewrite He in Hx. rewrite Hf in Hx'. inversion Hx; inversion Hx'; subst.
      cbn in Ht, Ht'. apply (conflict_owners _ _ Hconflict). congruence.
    + apply clos_t1n_trans, hb_lt in Hrest. destruct Hstep as [Hlt _]. lia.
  - apply hb_lt in Hhb. lia.
Qed.

(* Reordering adjacent events. *)

Fixpoint swap_index k i :=
  match k, i with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, S (S i) => S (S i)
  | S k, 0 => 0
  | S k, S i => S (swap_index k i)
  end.

Lemma swap_index_involutive : forall k i, swap_index k (swap_index k i) = i.
Proof. induction k; intros [|[|i]]; cbn; auto. Qed.

Lemma swap_index_order : forall k i j,
  i < j -> swap_index k i < swap_index k j \/ (i = k /\ j = S k).
Proof.
  induction k; intros [|i] [|j] Hlt; cbn; try lia.
  - destruct j; cbn; auto; lia.
  - destruct i, j; cbn; try lia.
  - destruct (IHk i j) as [Horder|[-> ->]]; lia.
Qed.

Lemma nth_error_swap : forall {A} (prefix : list A) e f suffix i,
  nth_error (prefix ++ f :: e :: suffix) (swap_index (length prefix) i) =
  nth_error (prefix ++ e :: f :: suffix) i.
Proof. intros A prefix. induction prefix as [|head prefix IH]; intros e f suffix [|[|i]]; cbn; auto. Qed.

(* Two events are independent when no thread takes part in both. *)
Definition independent (e f : event) : Prop :=
  forall t, involves e t -> involves f t -> False.

Definition swappable (e f : event) : Prop :=
  independent e f /\
  match e, f with
  | Memory x, Memory y => ~ Conflict (access x) (access y)
  | Sync i _, Sync i' _ => i <> i'
  | _, _ => True
  end.

Lemma hb_step_swap : forall prefix e f suffix i j,
  independent e f ->
  hb_step (prefix ++ e :: f :: suffix) i j ->
  hb_step (prefix ++ f :: e :: suffix)
    (swap_index (length prefix) i) (swap_index (length prefix) j).
Proof.
  intros prefix e f suffix i j Hind [Hlt [x [y [t [Hx [Hy [Htx Hty]]]]]]].
  destruct (swap_index_order (length prefix) i j Hlt) as [Hlt'|[-> ->]].
  - split; [exact Hlt'|]. exists x, y, t. rewrite !nth_error_swap. auto.
  - exfalso.
    rewrite nth_error_app2, Nat.sub_diag in Hx by lia.
    rewrite nth_error_app2 in Hy by lia.
    replace (S (length prefix) - length prefix) with 1 in Hy by lia.
    cbn in Hx, Hy. inversion Hx; inversion Hy; subst. exact (Hind t Htx Hty).
Qed.

Lemma hb_swap : forall prefix e f suffix i j,
  independent e f ->
  hb (prefix ++ e :: f :: suffix) i j ->
  hb (prefix ++ f :: e :: suffix)
    (swap_index (length prefix) i) (swap_index (length prefix) j).
Proof.
  intros prefix e f suffix i j Hind H.
  induction H as [i j Hstep|i k j _ IH1 _ IH2].
  - apply t_step. now apply hb_step_swap.
  - eapply t_trans; eauto.
Qed.

Lemma memory_drf_swap : forall prefix e f suffix,
  independent e f -> MemDRF (prefix ++ e :: f :: suffix) ->
  MemDRF (prefix ++ f :: e :: suffix).
Proof.
  intros prefix e f suffix Hind Hdrf i j x y Hx Hy Hconflict.
  assert (Hx' : nth_error (prefix ++ e :: f :: suffix)
    (swap_index (length prefix) i) = Some (Memory x)).
  { rewrite <- nth_error_swap, swap_index_involutive. exact Hx. }
  assert (Hy' : nth_error (prefix ++ e :: f :: suffix)
    (swap_index (length prefix) j) = Some (Memory y)).
  { rewrite <- nth_error_swap, swap_index_involutive. exact Hy. }
  destruct (Hdrf _ _ _ _ Hx' Hy' Hconflict) as [Horder|Horder].
  - left. apply (hb_swap _ _ _ _ _ _ Hind) in Horder.
    now rewrite !swap_index_involutive in Horder.
  - right. apply (hb_swap _ _ _ _ _ _ Hind) in Horder.
    now rewrite !swap_index_involutive in Horder.
Qed.

Lemma hb_tail : forall e trace i j, hb (e :: trace) (S i) (S j) -> hb trace i j.
Proof.
  intros e trace i j H.
  remember (S i) as x eqn:Hx. remember (S j) as y eqn:Hy. revert i j Hx Hy.
  induction H as [x y Hstep|x z y Hxz IH1 Hzy IH2]; intros i j -> ->.
  - apply t_step. destruct Hstep as [Hlt [a [b [t [Ha [Hb [Hta Htb]]]]]]].
    split; [lia|]. exists a, b, t. auto.
  - destruct z as [|z]; [apply hb_lt in Hxz; lia|].
    eapply t_trans; [apply (IH1 i z)|apply (IH2 z j)]; reflexivity.
Qed.

Lemma memory_drf_tail : forall e trace, MemDRF (e :: trace) -> MemDRF trace.
Proof.
  intros e trace H i j x y Hx Hy Hconflict.
  destruct (H (S i) (S j) x y Hx Hy Hconflict) as [Horder|Horder];
    [left|right]; eapply hb_tail; exact Horder.
Qed.

Lemma memory_drf_emit_tail : forall e trace,
  MemDRF (emit_event e trace) -> MemDRF trace.
Proof. intros [e|] trace H; [eapply memory_drf_tail|]; eauto. Qed.

(* Happens-before between two events of a prefix runs through the prefix, so a
   race in a prefix stays a race in every extension. *)
Lemma hb_app_l : forall left right i j,
  hb (left ++ right) i j -> j < length left -> hb left i j.
Proof.
  intros left right i j H.
  induction H as [i j [Hlt [e [f [t [He [Hf [Hte Htf]]]]]]]|i k j Hik IH1 Hkj IH2];
    intros Hj.
  - apply t_step. split; [exact Hlt|]. exists e, f, t.
    rewrite !nth_error_app1 in * by lia. auto.
  - pose proof (hb_lt _ _ _ Hkj) as Hlt.
    apply t_trans with k; [apply IH1; lia|exact (IH2 Hj)].
Qed.

Lemma memory_drf_app_l : forall left right, MemDRF (left ++ right) -> MemDRF left.
Proof.
  intros left right Hdrf i j e f He Hf Hconflict.
  assert (Hi : i < length left)
    by (apply (proj1 (nth_error_Some left i)); rewrite He; discriminate).
  assert (Hj : j < length left)
    by (apply (proj1 (nth_error_Some left j)); rewrite Hf; discriminate).
  destruct (Hdrf i j e f) as [Hhb|Hhb].
  - rewrite nth_error_app1 by exact Hi. exact He.
  - rewrite nth_error_app1 by exact Hj. exact Hf.
  - exact Hconflict.
  - left. exact (hb_app_l _ _ _ _ Hhb Hj).
  - right. exact (hb_app_l _ _ _ _ Hhb Hi).
Qed.

(* What an execution reveals: each thread's reads and each instance's groups. *)

Fixpoint memory_events (trace : list event) : list observation :=
  match trace with
  | [] => []
  | Memory o :: rest => o :: memory_events rest
  | Sync _ _ :: rest => memory_events rest
  end.

Definition read_history tid trace :=
  filter (fun o => Nat.eqb (av_owner (access o)) tid &&
    match av_mode (access o) with m_read => true | m_write => false end)
    (memory_events trace).

Fixpoint groups_at (i : instance) (trace : list event) : list (list nat) :=
  match trace with
  | [] => []
  | Memory _ :: rest => groups_at i rest
  | Sync i' group :: rest =>
      if instance_eqb i i' then group :: groups_at i rest else groups_at i rest
  end.

Lemma memory_events_app : forall prefix suffix,
  memory_events (prefix ++ suffix) = memory_events prefix ++ memory_events suffix.
Proof. induction prefix as [|[o|i g] prefix IH]; intros suffix; cbn; congruence. Qed.

Lemma groups_at_app : forall i prefix suffix,
  groups_at i (prefix ++ suffix) = groups_at i prefix ++ groups_at i suffix.
Proof.
  intros i. induction prefix as [|[o|i' g] prefix IH]; intros suffix; cbn; auto.
  destruct (instance_eqb i i'); cbn; now rewrite IH.
Qed.

Lemma read_history_app : forall tid prefix suffix,
  read_history tid (prefix ++ suffix) = read_history tid prefix ++ read_history tid suffix.
Proof. intros; unfold read_history; now rewrite memory_events_app, filter_app. Qed.

Lemma read_history_swap : forall prefix e f suffix,
  swappable e f -> forall tid,
  read_history tid (prefix ++ e :: f :: suffix) =
  read_history tid (prefix ++ f :: e :: suffix).
Proof.
  intros prefix [x|i g] [y|i' h] suffix [Hind _] tid;
    rewrite !read_history_app; f_equal; unfold read_history; cbn; try reflexivity.
  destruct (Nat.eqb (av_owner (access x)) tid) eqn:Hx,
    (Nat.eqb (av_owner (access y)) tid) eqn:Hy; cbn; try reflexivity.
  exfalso. apply Nat.eqb_eq in Hx, Hy.
  apply (Hind tid); cbn; assumption.
Qed.

Lemma groups_at_swap : forall prefix e f suffix,
  swappable e f -> forall i,
  groups_at i (prefix ++ e :: f :: suffix) = groups_at i (prefix ++ f :: e :: suffix).
Proof.
  intros prefix [x|i1 g] [y|i2 h] suffix [_ Hsites] i;
    rewrite !groups_at_app; f_equal; cbn; try reflexivity.
  destruct (instance_eqb i i1) eqn:H1, (instance_eqb i i2) eqn:H2; try reflexivity.
  apply instance_eqb_true in H1, H2. exfalso. apply Hsites. congruence.
Qed.

Inductive reorders : list event -> list event -> Prop :=
| reorders_refl : forall trace, reorders trace trace
| reorders_swap : forall prefix e f suffix,
    swappable e f -> reorders (prefix ++ e :: f :: suffix) (prefix ++ f :: e :: suffix)
| reorders_trans : forall a b c, reorders a b -> reorders b c -> reorders a c.

Lemma reorders_prefix : forall left right,
  reorders left right -> forall prefix, reorders (prefix ++ left) (prefix ++ right).
Proof.
  intros left right H. induction H; intros outer.
  - constructor.
  - rewrite !app_assoc. constructor; assumption.
  - eapply reorders_trans; eauto.
Qed.

Lemma reorders_emit : forall e left right,
  reorders left right -> reorders (emit_event e left) (emit_event e right).
Proof. intros [e|] left right H; [apply (reorders_prefix _ _ H [e])|assumption]. Qed.

Lemma reorders_memory_drf : forall left right,
  reorders left right -> MemDRF left -> MemDRF right.
Proof.
  intros left right H. induction H as [|prefix e f suffix [Hind _]|]; eauto.
  now apply memory_drf_swap.
Qed.

Lemma reorders_read_history : forall left right,
  reorders left right -> forall tid, read_history tid left = read_history tid right.
Proof.
  intros left right H. induction H; intros tid; auto using read_history_swap.
  now rewrite IHreorders1, IHreorders2.
Qed.

Lemma reorders_groups_at : forall left right,
  reorders left right -> forall i, groups_at i left = groups_at i right.
Proof.
  intros left right H. induction H; intros i; auto using groups_at_swap.
  now rewrite IHreorders1, IHreorders2.
Qed.

Lemma reorders_in : forall left right,
  reorders left right -> forall e, In e left <-> In e right.
Proof.
  intros left right H. induction H as [|prefix e f suffix _|a b c _ IH1 _ IH2];
    intros x; [tauto| |now rewrite IH1, IH2].
  rewrite !in_app_iff. cbn. tauto.
Qed.
