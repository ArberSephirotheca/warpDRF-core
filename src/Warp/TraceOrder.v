From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import AVal.
From Faial.Warp Require Import Semantics Participation Contract.

Import ListNotations.

(* Only independent events commute: conflicting accesses keep their order. *)
Definition swappable (e f : event) : Prop :=
  match e, f with
  | Memory x, Memory y =>
      av_owner (access x) <> av_owner (access y) /\ ~ Conflict (access x) (access y)
  | Memory x, Synchronize group | Synchronize group, Memory x =>
      ~ In (av_owner (access x)) group
  | Synchronize _, Synchronize _ => False
  end.

Fixpoint swap_index k i :=
  match k, i with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, S (S i) => S (S i)
  | S k, 0 => 0
  | S k, S i => S (swap_index k i)
  end.

Lemma swap_index_involutive : forall k i, swap_index k (swap_index k i) = i.
Proof.
  induction k; intros [|[|i]]; cbn; auto.
Qed.

Lemma swap_index_order : forall k i j,
  i < j -> swap_index k i < swap_index k j \/ (i = k /\ j = S k).
Proof.
  induction k; intros [|i] [|j] Hlt; cbn; try lia.
  - destruct j; cbn; auto; lia.
  - destruct i, j; cbn; try lia.
  - destruct (IHk i j) as [Horder|[-> ->]]; lia.
Qed.

Lemma nth_error_swap : forall (prefix : list event) e f suffix i,
  nth_error (prefix ++ f :: e :: suffix) (swap_index (length prefix) i) =
  nth_error (prefix ++ e :: f :: suffix) i.
Proof.
  induction prefix as [|head prefix IH]; intros e f suffix [|[|i]]; cbn; auto.
Qed.

Lemma collective_orders_swap : forall prefix e f suffix i j x y,
  swappable e f ->
  nth_error (prefix ++ e :: f :: suffix) i = Some (Memory x) ->
  nth_error (prefix ++ e :: f :: suffix) j = Some (Memory y) ->
  collective_orders (prefix ++ e :: f :: suffix) i j
    (av_owner (access x)) (av_owner (access y)) ->
  collective_orders (prefix ++ f :: e :: suffix)
    (swap_index (length prefix) i) (swap_index (length prefix) j)
    (av_owner (access x)) (av_owner (access y)).
Proof.
  intros prefix e f suffix i j x y Hswap Hx Hy
    [k [group [Hk [Hik [Hkj [Hin Hjn]]]]]].
  exists (swap_index (length prefix) k), group.
  split; [now rewrite nth_error_swap|].
  assert (Hi : swap_index (length prefix) i < swap_index (length prefix) k).
  { destruct (swap_index_order (length prefix) _ _ Hik) as [Hlt|[-> ->]]; auto.
    rewrite nth_error_app2, Nat.sub_diag in Hx by lia.
    rewrite nth_error_app2 in Hk by lia.
    replace (S (length prefix) - length prefix) with 1 in Hk by lia.
    cbn in Hx, Hk. inversion Hx; inversion Hk; subst.
    exfalso. exact (Hswap Hin). }
  assert (Hj : swap_index (length prefix) k < swap_index (length prefix) j).
  { destruct (swap_index_order (length prefix) _ _ Hkj) as [Hlt|[-> ->]]; auto.
    rewrite nth_error_app2, Nat.sub_diag in Hk by lia.
    rewrite nth_error_app2 in Hy by lia.
    replace (S (length prefix) - length prefix) with 1 in Hy by lia.
    cbn in Hy, Hk. inversion Hy; inversion Hk; subst.
    exfalso. exact (Hswap Hjn). }
  auto.
Qed.

Lemma memory_drf_swap : forall prefix e f suffix,
  swappable e f -> MemDRF (prefix ++ e :: f :: suffix) ->
  MemDRF (prefix ++ f :: e :: suffix).
Proof.
  intros prefix e f suffix Hswap Hdrf i j x y Hx Hy Hconflict.
  assert (Hx' : nth_error (prefix ++ e :: f :: suffix)
    (swap_index (length prefix) i) = Some (Memory x)).
  { rewrite <- nth_error_swap, swap_index_involutive. exact Hx. }
  assert (Hy' : nth_error (prefix ++ e :: f :: suffix)
    (swap_index (length prefix) j) = Some (Memory y)).
  { rewrite <- nth_error_swap, swap_index_involutive. exact Hy. }
  destruct (Hdrf _ _ _ _ Hx' Hy' Hconflict) as [Horder|Horder].
  - left. apply (collective_orders_swap _ _ _ _ _ _ _ _ Hswap Hx' Hy') in Horder.
    now rewrite !swap_index_involutive in Horder.
  - right. apply (collective_orders_swap _ _ _ _ _ _ _ _ Hswap Hy' Hx') in Horder.
    now rewrite !swap_index_involutive in Horder.
Qed.

Lemma memory_events_app : forall prefix suffix,
  memory_events (prefix ++ suffix) = memory_events prefix ++ memory_events suffix.
Proof. induction prefix as [|[o|g] prefix IH]; intros suffix; cbn; congruence. Qed.

Lemma read_history_app : forall tid prefix suffix,
  read_history tid (prefix ++ suffix) = read_history tid prefix ++ read_history tid suffix.
Proof. intros; unfold read_history; now rewrite memory_events_app, filter_app. Qed.

Lemma read_history_swap : forall prefix e f suffix,
  swappable e f -> forall tid,
  read_history tid (prefix ++ e :: f :: suffix) =
  read_history tid (prefix ++ f :: e :: suffix).
Proof.
  intros prefix [x|g] [y|h] suffix Hswap tid;
    rewrite !read_history_app; f_equal; unfold read_history; cbn; try reflexivity.
  destruct (Nat.eqb (av_owner (access x)) tid) eqn:Hx,
    (Nat.eqb (av_owner (access y)) tid) eqn:Hy; cbn; try reflexivity.
  exfalso. apply Nat.eqb_eq in Hx, Hy. destruct Hswap as [Hswap _]. apply Hswap; congruence.
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
Proof.
  intros [e|] left right H; [apply (reorders_prefix _ _ H [e])|assumption].
Qed.

Lemma reorders_memory_drf : forall left right,
  reorders left right -> MemDRF left -> MemDRF right.
Proof. intros left right H; induction H; eauto using memory_drf_swap. Qed.

Lemma reorders_read_history : forall left right,
  reorders left right -> forall tid, read_history tid left = read_history tid right.
Proof.
  intros left right H. induction H; intros tid; auto using read_history_swap.
  now rewrite IHreorders1, IHreorders2.
Qed.

Lemma memory_drf_tail : forall e trace, MemDRF (e :: trace) -> MemDRF trace.
Proof.
  intros e trace H i j x y Hx Hy Hconflict.
  destruct (H (S i) (S j) x y Hx Hy Hconflict) as [Horder|Horder];
    destruct Horder as [[|k] [group [Hk [Hi [Hj Hgroup]]]]]; try lia.
  - left; exists k, group; cbn in Hk; repeat split; intuition lia.
  - right; exists k, group; cbn in Hk; repeat split; intuition lia.
Qed.

Lemma memory_drf_emit_tail : forall e trace,
  MemDRF (emit_event e trace) -> MemDRF trace.
Proof. intros [e|] trace H; [eapply memory_drf_tail|]; eauto. Qed.
