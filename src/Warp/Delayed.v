From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import NatUtil AVal.
From Faial.Core Require Mem.
From Faial.Warp Require Import Semantics.

Import ListNotations.

Record write := Write {
  owner : nat;
  address : nat;
  contents : nat;
}.

Record state := State {
  committed : Mem.t;
  pending : list write;
}.

Definition initial := State Mem.empty [].

(* Newest writes are first; folding from the right preserves write order. *)
Fixpoint publish (writes : list write) (m : Mem.t) : Mem.t :=
  match writes with
  | [] => m
  | w :: rest => Map_NAT.add (address w) (contents w) (publish rest m)
  end.

Definition view tid s :=
  publish (filter (fun w => Nat.eqb (owner w) tid) (pending s)) (committed s).

Definition read input tid location s := load input (view tid s) location.

Definition store tid location value s :=
  State (committed s) (Write tid location value :: pending s).

Definition selected group w := existsb (Nat.eqb (owner w)) group.

Definition flush group s :=
  State (publish (filter (selected group) (pending s)) (committed s))
    (filter (fun w => negb (selected group w)) (pending s)).

(* Kernel completion publishes the remaining writes before the host observes
   final memory. This is not a cross-thread synchronization event. *)
Definition finish s := State (publish (pending s) (committed s)) [].

Lemma selected_spec : forall group w, selected group w = true <-> In (owner w) group.
Proof.
  intros group w. unfold selected. rewrite existsb_exists. split.
  - intros [tid [Hin Heq]]. apply Nat.eqb_eq in Heq. now subst tid.
  - intros Hin. exists (owner w). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma read_own_write : forall input tid location value s,
  read input tid location (store tid location value s) = value.
Proof.
  intros. unfold read, view, store; cbn. rewrite Nat.eqb_refl. cbn.
  apply load_after_write.
Qed.

Lemma other_thread_does_not_see_store : forall input tid other location value s,
  tid <> other ->
  read input other location (store tid location value s) = read input other location s.
Proof.
  intros input tid other location value s Hneq.
  unfold read, view, store; cbn. apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma store_does_not_publish : forall tid location value s,
  committed (store tid location value s) = committed s.
Proof. reflexivity. Qed.

Lemma flush_removes_participant_writes : forall group s w,
  In w (pending (flush group s)) -> ~ In (owner w) group.
Proof.
  intros group s w Hin Howner. apply filter_In in Hin as [_ Hnot].
  apply negb_true_iff in Hnot. apply selected_spec in Howner. congruence.
Qed.

Lemma flush_keeps_nonparticipant_writes : forall group s w,
  ~ In (owner w) group ->
  (In w (pending (flush group s)) <-> In w (pending s)).
Proof.
  intros group s w Hnot. cbn. rewrite filter_In. split; [tauto|].
  intros Hin. split; [exact Hin|]. apply negb_true_iff.
  destruct (selected group w) eqn:Hselected; [|reflexivity].
  exfalso. apply Hnot. now apply selected_spec.
Qed.

Lemma publish_unwritten : forall writes m input location,
  (forall w, In w writes -> address w <> location) ->
  load input (publish writes m) location = load input m location.
Proof.
  induction writes as [|w rest IH]; intros m input location Hnot; [reflexivity|].
  cbn [publish]. unfold load at 1.
  rewrite Map_NAT_Facts.add_neq_o by (apply Hnot; now left).
  change (load input (publish rest m) location = load input m location).
  apply IH. intros x Hin. apply Hnot. now right.
Qed.

Lemma flush_only_publishes_participants : forall group s input location,
  (forall w, In w (pending s) -> In (owner w) group -> address w <> location) ->
  load input (committed (flush group s)) location = load input (committed s) location.
Proof.
  intros group s input location Hnot. apply publish_unwritten.
  intros w Hin. apply filter_In in Hin as [Hin Hselected].
  apply Hnot; auto. now apply selected_spec.
Qed.

Lemma flush_empty : forall s, flush [] s = s.
Proof.
  intros [m writes]. unfold flush, selected; cbn.
  now rewrite filter_false, filter_true.
Qed.

Lemma flush_idempotent : forall group s, flush group (flush group s) = flush group s.
Proof.
  intros group s.
  assert (Hnot : forall w, In w (pending (flush group s)) -> selected group w = false).
  { intros w Hin. destruct (selected group w) eqn:Hsel; [|reflexivity].
    exfalso. eapply flush_removes_participant_writes; [exact Hin|]. now apply selected_spec. }
  assert (Hnone : filter (selected group) (pending (flush group s)) = []).
  { rewrite <- (filter_false (pending (flush group s))).
    apply filter_ext_in. intros w Hin. now apply Hnot. }
  assert (Hsame : filter (fun w => negb (selected group w)) (pending (flush group s)) =
    pending (flush group s)).
  { apply forallb_filter_id. apply forallb_forall. intros w Hin.
    now rewrite (Hnot w Hin). }
  unfold flush at 1. rewrite Hnone, Hsame. destruct (flush group s); reflexivity.
Qed.

Lemma view_after_flush : forall tid group s,
  In tid group -> view tid (flush group s) = committed (flush group s).
Proof.
  intros tid group s Hin. unfold view.
  assert (Hempty : filter (fun w => Nat.eqb (owner w) tid) (pending (flush group s)) = []).
  { rewrite <- (filter_false (pending (flush group s))).
    apply filter_ext_in. intros w Hw. apply Nat.eqb_neq.
    intros Heq. apply (flush_removes_participant_writes _ _ _ Hw). now rewrite Heq. }
  now rewrite Hempty.
Qed.

Lemma participant_views_agree : forall input group s t u location,
  In t group -> In u group ->
  read input t location (flush group s) = read input u location (flush group s).
Proof.
  intros input group s t u location Ht Hu. unfold read.
  now rewrite !view_after_flush by assumption.
Qed.

(* Logical memory includes every issued write. It is used only to relate the
   delayed implementation to SC; threads still read their own views. *)
Definition logical s := publish (pending s) (committed s).

Definition coherent s := forall x y,
  In x (pending s) -> In y (pending s) -> address x = address y -> owner x = owner y.

Lemma load_publish : forall writes m input location,
  load input (publish writes m) location =
    match find (fun w => Nat.eqb (address w) location) writes with
    | Some w => contents w
    | None => load input m location
    end.
Proof.
  induction writes as [|w rest IH]; intros m input location; [reflexivity|].
  cbn [publish find]. destruct (Nat.eqb (address w) location) eqn:Heq.
  - apply Nat.eqb_eq in Heq. rewrite Heq. apply load_after_write.
  - apply Nat.eqb_neq in Heq. unfold load at 1.
    rewrite Map_NAT_Facts.add_neq_o by exact Heq. apply IH.
Qed.

Local Lemma find_address_filter : forall writes location p b,
  (forall w, In w writes -> address w = location -> p w = b) ->
  find (fun w => Nat.eqb (address w) location) (filter p writes) =
    if b then find (fun w => Nat.eqb (address w) location) writes else None.
Proof.
  induction writes as [|w rest IH]; intros location p b Hconstant; cbn; [now destruct b|].
  assert (Hrest : forall x, In x rest -> address x = location -> p x = b).
  { intros x Hin Heq. apply Hconstant; [now right|exact Heq]. }
  specialize (IH location p b Hrest).
  destruct (Nat.eqb (address w) location) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    rewrite (Hconstant w (or_introl eq_refl) Heq). destruct b; cbn.
    + rewrite Heq, Nat.eqb_refl. reflexivity.
    + exact IH.
  - destruct (p w); cbn; rewrite ?Heq; exact IH.
Qed.

Lemma read_matches_logical : forall input tid location s,
  (forall w, In w (pending s) -> address w = location -> owner w = tid) ->
  read input tid location s = load input (logical s) location.
Proof.
  intros input tid location s Hown. unfold read, view, logical. rewrite !load_publish.
  rewrite (find_address_filter _ _ _ true); [reflexivity|].
  intros w Hin Heq. rewrite (Hown w Hin Heq). apply Nat.eqb_refl.
Qed.

Lemma flush_preserves_logical : forall input group s,
  coherent s -> forall location,
  load input (logical (flush group s)) location = load input (logical s) location.
Proof.
  intros input group [m writes] Hcoherent location.
  unfold coherent in Hcoherent; cbn in Hcoherent.
  destruct (find (fun w => Nat.eqb (address w) location) writes) as [w|] eqn:Hfind.
  - apply find_some in Hfind as [Hin Heq]. apply Nat.eqb_eq in Heq.
    assert (Hconstant : forall x, In x writes -> address x = location ->
      selected group x = selected group w).
    { intros x Hx Haddr. unfold selected. rewrite (Hcoherent x w Hx Hin) by congruence.
      reflexivity. }
    unfold logical, flush; cbn. rewrite !load_publish.
    rewrite (find_address_filter _ _ _ (selected group w) Hconstant).
    rewrite (find_address_filter _ _ _ (negb (selected group w))).
    + now destruct (selected group w).
    + intros x Hx Haddr. now rewrite (Hconstant x Hx Haddr).
  - assert (Hnone : forall w, In w writes -> address w <> location).
    { intros w Hin. apply Nat.eqb_neq. exact (find_none _ _ Hfind w Hin). }
    unfold logical, flush; cbn.
    rewrite !publish_unwritten; auto;
      intros w Hin; apply filter_In in Hin as [Hin _]; now apply Hnone.
Qed.

Lemma flush_preserves_coherence : forall group s, coherent s -> coherent (flush group s).
Proof.
  intros group s Hcoherent x y Hx Hy Heq.
  apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _]. eauto.
Qed.

Lemma store_preserves_coherence : forall tid location value s,
  coherent s ->
  (forall w, In w (pending s) -> address w = location -> owner w = tid) ->
  coherent (store tid location value s).
Proof.
  intros tid location value s Hcoherent Hown x y [<-|Hx] [<-|Hy] Heq; cbn in *;
    eauto; symmetry; eauto.
Qed.

Example own_write_is_immediate : read (fun _ => 0) 0 0 (store 0 0 5 initial) = 5.
Proof. reflexivity. Qed.

Example another_thread_sees_old_value : read (fun _ => 0) 1 0 (store 0 0 5 initial) = 0.
Proof. reflexivity. Qed.

Example participant_sees_published_write :
  read (fun _ => 0) 1 0 (flush [0; 1] (store 0 0 5 initial)) = 5.
Proof. reflexivity. Qed.

Example excluded_writer_is_not_flushed :
  read (fun _ => 0) 1 0 (flush [1; 2] (store 0 0 5 initial)) = 0 /\
  pending (flush [1; 2] (store 0 0 5 initial)) = [Write 0 0 5].
Proof. split; reflexivity. Qed.

Example repeated_writes_keep_latest_value :
  read (fun _ => 0) 1 0 (flush [0; 1] (store 0 0 7 (store 0 0 5 initial))) = 7.
Proof. reflexivity. Qed.

Example final_memory_includes_unpublished_writes :
  load (fun _ => 0) (committed (finish (store 0 0 5 initial))) 0 = 5.
Proof. reflexivity. Qed.
