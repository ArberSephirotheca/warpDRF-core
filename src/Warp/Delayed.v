From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Faial.Core Require Import AVal NatUtil.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Commute Agree.

Import ListNotations.

(* A target with delayed visibility, after GPUVerify's synchronous, delayed
   visibility semantics. A thread's write stays pending, visible only to that
   thread, until the thread takes part in a primitive that orders memory; the
   release of such a primitive publishes the pending writes of its
   participants. A primitive that does not order memory publishes nothing.
   Kernel completion publishes the remaining writes before final memory is
   observed. Control is SSO's. *)

Record pending_write := Pending {
  owner : nat;
  location : nat;
  contents : nat;
}.

Record dstate := DState {
  dcodes : list code;
  committed : Mem.t;
  pending : list pending_write;
}.

Definition dinitial (programs : list code) := DState programs Mem.empty [].

(* Newest writes first; publishing folds from the right, so the newest wins. *)
Fixpoint publish (writes : list pending_write) (m : Mem.t) : Mem.t :=
  match writes with
  | [] => m
  | w :: rest => Map_NAT.add (location w) (contents w) (publish rest m)
  end.

Definition own (tid : nat) (w : pending_write) : bool := Nat.eqb (owner w) tid.

(* What a thread reads: committed memory with its own pending writes. *)
Definition view (tid : nat) (d : dstate) : Mem.t :=
  publish (filter (own tid) (pending d)) (committed d).

(* Memory with every pending write published. *)
Definition logical (d : dstate) : Mem.t := publish (pending d) (committed d).

Definition in_group (group : list nat) (w : pending_write) : bool :=
  existsb (Nat.eqb (owner w)) group.

(* A write becomes pending; other steps leave the pending writes alone. *)
Definition buffer (o : option observation) (tid : nat) (writes : list pending_write) :=
  match o with
  | Some (Observe a v) =>
      match av_mode a with
      | m_write => Pending tid (av_index a) v :: writes
      | m_read => writes
      end
  | None => writes
  end.

Definition drelease (i : instance) (group : list nat) (d : dstate) : dstate :=
  if site_sync (fst i) then
    DState (release i (dcodes d))
      (publish (filter (in_group group) (pending d)) (committed d))
      (filter (fun w => negb (in_group group w)) (pending d))
  else DState (release i (dcodes d)) (committed d) (pending d).

Definition dadvance input (a : action) (d : dstate) : option (option event * dstate) :=
  match a with
  | Thread tid =>
      match nth_error (dcodes d) tid with
      | Some c =>
          match step tid input (view tid d) c with
          | Some (o, _, c') =>
              Some (option_map Memory o,
                DState (replace_thread tid c' (dcodes d)) (committed d)
                  (buffer o tid (pending d)))
          | None => None
          end
      | None => None
      end
  | Release i =>
      match arrived i (dcodes d), unknown i (dcodes d) with
      | (_ :: _) as group, [] => Some (Some (Sync i group), drelease i group d)
      | _, _ => None
      end
  end.

Inductive dexecution input : dstate -> list event -> dstate -> Prop :=
| dexecution_refl : forall d, dexecution input d [] d
| dexecution_step : forall a d e d' trace last,
    dadvance input a d = Some (e, d') ->
    dexecution input d' trace last ->
    dexecution input d (emit_event e trace) last.

(* Run a schedule; fails if an action is not enabled. *)
Fixpoint drun input (schedule : list action) (d : dstate)
    : option (list event * dstate) :=
  match schedule with
  | [] => Some ([], d)
  | a :: rest =>
      match dadvance input a d with
      | Some (e, d') =>
          match drun input rest d' with
          | Some (trace, last) => Some (emit_event e trace, last)
          | None => None
          end
      | None => None
      end
  end.

Lemma drun_sound : forall input schedule d trace last,
  drun input schedule d = Some (trace, last) -> dexecution input d trace last.
Proof.
  intros input schedule. induction schedule as [|a rest IH]; intros d trace last Hrun;
    cbn in Hrun.
  - inversion Hrun; subst. constructor.
  - destruct (dadvance input a d) as [[e d']|] eqn:Hstep; try discriminate.
    destruct (drun input rest d') as [[tail final]|] eqn:Hrest; try discriminate.
    inversion Hrun; subst. econstructor; [exact Hstep|]. now apply IH.
Qed.

(* A completed run; the observed final memory has every write published. *)
Definition delayed_completed input programs trace last :=
  exists d, dexecution input (dinitial programs) trace d /\
    last = State (logical d) (dcodes d) /\ finished last.

(* Publishing. *)

Lemma load_add : forall input m a v b,
  load input (Map_NAT.add a v m) b = if Nat.eq_dec a b then v else load input m b.
Proof.
  intros input m a v b. unfold load. destruct (Nat.eq_dec a b) as [->|Hne].
  - now rewrite Map_NAT_Facts.add_eq_o by reflexivity.
  - now rewrite Map_NAT_Facts.add_neq_o by exact Hne.
Qed.

Lemma load_publish_equiv : forall input writes m n a,
  load input m a = load input n a ->
  load input (publish writes m) a = load input (publish writes n) a.
Proof.
  intros input writes m n a H. induction writes as [|w rest IH]; cbn [publish]; [exact H|].
  rewrite !load_add. destruct (Nat.eq_dec (location w) a); [reflexivity|exact IH].
Qed.

Lemma load_publish_untouched : forall input writes m a,
  (forall w, In w writes -> location w <> a) ->
  load input (publish writes m) a = load input m a.
Proof.
  intros input writes m a H. induction writes as [|w rest IH]; cbn [publish]; [reflexivity|].
  rewrite load_add. destruct (Nat.eq_dec (location w) a) as [Heq|_].
  - exfalso. exact (H w (or_introl eq_refl) Heq).
  - apply IH. intros x Hx. apply H. now right.
Qed.

Lemma load_publish_filter : forall input p writes m a,
  (forall w, In w writes -> location w = a -> p w = true) ->
  load input (publish (filter p writes) m) a = load input (publish writes m) a.
Proof.
  intros input p writes m a H. induction writes as [|w rest IH]; cbn [filter]; [reflexivity|].
  assert (IH' : load input (publish (filter p rest) m) a = load input (publish rest m) a)
    by (apply IH; intros x Hx; apply H; now right).
  destruct (p w) eqn:Hp; cbn [publish]; rewrite ?load_add.
  - destruct (Nat.eq_dec (location w) a); [reflexivity|exact IH'].
  - destruct (Nat.eq_dec (location w) a) as [Heq|_].
    + rewrite (H w (or_introl eq_refl) Heq) in Hp. discriminate.
    + exact IH'.
Qed.

(* Publishing one part of the pending writes before the other gives the same
   memory when writes to one location all fall in the same part. *)
Lemma load_publish_split : forall input q writes m a,
  (forall w1 w2, In w1 writes -> In w2 writes -> location w1 = location w2 -> q w1 = q w2) ->
  load input (publish (filter (fun w => negb (q w)) writes) (publish (filter q writes) m)) a =
  load input (publish writes m) a.
Proof.
  intros input q writes m a Hq.
  destruct (existsb (fun w => Nat.eqb (location w) a && q w) writes) eqn:Hex.
  - apply existsb_exists in Hex as [w0 [Hw0 Hsel]].
    apply andb_true_iff in Hsel as [Hloc Hq0]. apply Nat.eqb_eq in Hloc.
    rewrite load_publish_untouched.
    + apply load_publish_filter. intros w Hw Hwloc.
      rewrite (Hq w w0 Hw Hw0 (eq_trans Hwloc (eq_sym Hloc))). exact Hq0.
    + intros w Hw Hwloc. apply filter_In in Hw as [Hw Hneg].
      rewrite (Hq w w0 Hw Hw0 (eq_trans Hwloc (eq_sym Hloc))), Hq0 in Hneg. discriminate.
  - assert (Hnone : forall w, In w writes -> location w = a -> q w = false).
    { intros w Hw Hwloc. destruct (q w) eqn:Hqw; [|reflexivity]. exfalso.
      assert (Htrue : existsb (fun w => Nat.eqb (location w) a && q w) writes = true).
      { apply existsb_exists. exists w. split; [exact Hw|].
        now rewrite Hwloc, Nat.eqb_refl, Hqw. }
      congruence. }
    transitivity (load input (publish (filter (fun w => negb (q w)) writes) m) a).
    + apply load_publish_equiv. apply load_publish_untouched.
      intros w Hw Hwloc. apply filter_In in Hw as [Hw Hqw].
      rewrite (Hnone w Hw Hwloc) in Hqw. discriminate.
    + apply load_publish_filter. intros w Hw Hwloc. now rewrite (Hnone w Hw Hwloc).
Qed.

Lemma view_logical : forall input tid d a,
  (forall w, In w (pending d) -> location w = a -> owner w = tid) ->
  load input (view tid d) a = load input (logical d) a.
Proof.
  intros input tid d a H. unfold view, logical. apply load_publish_filter.
  intros w Hw Hloc. unfold own. apply Nat.eqb_eq. exact (H w Hw Hloc).
Qed.

Lemma publish_buffer : forall o tid writes m,
  publish (buffer o tid writes) m = effect o (publish writes m).
Proof. intros [[a v]|] tid writes m; cbn; [destruct (av_mode a)|]; reflexivity. Qed.

Lemma in_group_spec : forall group w, in_group group w = true <-> In (owner w) group.
Proof.
  intros group w. unfold in_group. rewrite existsb_exists. split.
  - intros [t [Hin Heq]]. apply Nat.eqb_eq in Heq. now subst t.
  - intros Hin. exists (owner w). split; [exact Hin|apply Nat.eqb_refl].
Qed.

(* Pending writes and memory DRF. *)

Definition write_event (w : pending_write) :=
  Memory (Observe (av_write (owner w) (location w)) (contents w)).

(* The write was issued, and no later primitive that orders memory has
   included its owner. *)
Definition unpublished (trace : list event) (w : pending_write) := exists before after,
  trace = before ++ write_event w :: after /\
  forall i g, In (Sync i g) after -> ~ involves (Sync i g) (owner w).

Lemma unpublished_append : forall trace tail w,
  unpublished trace w ->
  (forall i g, In (Sync i g) tail -> ~ involves (Sync i g) (owner w)) ->
  unpublished (trace ++ tail) w.
Proof.
  intros trace tail w [before [after [-> Hafter]]] Htail.
  exists before, (after ++ tail). split; [now rewrite <- app_assoc|].
  intros i g Hin. apply in_app_or in Hin as [Hin|Hin]; eauto.
Qed.

(* Happens-before cannot leave a thread that takes part in no primitive that
   orders memory. *)
Lemma hb_quiet : forall trace u p q,
  (forall e t, nth_error trace p = Some e -> involves e t -> t = u) ->
  (forall k i g, p < k -> k <= q -> nth_error trace k = Some (Sync i g) ->
    ~ involves (Sync i g) u) ->
  hb trace p q ->
  forall e t, nth_error trace q = Some e -> involves e t -> t = u.
Proof.
  intros trace u p q Hstart Hquiet Hhb.
  apply clos_trans_tn1 in Hhb. revert Hquiet.
  induction Hhb as [q Hstep|y q Hstep Hhb IH]; intros Hquiet e t Hq Ht.
  - destruct Hstep as [Hlt [e0 [f [t0 [He0 [Hf [Ht0 Hft0]]]]]]].
    rewrite Hq in Hf. inversion Hf; subst f.
    pose proof (Hstart _ _ He0 Ht0) as ->.
    destruct e as [o|i g]; cbn [involves] in Ht, Hft0.
    + congruence.
    + exfalso. exact (Hquiet q i g Hlt (le_n q) Hq Hft0).
  - destruct Hstep as [Hlt [e0 [f [t0 [He0 [Hf [Ht0 Hft0]]]]]]].
    rewrite Hq in Hf. inversion Hf; subst f.
    assert (Hpy : p < y) by (apply clos_tn1_trans in Hhb; exact (hb_lt _ _ _ Hhb)).
    assert (Hquiet' : forall k i g, p < k -> k <= y -> nth_error trace k = Some (Sync i g) ->
      ~ involves (Sync i g) u) by (intros k i g Hk1 Hk2; apply Hquiet; lia).
    pose proof (IH Hquiet' _ _ He0 Ht0) as ->.
    destruct e as [o|i g]; cbn [involves] in Ht, Hft0.
    + congruence.
    + exfalso. exact (Hquiet q i g (Nat.lt_trans _ _ _ Hpy Hlt) (le_n q) Hq Hft0).
Qed.

(* In a memory-DRF trace, an access right after the history cannot conflict
   with another thread's write that is still unpublished. *)
Lemma unpublished_no_conflict : forall history rest w o,
  unpublished history w -> MemDRF ((history ++ [Memory o]) ++ rest) ->
  av_owner (access o) <> owner w -> av_index (access o) = location w -> False.
Proof.
  intros history rest w o [before [after [-> Hafter]]] Hdrf Howner Hindex.
  replace (((before ++ write_event w :: after) ++ [Memory o]) ++ rest)
    with (before ++ write_event w :: (after ++ Memory o :: rest)) in Hdrf
    by (rewrite <- !app_assoc; reflexivity).
  set (trace := before ++ write_event w :: (after ++ Memory o :: rest)) in Hdrf.
  set (p := length before). set (q := length before + S (length after)).
  assert (Hp : nth_error trace p = Some (write_event w)).
  { unfold trace, p. rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag. }
  assert (Hq : nth_error trace q = Some (Memory o)).
  { unfold trace, q. rewrite nth_error_app2 by lia.
    replace (length before + S (length after) - length before) with (S (length after)) by lia.
    cbn. rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag. }
  assert (Hconflict : Conflict (av_write (owner w) (location w)) (access o)).
  { apply conflict_l; cbn; congruence. }
  destruct (Hdrf p q _ _ Hp Hq Hconflict) as [Hhb|Hhb].
  - apply Howner.
    refine (hb_quiet trace (owner w) p q _ _ Hhb (Memory o) _ Hq eq_refl).
    + intros e t He Ht. rewrite Hp in He. inversion He; subst e. cbn in Ht. congruence.
    + intros k i g Hk1 Hk2 Hk Hinv.
      assert (Hkq : k <> q) by (intros ->; rewrite Hq in Hk; discriminate).
      unfold trace, p, q in *. rewrite nth_error_app2 in Hk by lia.
      destruct (k - length before) as [|j] eqn:Hj; [lia|]. cbn in Hk.
      rewrite nth_error_app1 in Hk by lia.
      exact (Hafter i g (nth_error_In _ _ Hk) Hinv).
  - apply hb_lt in Hhb. unfold p, q in Hhb. lia.
Qed.

(* Steps. *)

Lemma step_access : forall c tid input ma mb e ma' ca f mb' cb,
  step tid input ma c = Some (e, ma', ca) -> step tid input mb c = Some (f, mb', cb) ->
  option_map access e = option_map access f.
Proof.
  induction c; intros tid input ma mb e ma' ca f mb' cb H1 H2.
  - cbn in H1, H2. destruct (n_step tid n); try discriminate.
    inversion H1; inversion H2; subst; reflexivity.
  - cbn in H1, H2. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H1; inversion H2; subst; reflexivity.
  - destruct (ender c1) eqn:Hend.
    + destruct c1; try discriminate; cbn in H1, H2; inversion H1; inversion H2; subst;
        reflexivity.
    + rewrite step_seq_other in H1, H2 by exact Hend.
      destruct (step tid input ma c1) as [[[e1 m1] f1]|] eqn:S1; try discriminate.
      destruct (step tid input mb c1) as [[[e2 m2] f2]|] eqn:S2; try discriminate.
      inversion H1; inversion H2; subst. eapply IHc1; eauto.
  - cbn in H1, H2. destruct (b_step tid b); try discriminate.
    inversion H1; inversion H2; subst; reflexivity.
  - cbn in H1, H2. inversion H1; inversion H2; subst; reflexivity.
  - destruct (ender c1) eqn:Hend.
    + destruct c1; try discriminate; cbn in H1, H2; inversion H1; inversion H2; subst;
        reflexivity.
    + rewrite step_iter_other in H1, H2 by exact Hend.
      destruct (step tid input ma c1) as [[[e1 m1] f1]|] eqn:S1; try discriminate.
      destruct (step tid input mb c1) as [[[e2 m2] f2]|] eqn:S2; try discriminate.
      inversion H1; inversion H2; subst. eapply IHc1; eauto.
  - cbn in H1; discriminate.
  - cbn in H1; discriminate.
  - cbn in H1, H2. match type of H1 with context [eval_all ?t ?a] =>
      destruct (eval_all t a) end; try discriminate.
    inversion H1; inversion H2; subst; reflexivity.
  - cbn in H1; discriminate.
  - cbn in H1; discriminate.
  - cbn in H1, H2. match type of H1 with context [eval_all ?t ?a] =>
      destruct (eval_all t a) end; try discriminate.
    inversion H1; inversion H2; subst; reflexivity.
  - cbn in H1; discriminate.
Qed.

Lemma execution_append : forall input s h1 m h2 last,
  execution input s h1 m -> execution input m h2 last -> execution input s (h1 ++ h2) last.
Proof.
  intros input s h1 m h2 last H1 H2.
  induction H1 as [s|a s e s' h1 m Hstep H1 IH]; [exact H2|].
  replace (emit_event e h1 ++ h2) with (emit_event e (h1 ++ h2)) by (destruct e; reflexivity).
  econstructor; eauto.
Qed.

(* Any run that starts like a completed memory-DRF run from the same state
   extends to a memory-DRF trace. *)
Lemma prefix_drf : forall input programs reference_trace reference_last history s,
  execution input (initial programs) reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  execution input (initial programs) history s ->
  exists rest, MemDRF (history ++ rest).
Proof.
  intros input programs reference_trace reference_last history s Href Hdone Hdrf Hexec.
  destruct (prefix_agreement _ _ _ _ Hexec _ _ Href Hdone Hdrf)
    as [rest [final [_ [_ [_ Horder]]]]].
  exists rest. exact (reorders_memory_drf _ _ Horder Hdrf).
Qed.

(* A delayed state matches an SC state after the same history: the same code,
   the same memory once every pending write is published, pending writes that
   are still unpublished in the history, and no two threads with pending
   writes to one location. *)
Definition related input (history : list event) (d : dstate) (s : state) :=
  dcodes d = threads s /\
  (forall a, load input (logical d) a = load input (memory s) a) /\
  (forall w, In w (pending d) -> unpublished history w) /\
  (forall w1 w2, In w1 (pending d) -> In w2 (pending d) ->
    location w1 = location w2 -> owner w1 = owner w2).

(* Each delayed step is the SC step with the same action and event. *)
Lemma dstep_matches : forall input programs reference_trace reference_last,
  execution input (initial programs) reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  forall history s d a e d',
  execution input (initial programs) history s -> related input history d s ->
  dadvance input a d = Some (e, d') ->
  exists s', advance input a s = Some (e, s') /\
    related input (history ++ emit_event e []) d' s'.
Proof.
  intros input programs reference_trace reference_last Href Hrefdone Hrefdrf
    history s d [tid|i] e d' Hsso [Hcodes [Hmem [Hsupp Hdisj]]] Hd.
  - cbn [dadvance] in Hd.
    destruct (nth_error (dcodes d) tid) as [c|] eqn:Hc; [|discriminate].
    destruct (step tid input (view tid d) c) as [[[o mv] c']|] eqn:Hstep; [|discriminate].
    inversion Hd; subst e d'. clear Hd.
    rewrite Hcodes in Hc.
    destruct (step_enabled_memory _ _ _ _ _ _ _ (memory s) Hstep) as [o' [m' [c'' Hsc]]].
    assert (Hexec1 : execution input (initial programs)
      (history ++ emit_event (option_map Memory o') [])
      (State m' (replace_thread tid c'' (threads s)))).
    { eapply execution_append; [exact Hsso|].
      econstructor; [eapply thread_build; eassumption|constructor]. }
    destruct (prefix_drf _ _ _ _ _ _ Href Hrefdone Hrefdrf Hexec1) as [rest Hdrf1].
    pose proof (step_access _ _ _ _ _ _ _ _ _ _ _ Hstep Hsc) as Hacc.
    pose proof (step_replay _ _ _ _ _ _ _ Hstep) as [_ [Hr [Howner Hreplay]]].
    assert (Hlocal : forall acc v, o = Some (Observe acc v) ->
      forall w, In w (pending d) -> location w = av_index acc -> owner w = tid).
    { intros acc v -> w Hw Hloc.
      destruct o' as [o'|]; [|discriminate Hacc]. cbn in Hacc. injection Hacc as Hacc.
      pose proof (Howner _ eq_refl) as Hown. cbn in Hown.
      destruct (Nat.eq_dec (owner w) tid) as [Heq|Hne]; [exact Heq|exfalso].
      apply (unpublished_no_conflict history rest w o' (Hsupp w Hw) Hdrf1);
        rewrite <- Hacc; congruence. }
    assert (Hread : readable input (memory s) o).
    { destruct o as [[acc v]|]; [|exact I]. cbn in Hr |- *.
      destruct (av_mode acc) eqn:Hmode; [|exact I].
      rewrite <- Hr, <- Hmem. symmetry. apply view_logical.
      exact (Hlocal acc v eq_refl). }
    pose proof (Hreplay _ Hread) as Hsc2. rewrite Hsc2 in Hsc.
    inversion Hsc; subst o' m' c''. clear Hsc.
    exists (State (effect o (memory s)) (replace_thread tid c' (threads s))).
    split; [eapply thread_build; eassumption|].
    split; [cbn; now rewrite Hcodes|].
    split.
    { intros a. unfold logical. cbn [pending committed memory].
      rewrite publish_buffer. apply effect_equiv. exact Hmem. }
    split.
    { intros w Hw. cbn [pending] in Hw. destruct o as [[acc v]|]; cbn [buffer] in Hw.
      - destruct (av_mode acc) eqn:Hmode.
        + apply unpublished_append; [exact (Hsupp w Hw)|].
          intros i g [Heq|[]]; discriminate.
        + destruct Hw as [<-|Hw].
          * pose proof (Howner _ eq_refl) as Hown. cbn in Hown.
            exists history, []. split; [|intros i g []].
            unfold write_event. cbn [owner location contents emit_event option_map].
            destruct acc as [aw ai am]; cbn in Hown, Hmode |- *. subst. reflexivity.
          * apply unpublished_append; [exact (Hsupp w Hw)|].
            intros i g [Heq|[]]; discriminate.
      - apply unpublished_append; [exact (Hsupp w Hw)|]. intros i g []. }
    { intros w1 w2 Hw1 Hw2 Hloc. cbn [pending] in Hw1, Hw2.
      destruct o as [[acc v]|]; cbn [buffer] in Hw1, Hw2; [|exact (Hdisj _ _ Hw1 Hw2 Hloc)].
      destruct (av_mode acc) eqn:Hmode; [exact (Hdisj _ _ Hw1 Hw2 Hloc)|].
      pose proof (Hlocal acc v eq_refl) as Hl.
      destruct Hw1 as [<-|Hw1], Hw2 as [<-|Hw2]; cbn [owner location] in *.
      - reflexivity.
      - symmetry. exact (Hl w2 Hw2 (eq_sym Hloc)).
      - exact (Hl w1 Hw1 Hloc).
      - exact (Hdisj _ _ Hw1 Hw2 Hloc). }
  - cbn [dadvance] in Hd.
    destruct (arrived i (dcodes d)) as [|t g] eqn:Harr; [discriminate|].
    destruct (unknown i (dcodes d)) eqn:Hunk; [|discriminate].
    inversion Hd; subst e d'. clear Hd.
    rewrite Hcodes in Harr, Hunk.
    assert (Hsc : advance input (Release i) s =
      Some (Some (Sync i (t :: g)), State (memory s) (release i (threads s)))).
    { rewrite release_build by (rewrite ?Harr; congruence). now rewrite Harr. }
    exists (State (memory s) (release i (threads s))). split; [exact Hsc|].
    unfold drelease. destruct (site_sync (fst i)) eqn:Hsync.
    + split; [cbn; now rewrite Hcodes|]. split.
      { intros a. unfold logical. cbn [pending committed memory].
        rewrite load_publish_split; [apply Hmem|].
        intros w1 w2 Hw1 Hw2 Hloc. unfold in_group. now rewrite (Hdisj _ _ Hw1 Hw2 Hloc). }
      split.
      { intros w Hw. cbn [pending] in Hw. apply filter_In in Hw as [Hw Hout].
        apply unpublished_append; [exact (Hsupp w Hw)|].
        intros i' g' [Heq|[]]. inversion Heq; subst i' g'. intros [_ Hin].
        apply in_group_spec in Hin. rewrite Hin in Hout. discriminate. }
      { intros w1 w2 Hw1 Hw2 Hloc. cbn [pending] in Hw1, Hw2.
        apply filter_In in Hw1 as [Hw1 _]. apply filter_In in Hw2 as [Hw2 _].
        exact (Hdisj _ _ Hw1 Hw2 Hloc). }
    + split; [cbn; now rewrite Hcodes|]. split; [exact Hmem|]. split.
      { intros w Hw. apply unpublished_append; [exact (Hsupp w Hw)|].
        intros i' g' [Heq|[]]. inversion Heq; subst i' g'. intros [Hs _]. congruence. }
      { exact Hdisj. }
Qed.

Lemma delayed_simulation : forall input programs reference_trace reference_last,
  execution input (initial programs) reference_trace reference_last ->
  finished reference_last -> MemDRF reference_trace ->
  forall d trace d_last, dexecution input d trace d_last ->
  forall history s,
  execution input (initial programs) history s -> related input history d s ->
  exists s_last, execution input s trace s_last /\
    related input (history ++ trace) d_last s_last.
Proof.
  intros input programs reference_trace reference_last Href Hrefdone Hrefdrf
    d trace d_last Hdexec.
  induction Hdexec as [d|a d e d' trace d_last Hstep Hdexec IH];
    intros history s Hsso Hrel.
  - exists s. split; [constructor|]. now rewrite app_nil_r.
  - destruct (dstep_matches _ _ _ _ Href Hrefdone Hrefdrf _ _ _ _ _ _ Hsso Hrel Hstep)
      as [s' [Hstep' Hrel']].
    assert (Hsso' : execution input (initial programs) (history ++ emit_event e []) s').
    { eapply execution_append; [exact Hsso|]. econstructor; [exact Hstep'|constructor]. }
    destruct (IH _ _ Hsso' Hrel') as [s_last [Hrest Hrel_last]].
    exists s_last. split; [econstructor; eauto|].
    replace (history ++ emit_event e trace) with ((history ++ emit_event e []) ++ trace)
      by (destruct e; cbn; rewrite <- ?app_assoc; reflexivity).
    exact Hrel_last.
Qed.

(* Reference memory DRF alone suffices, as for SSO. *)
Theorem delayed_agreement_from_drf : forall programs fuel input reference_trace
    reference_last,
  run fuel input programs = Some (reference_trace, reference_last) ->
  MemDRF reference_trace ->
  forall trace last, delayed_completed input programs trace last ->
  same_observations input reference_trace reference_last trace last.
Proof.
  intros programs fuel input reference_trace reference_last Hrun Hdrf
    trace last [d [Hdexec [-> Hdone]]].
  pose proof Hrun as Hsound. apply run_sound in Hsound as [_ [Href Hrefdone]].
  assert (Hrel0 : related input [] (dinitial programs) (initial programs)).
  { split; [reflexivity|]. split; [intros a; reflexivity|].
    split; [intros w []|]. intros w1 w2 []. }
  destruct (delayed_simulation _ _ _ _ Href Hrefdone Hdrf _ _ _ Hdexec
    [] (initial programs) (execution_refl _ _) Hrel0) as [s_last [Hsso [Hcodes [Hmem _]]]].
  assert (Hfin : finished s_last).
  { unfold finished in *. cbn [threads] in Hdone. now rewrite <- Hcodes. }
  destruct (agreement_from_drf _ _ _ _ _ Hrun Hdrf _ _ Hsso Hfin)
    as [Hgroups [Hreads Hfinal]].
  split; [exact Hgroups|]. split; [exact Hreads|].
  intros a. rewrite Hfinal. cbn [memory]. symmetry. apply Hmem.
Qed.

(* The target with delayed visibility meets WarpDRF's guarantee: on a kernel
   that meets both conditions, every completed run has the reference's
   observations. *)
Theorem delayed_agreement : forall c, Guarantee c delayed_completed.
Proof.
  intros c programs fuel input reference_trace reference_last Hrun [Hdrf _].
  exact (delayed_agreement_from_drf _ _ _ _ _ Hrun Hdrf).
Qed.
