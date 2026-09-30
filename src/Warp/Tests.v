From Stdlib Require Import Lists.List Strings.String Arith.PeanoNat Bool.Bool Lia.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Faial.Core Require Import Var AVal.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Agree.

Import ListNotations.
Open Scope string_scope.

Definition zero_input (_ : nat) := 0.
Definition tid_is n := NRel NEquals NTid (NNum n).
Definition tid_below n := NRel NLt NTid (NNum n).
Definition plus1 e := NBin NPlus e (NNum 1).

(* Each thread keeps its loop counters in its own memory cells. *)
Definition counter := NBin NPlus (NNum 10) NTid.
Definition inner_counter := NBin NPlus (NNum 20) NTid.
Definition i_var := variable "i".
Definition j_var := variable "j".

(* A computable sufficient check for memory DRF: no two accesses conflict. *)

Definition is_write (a : access_val) : bool :=
  match av_mode a with m_write => true | m_read => false end.

Definition conflictb (a b : access_val) : bool :=
  negb (Nat.eqb (av_owner a) (av_owner b)) && Nat.eqb (av_index a) (av_index b) &&
  (is_write a || is_write b).

Lemma conflictb_complete : forall a b, Conflict a b -> conflictb a b = true.
Proof.
  intros [oa ia ma] [ob ib mb] H. unfold conflictb, is_write.
  inversion H as [Hown Hidx Hmode|Hown Hidx Hmode]; cbn in *; subst;
    rewrite (proj2 (Nat.eqb_neq _ _) Hown), Nat.eqb_refl; cbn;
    [reflexivity|now rewrite orb_true_r].
Qed.

Definition conflict_free (trace : list event) : bool :=
  let accesses := memory_events trace in
  forallb (fun e => forallb (fun f =>
    negb (conflictb (access e) (access f))) accesses) accesses.

Lemma memory_event_in : forall trace o, In (Memory o) trace -> In o (memory_events trace).
Proof.
  induction trace as [|first rest IH]; intros o Hin; [contradiction|].
  destruct first as [f|i g]; cbn in *.
  - destruct Hin as [Heq|Hin]; [inversion Heq; subst; auto|auto].
  - destruct Hin as [Heq|Hin]; [discriminate|auto].
Qed.

Lemma conflict_free_drf : forall trace, conflict_free trace = true -> MemDRF trace.
Proof.
  intros trace Hfree i j e f He Hf Hconflict. exfalso.
  apply conflictb_complete in Hconflict.
  apply nth_error_In, memory_event_in in He, Hf.
  unfold conflict_free in Hfree. rewrite forallb_forall in Hfree.
  specialize (Hfree e He). rewrite forallb_forall in Hfree.
  specialize (Hfree f Hf). now rewrite Hconflict in Hfree.
Qed.

(* A completed, conflict-free reference run fixes the group of an instance
   in every completed execution. *)
Lemma group_in_every_execution : forall fuel programs i expected,
  match run fuel zero_input programs with
  | Some (reference_trace, _) =>
      conflict_free reference_trace = true /\ groups_at i reference_trace = expected
  | None => False
  end ->
  forall trace last,
  execution zero_input (initial programs) trace last -> finished last ->
  groups_at i trace = expected.
Proof.
  intros fuel programs i expected H trace last Hexec Hdone.
  destruct (run fuel zero_input programs) as [[reference_trace reference_last]|] eqn:Hrun;
    [|contradiction].
  destruct H as [Hfree Hgroups].
  destruct (agreement_from_drf _ _ _ _ _ Hrun (conflict_free_drf _ Hfree) _ _ Hexec Hdone)
    as [Hsame _].
  rewrite <- Hsame. exact Hgroups.
Qed.

Ltac groups_by_reference fuel :=
  intros trace last Hexec Hdone; repeat split;
  (refine (group_in_every_execution fuel _ _ _ _ trace last Hexec Hdone);
   vm_compute; split; reflexivity).

Ltac finished_codes := unfold finished; repeat constructor.

(* Loop-free programs. *)

(* Threads 0 and 1 meet at barrier 1; inside, thread 0 alone runs barrier 2;
   all three threads meet at barrier 3. Each site gets its own group. *)
Definition nested :=
  Seq (Cond (tid_below 2) (Seq (Barrier 1) (Cond (tid_is 0) (Barrier 2) Skip)) Skip)
    (Barrier 3).

Theorem nested_groups : forall trace last,
  execution zero_input (initial [nested; nested; nested]) trace last -> finished last ->
  groups_at (BarrierSite 1, []) trace = [[0; 1]] /\
  groups_at (BarrierSite 2, []) trace = [[0]] /\
  groups_at (BarrierSite 3, []) trace = [[0; 1; 2]].
Proof. groups_by_reference 100. Qed.

(* Two independent collectives: the halves of the warp meet at different
   sites, whatever order the releases happen in. *)
Definition halves := Cond (tid_below 2) (Barrier 1) (Barrier 2).

Theorem halves_groups : forall trace last,
  execution zero_input (initial [halves; halves; halves; halves]) trace last ->
  finished last ->
  groups_at (BarrierSite 1, []) trace = [[0; 1]] /\
  groups_at (BarrierSite 2, []) trace = [[2; 3]].
Proof. groups_by_reference 100. Qed.

(* Thread 0 publishes x and meets thread 1 at barrier 1; thread 1 then meets
   thread 2 at barrier 2, and thread 2 reads x. No collective contains both
   threads 0 and 2: the write reaches the read only through the relay, which
   is why condition 1 uses the transitive happens-before. *)
Definition relay :=
  [Seq (Write (NNum 0) (NNum 1)) (Barrier 1);
   Seq (Barrier 1) (Barrier 2);
   Seq (Barrier 2) (Read (variable "r") (NNum 0) Skip)].

Definition relay_trace :=
  [Memory (Observe (av_write 0 0) 1);
   Sync (BarrierSite 1, []) [0; 1];
   Sync (BarrierSite 2, []) [1; 2];
   Memory (Observe (av_read 2 0) 1)].

Example relay_reference :
  exists last, run 100 zero_input relay = Some (relay_trace, last) /\ finished last.
Proof. eexists; split; [vm_compute; reflexivity|finished_codes]. Qed.

Ltac hb_link t :=
  split; [lia|]; do 2 eexists; exists t;
  split; [reflexivity|]; split; [reflexivity|]; cbn; split; auto.

Theorem relay_memory_drf : MemDRF relay_trace.
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 4).
  { apply (proj1 (nth_error_Some relay_trace i)). rewrite He. discriminate. }
  assert (Hj : j < 4).
  { apply (proj1 (nth_error_Some relay_trace j)). rewrite Hf. discriminate. }
  destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; cbn in *; congruence].
  - left. apply t_trans with 1; [apply t_step; hb_link 0|].
    apply t_trans with 2; apply t_step; [hb_link 1|hb_link 2].
  - right. apply t_trans with 1; [apply t_step; hb_link 0|].
    apply t_trans with 2; apply t_step; [hb_link 1|hb_link 2].
Qed.

Theorem relay_reads_published_value : forall trace last,
  execution zero_input (initial relay) trace last -> finished last ->
  read_history 2 trace = [Observe (av_read 2 0) 1].
Proof.
  intros trace last Hexec Hdone.
  destruct relay_reference as [reference_last [Hrun _]].
  destruct (agreement_from_drf _ _ _ _ _ Hrun relay_memory_drf _ _ Hexec Hdone)
    as [_ [Hreads _]].
  rewrite <- Hreads. reflexivity.
Qed.

(* Two threads wait at different sites, each still able to reach the other's:
   neither release is ever enabled, so SSO reports the deadlock. *)
Definition crossed :=
  [Seq (Barrier 1) (Barrier 2); Seq (Barrier 2) (Barrier 1)].

Example crossed_reference_fails : run 100 zero_input crossed = None.
Proof. vm_compute. reflexivity. Qed.

(* A run stays within states satisfying P; if none of them is finished, no run
   finishes. *)
Lemma never_finishes : forall (P : state -> Prop) input,
  (forall s, P s -> ~ finished s) ->
  (forall s a e s', P s -> advance input a s = Some (e, s') -> P s') ->
  forall s trace last, P s -> execution input s trace last -> ~ finished last.
Proof.
  intros P input Hnot Hclosed s trace last Hs Hexec.
  induction Hexec as [s|a s e s' trace last Hstep Hexec IH]; [exact (Hnot s Hs)|].
  exact (IH (Hclosed _ _ _ _ Hs Hstep)).
Qed.

(* A thread that has arrived at Barrier n. *)
Definition arrived_at (n : nat) := Wait n true false (fun _ _ => 0) [] unused Skip.

(* Each thread is before or at its first barrier. *)
Definition crossed_state (s : state) : Prop :=
  exists x y, threads s = [x; y] /\
    (x = Seq (Barrier 1) (Barrier 2) \/ x = Seq (arrived_at 1) (Barrier 2)) /\
    (y = Seq (Barrier 2) (Barrier 1) \/ y = Seq (arrived_at 2) (Barrier 1)).

Lemma crossed_closed : forall s a e s',
  crossed_state s -> advance zero_input a s = Some (e, s') -> crossed_state s'.
Proof.
  intros s a e s' [x [y [Hthreads [Hx Hy]]]] Hstep. destruct a as [tid|i].
  - apply thread_view in Hstep as [c [o [m' [c' [Hc [Hthread [_ ->]]]]]]].
    rewrite Hthreads in Hc |- *.
    destruct tid as [|[|[|tid]]]; cbn in Hc; inversion Hc; subst.
    + destruct Hx as [-> | ->]; cbn in Hthread; inversion Hthread; subst.
      exists (Seq (arrived_at 1) (Barrier 2)), y.
      split; [reflexivity|]. split; [right; reflexivity|exact Hy].
    + destruct Hy as [-> | ->]; cbn in Hthread; inversion Hthread; subst.
      exists x, (Seq (arrived_at 2) (Barrier 1)).
      split; [reflexivity|]. split; [exact Hx|right; reflexivity].
  - apply release_view in Hstep as [Harrived [Hunknown _]]. exfalso.
    rewrite Hthreads in Harrived, Hunknown.
    destruct (instance_eq_dec i (Site 1 true false, [])) as [->|H1].
    { destruct Hx as [-> | ->], Hy as [-> | ->]; vm_compute in Hunknown; discriminate. }
    destruct (instance_eq_dec i (Site 2 true false, [])) as [->|H2].
    { destruct Hx as [-> | ->], Hy as [-> | ->]; vm_compute in Hunknown; discriminate. }
    apply Harrived. apply select_nil. intros t c Hc.
    destruct t as [|[|[|t]]]; cbn in Hc; inversion Hc; subst.
    + destruct Hx as [-> | ->]; unfold waits_at; cbn [at_collective arrived_at Barrier];
        [reflexivity|]. now apply instance_eqb_false.
    + destruct Hy as [-> | ->]; unfold waits_at; cbn [at_collective arrived_at Barrier];
        [reflexivity|]. now apply instance_eqb_false.
Qed.

Theorem crossed_never_finishes : forall trace last,
  ~ (execution zero_input (initial crossed) trace last /\ finished last).
Proof.
  intros trace last [Hexec Hdone].
  refine (never_finishes crossed_state zero_input _ crossed_closed _ _ _ _ Hexec Hdone).
  - intros s [x [y [Hthreads [Hx _]]]] Hfinished. unfold finished in Hfinished.
    rewrite Hthreads in Hfinished. apply Forall_inv in Hfinished.
    destruct Hx as [-> | ->]; destruct Hfinished; discriminate.
  - exists (Seq (Barrier 1) (Barrier 2)), (Seq (Barrier 2) (Barrier 1)).
    split; [reflexivity|]. split; left; reflexivity.
Qed.

(* One conditional per thread and one collective in its true branch: only
   thread 0 meets at AddZero. *)
Definition partial := Cond (tid_is 0) (AddZero 0) Skip.

Example partial_reference :
  exists last,
  run 100 zero_input [partial; partial; partial] = Some ([Sync (AddSite 0, []) [0]], last) /\
  finished last.
Proof. eexists; split; [vm_compute; reflexivity|finished_codes]. Qed.

Theorem partial_groups : forall trace last,
  execution zero_input (initial [partial; partial; partial]) trace last -> finished last ->
  groups_at (AddSite 0, []) trace = [[0]].
Proof. groups_by_reference 100. Qed.

(* Two AddZero calls in one thread's code, with different labels, are two
   collectives, each met by both threads. *)
Definition two_adds := Seq (AddZero 0) (AddZero 1).

Theorem two_adds_groups : forall trace last,
  execution zero_input (initial [two_adds; two_adds]) trace last -> finished last ->
  groups_at (AddSite 0, []) trace = [[0; 1]] /\
  groups_at (AddSite 1, []) trace = [[0; 1]].
Proof. groups_by_reference 100. Qed.

(* Primitive results and memory ordering. *)

Lemma memory_in_every_execution : forall fuel programs address expected,
  match run fuel zero_input programs with
  | Some (reference_trace, reference_last) =>
      conflict_free reference_trace = true /\
      load zero_input (memory reference_last) address = expected
  | None => False
  end ->
  forall trace last,
  execution zero_input (initial programs) trace last -> finished last ->
  load zero_input (memory last) address = expected.
Proof.
  intros fuel programs address expected H trace last Hexec Hdone.
  destruct (run fuel zero_input programs) as [[reference_trace reference_last]|] eqn:Hrun;
    [|contradiction].
  destruct H as [Hfree Hload].
  destruct (agreement_from_drf _ _ _ _ _ Hrun (conflict_free_drf _ Hfree) _ _ Hexec Hdone)
    as [_ [_ Hmemory]].
  rewrite <- Hmemory. exact Hload.
Qed.

Definition sum_values (values : list (nat * list nat)) (_ : nat) : nat :=
  fold_right (fun p total => hd 0 (snd p) + total) 0 values.

Definition total := variable "total".

(* Each thread adds tid + 1 with a reduction that does not order memory, and
   thread 0 stores the sum it receives. *)
Definition reduce :=
  Prim 0 false false sum_values [plus1 NTid] total
    (Cond (tid_is 0) (Write (NNum 0) (NVar total)) Skip).

Theorem reduce_result : forall trace last,
  execution zero_input (initial [reduce; reduce; reduce]) trace last -> finished last ->
  load zero_input (memory last) 0 = 6.
Proof.
  intros trace last Hexec Hdone.
  refine (memory_in_every_execution 100 _ 0 6 _ trace last Hexec Hdone).
  vm_compute. split; reflexivity.
Qed.

(* Thread 0 writes a cell, both threads meet at a primitive, and thread 1 then
   reads the cell. A primitive that orders memory orders the write before the
   read; one that does not leaves them racing. *)
Definition handoff (sync : bool) :=
  [Seq (Write (NNum 0) (NNum 1)) (Prim 0 sync false (fun _ _ => 0) [] unused Skip);
   Prim 0 sync false (fun _ _ => 0) [] unused (Read (variable "r") (NNum 0) Skip)].

Definition handoff_trace (sync : bool) :=
  [Memory (Observe (av_write 0 0) 1); Sync (Site 0 sync false, []) [0; 1];
   Memory (Observe (av_read 1 0) 1)].

Example handoff_reference : forall sync,
  exists last, run 100 zero_input (handoff sync) = Some (handoff_trace sync, last) /\
  finished last.
Proof. intros []; eexists; split; [vm_compute; reflexivity|finished_codes| |];
  [vm_compute; reflexivity|finished_codes]. Qed.

Lemma sync_handoff_drf : MemDRF (handoff_trace true).
Proof.
  intros i j e f He Hf Hconflict.
  assert (Hi : i < 3).
  { apply (proj1 (nth_error_Some (handoff_trace true) i)). rewrite He. discriminate. }
  assert (Hj : j < 3).
  { apply (proj1 (nth_error_Some (handoff_trace true) j)). rewrite Hf. discriminate. }
  destruct i as [|[|[|i]]], j as [|[|[|j]]]; try lia;
    cbn in He, Hf; try discriminate;
    inversion He; inversion Hf; subst; clear He Hf;
    try solve [inversion Hconflict; cbn in *; congruence].
  - left. apply t_trans with 1; apply t_step; [hb_link 0|hb_link 1].
  - right. apply t_trans with 1; apply t_step; [hb_link 0|hb_link 1].
Qed.

Theorem sync_handoff_reads : forall trace last,
  execution zero_input (initial (handoff true)) trace last -> finished last ->
  read_history 1 trace = [Observe (av_read 1 0) 1].
Proof.
  intros trace last Hexec Hdone.
  destruct (handoff_reference true) as [reference_last [Hrun _]].
  destruct (agreement_from_drf _ _ _ _ _ Hrun sync_handoff_drf _ _ Hexec Hdone)
    as [_ [Hreads _]].
  rewrite <- Hreads. reflexivity.
Qed.

Theorem nosync_handoff_race : ~ MemDRF (handoff_trace false).
Proof.
  intros Hdrf.
  assert (Hconflict : Conflict (av_write 0 0) (av_read 1 0))
    by (apply conflict_l; cbn; [discriminate|reflexivity|reflexivity]).
  assert (Hno : forall y, ~ hb_step (handoff_trace false) 0 y).
  { intros y [Hlt [e [f [t [He [Hf [Het Hft]]]]]]].
    cbn in He. inversion He; subst e. cbn in Het.
    destruct y as [|[|[|[|y]]]]; cbn in Hf; inversion Hf; subst f; cbn in Hft.
    - lia.
    - destruct Hft as [Hsync _]. discriminate.
    - congruence. }
  destruct (Hdrf 0 2 (Observe (av_write 0 0) 1) (Observe (av_read 1 0) 1)
    eq_refl eq_refl Hconflict) as [Hhb|Hhb].
  - apply clos_trans_t1n in Hhb.
    inversion Hhb as [y Hstep|y z Hstep _]; exact (Hno _ Hstep).
  - apply hb_lt in Hhb. lia.
Qed.

(* A primitive with two arguments: each thread supplies tid and tid + 1, and
   every participant receives the sum of the products; thread 0 stores it. *)
Definition dot_values (values : list (nat * list nat)) (_ : nat) : nat :=
  fold_right (fun p total =>
    match snd p with [a; b] => a * b + total | _ => total end) 0 values.

Definition dot :=
  Prim 0 false false dot_values [NTid; plus1 NTid] total
    (Cond (tid_is 0) (Write (NNum 0) (NVar total)) Skip).

Theorem dot_result : forall trace last,
  execution zero_input (initial [dot; dot; dot]) trace last -> finished last ->
  load zero_input (memory last) 0 = 8.
Proof.
  intros trace last Hexec Hdone.
  refine (memory_in_every_execution 100 _ 0 8 _ trace last Hexec Hdone).
  vm_compute. split; reflexivity.
Qed.

(* A primitive that requires the whole warp (req(p) = full), run by thread 0
   alone: the structured partial configuration rejects the kernel. *)
Definition lone_full :=
  Cond (tid_is 0) (Prim 0 true true (fun _ _ => 0) [] unused Skip) Skip.

Theorem lone_full_rejected : forall trace last,
  run 100 zero_input [lone_full; lone_full] = Some (trace, last) ->
  ~ UnambiguousParticipation StructuredPartial [lone_full; lone_full] trace.
Proof.
  intros trace last Hrun Hpart. vm_compute in Hrun. inversion Hrun; subst.
  destruct (Hpart (Site 0 true true, []) [0] (or_introl eq_refl)) as [_ [_ [_ Hfull]]].
  specialize (Hfull eq_refl). vm_compute in Hfull. discriminate.
Qed.

(* Local statements, return and switch. *)

Definition double := variable "double".

(* Each thread computes double := 2 * tid locally and stores it in its own
   cell. *)
Definition doubled := Local double (fun vs => 2 * hd 0 vs) [NTid] (Write NTid (NVar double)).

Theorem doubled_result : forall trace last,
  execution zero_input (initial [doubled; doubled; doubled]) trace last -> finished last ->
  load zero_input (memory last) 2 = 4.
Proof.
  intros trace last Hexec Hdone.
  refine (memory_in_every_execution 100 _ 2 4 _ trace last Hexec Hdone).
  vm_compute. split; reflexivity.
Qed.

(* Thread 1 returns before the barrier, so barrier 1 is met by threads 0 and 2
   in every completed execution. *)
Definition early_return := Seq (Cond (tid_is 1) Return Skip) (Barrier 1).

Theorem early_return_groups : forall trace last,
  execution zero_input (initial [early_return; early_return; early_return]) trace last ->
  finished last ->
  groups_at (BarrierSite 1, []) trace = [[0; 2]].
Proof. groups_by_reference 100. Qed.

(* Each thread picks a barrier by its thread identifier. *)
Definition switched := Switch NTid [(0, Barrier 1); (1, Barrier 2)] (Barrier 3).

Theorem switch_groups : forall trace last,
  execution zero_input (initial [switched; switched; switched]) trace last ->
  finished last ->
  groups_at (BarrierSite 1, []) trace = [[0]] /\
  groups_at (BarrierSite 2, []) trace = [[1]] /\
  groups_at (BarrierSite 3, []) trace = [[2]].
Proof. groups_by_reference 100. Qed.

(* Loops. *)

(* Thread 1 breaks out of the loop from inside a conditional. Thread 0 meets
   no one at barrier 1: thread 1 can no longer reach it. After the loop both
   meet at barrier 2. An unknown set must drop the thread that broke out. *)
Definition break_early :=
  Seq (Loop (Seq (Cond (tid_is 1) Break Skip) (Seq (Barrier 1) Break))) (Barrier 2).

Definition break_trace :=
  [Sync (BarrierSite 1, [0]) [0]; Sync (BarrierSite 2, []) [0; 1]].

Example break_reference :
  exists last, run 200 zero_input [break_early; break_early] = Some (break_trace, last) /\
  finished last.
Proof. eexists; split; [vm_compute; reflexivity|finished_codes]. Qed.

Theorem break_groups : forall trace last,
  execution zero_input (initial [break_early; break_early]) trace last -> finished last ->
  groups_at (BarrierSite 1, [0]) trace = [[0]] /\
  groups_at (BarrierSite 2, []) trace = [[0; 1]].
Proof. groups_by_reference 200. Qed.

(* Thread 1 skips the rest of iteration 0 with Continue. Once it is in
   iteration 1 it can no longer reach barrier 1 of iteration 0, so thread 0
   meets no one there. *)
Definition continue_body :=
  Read i_var counter
    (Cond (NRel NLt (NVar i_var) (NNum 1))
      (Seq (Write counter (plus1 (NVar i_var)))
        (Seq (Cond (tid_is 1) Continue Skip) (Barrier 1)))
      Break).

Definition continue_early := Seq (Loop continue_body) (Barrier 2).

Theorem continue_groups : forall trace last,
  execution zero_input (initial [continue_early; continue_early]) trace last ->
  finished last ->
  groups_at (BarrierSite 1, [0]) trace = [[0]] /\
  groups_at (BarrierSite 2, []) trace = [[0; 1]].
Proof. groups_by_reference 200. Qed.

(* Thread 1 leaves in iteration 0, thread 0 in iteration 1. The collective
   after the loop waits for thread 0, which may still reach it, so both meet
   there in every schedule. *)
Definition exit_body :=
  Seq (Cond (tid_is 1) Break Skip)
    (Read i_var counter
      (Cond (NRel NLt (NVar i_var) (NNum 1)) (Write counter (plus1 (NVar i_var))) Break)).

Definition split_exit := Seq (Loop exit_body) (Barrier 2).

Theorem split_exit_groups : forall trace last,
  execution zero_input (initial [split_exit; split_exit]) trace last -> finished last ->
  groups_at (BarrierSite 2, []) trace = [[0; 1]].
Proof. groups_by_reference 200. Qed.

(* Thread t runs t + 1 iterations with a barrier in each: iteration k of the
   barrier is its own dynamic block, met by the threads still iterating. *)
Definition iterations_body :=
  Read i_var counter
    (Cond (NRel NLe (NVar i_var) NTid)
      (Seq (Write counter (plus1 (NVar i_var))) (Barrier 1))
      Break).

Definition iterations := Loop iterations_body.

Theorem iteration_groups : forall trace last,
  execution zero_input (initial [iterations; iterations; iterations]) trace last ->
  finished last ->
  groups_at (BarrierSite 1, [0]) trace = [[0; 1; 2]] /\
  groups_at (BarrierSite 1, [1]) trace = [[1; 2]] /\
  groups_at (BarrierSite 1, [2]) trace = [[2]].
Proof. groups_by_reference 500. Qed.

(* Nested loops: two outer iterations, each with one inner iteration. A
   barrier in the inner loop is named by both counts, outermost first; the
   barrier after the inner loop by the outer count alone. *)
Definition inner_body :=
  Read j_var inner_counter
    (Cond (NRel NLt (NVar j_var) (NNum 1))
      (Seq (Write inner_counter (plus1 (NVar j_var))) (Barrier 2))
      Break).

Definition outer_body :=
  Read i_var counter
    (Cond (NRel NLt (NVar i_var) (NNum 2))
      (Seq (Write counter (plus1 (NVar i_var)))
        (Seq (Write inner_counter (NNum 0)) (Seq (Loop inner_body) (Barrier 3))))
      Break).

Definition nested_loops := Loop outer_body.

Theorem nested_loop_groups : forall trace last,
  execution zero_input (initial [nested_loops; nested_loops]) trace last ->
  finished last ->
  groups_at (BarrierSite 2, [0; 0]) trace = [[0; 1]] /\
  groups_at (BarrierSite 3, [0]) trace = [[0; 1]] /\
  groups_at (BarrierSite 2, [1; 0]) trace = [[0; 1]] /\
  groups_at (BarrierSite 3, [1]) trace = [[0; 1]].
Proof. groups_by_reference 500. Qed.

(* The reference run rejects a thread whose code contains the same collective
   twice. *)
Example repeated_site_rejected :
  run 100 zero_input [Loop (Seq (Barrier 0) (Seq (Barrier 0) Break))] = None.
Proof. reflexivity. Qed.
