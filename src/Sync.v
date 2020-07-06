Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Access.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | Seq: inst -> inst -> inst
  | Access: access_exp -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.


Fixpoint i_subst x v i :=
  match i with
  | Access a => Access (access_subst x v a)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  | Loop y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2'
  | Skip => Skip
  | Sync => Sync
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  end.


Inductive Unsync : inst -> Prop :=
| unsync_skip:
  Unsync Skip
| unsync_seq:
  forall i j, 
  Unsync i ->
  Unsync j ->
  Unsync (Seq i j)
| unsync_access:
  forall a, 
  Unsync (Access a)
| unsync_for:
  forall v r i,
  Unsync i ->
  Unsync (For v r i)
| unsync_loop:
  forall v r i,
  Unsync i ->
  Unsync (Loop v r i).

Goal Unsync (Seq Skip Skip).
Proof.
simpl.
apply unsync_seq.
- apply unsync_skip.
- apply unsync_skip.
Qed.


Theorem Unsync_skip_seq_l:
forall i,
Unsync i ->
Unsync (Seq i Skip).
Proof.
intros.
apply unsync_seq.
- assumption.
- apply unsync_skip.
Qed.

Theorem Unsync_syncs:
~Unsync Sync.
Proof.
unfold not.
intros N.
inversion N.
Qed.


Inductive In : inst -> inst -> Prop :=
| in_skip:
  In Skip Skip
| in_sync:
  In Sync Sync
| in_access:
  forall a,
  In (Access a) (Access a)
| in_seq_l:
  forall k i j,
  In k i ->
  In k (Seq i j)
| in_seq_r:
  forall k i j,
  In k j ->
  In k (Seq i j)
| in_for:
  forall k v r i,
  In k i ->
  In k (For v r i)
| in_loop:
  forall k v r i,
  In k i ->
  In k (Loop v r i).

Theorem Sync_sync_in:
forall i,
Unsync i -> ~In Sync i.
Proof.
induction i; intros; intros N.
- inversion N.
- inversion H.
- inversion N; subst; clear N.
  * inversion H; subst; clear H.
    apply IHi1 in H3. 
    unfold not in *.
    apply H3.
    assumption.
  * inversion H; subst; clear H.
    apply IHi2 in H2. 
    unfold not in *.
    apply H2.
    assumption.
- inversion N.
- inversion N; subst; clear N.
  inversion H; subst; clear H.
  apply IHi in H1.
  contradiction.
- inversion N; subst; clear N.
  inversion H; subst; clear H.
  apply IHi in H1.
  contradiction.
Qed.


Theorem Sync_sync_in_rev:
forall i,
~In Sync i -> Unsync i.
Proof.
induction i; intros.
- apply unsync_skip.
- unfold not in *. contradict H. apply in_sync.
- apply unsync_seq.
  * apply IHi1.
    intros N.
    contradict H.
    apply in_seq_l.
    assumption.
  * apply IHi2.
    intros N.
    contradict H.
    apply in_seq_r.
    assumption.
- apply unsync_access.
- apply unsync_for.
  apply IHi.
  intros N.
  contradict H.
  apply in_for.
  assumption.
- apply unsync_loop.
  apply IHi.
  intros N.
  contradict H.
  apply in_loop.
  assumption.
Qed.


Import Hist.

Notation history := (list access_val).

Context `{T:Tasks}.


Inductive Run: (inst * history) -> (inst * history) -> Prop :=
| run_sync:
  forall h,
  Run (Sync, h) (Skip, [])
| run_access:
  forall a h v,
  GenAccess TID a TID_COUNT v ->
  Run ((Access a), h) (Skip, (List.concat v ++ h))
| run_seq:
  forall h h' i j k,
  Run (i, h) (j, h') ->
  Run ((Seq i k), h) ((Seq j k), h')
| run_seq_skip:
  forall h i,
  Run ((Seq Skip i), h) (i, h)
| run_for:
  forall r l i x h,
  RStep r l ->
  Run ((For x r i), h) ((Loop x l i), h)
| run_for_loop_nil:
  forall x i h,
  Run ((Loop x [] i), h) (Skip, h)
| run_for_loop_cons:
  forall x n i h l,
  Run ((Loop x (n::l) i), h) ((Seq (i_subst x (NNum n) i) (Loop x l i)), h).


Inductive Multi_Run: (inst * history) -> (inst * history) -> Prop :=
| mrun_refl:
  forall i h,
  Multi_Run (i, h) (i, h)
| mrun_step:
  forall i1 i2 i3 h1 h2 h3,
  Run (i1, h1) (i2, h2) ->
  Multi_Run (i2, h2) (i3, h3) ->
  Multi_Run (i1, h1) (i3, h3).

(*

(* If we define Multi_Run in terms of pairs, then we can use the
   Setoid tactics (see example next). *)
Inductive MRun : (inst * history) -> (inst * history) -> Prop :=
| m_run_def:
  forall i h1 j h2, 
  Multi_Run i h1 j h2 ->
  MRun  (i, h1) (j, h2).

*)

Lemma m_run_refl:
  forall x,
  Multi_Run x x.
Proof.
  intros.
  destruct x.
  apply mrun_refl.
Qed.

Theorem run_imp_mrun:
forall x y,
Run x y ->
Multi_Run x y.
Proof.
intros.
destruct x as (i1,h1).
destruct y as (i2,h2).
apply mrun_step with (i2:=i2) (h2:=h2).
- assumption.
- apply mrun_refl.
Qed.



Lemma m_run_trans:
  forall x y z,
  Multi_Run x y ->
  Multi_Run y z ->
  Multi_Run x z.
Proof.
  intros x y.
  intros z H.
  (* introduce the z back into the assumptions,
     so that induction doesn't capture it *)
  generalize dependent z.
 (* inversion H; subst; clear H. *)
  induction H; intros.
  - assumption.
  - apply IHMulti_Run in H1.
    inversion H1; subst; clear H1.
    + auto using run_imp_mrun.
    + eauto using mrun_step.
Qed.


(** We register MRun's transitivity and reflexivity with Coq's tactics.
    1. Instead of using m_run_refl we can use the tactics 'reflexivity'.
    2. Instead of using m_run_trans we can use the tactics 'transitivity'.
    *)
Global Add Parametric Relation : _ Multi_Run
  reflexivity proved by m_run_refl
  transitivity proved by m_run_trans
  as m_run_setoid.



Theorem uni_skip_one:
forall i1 i2 h1 h2,
Run (i1, h1) (i2, h2) ->
Multi_Run ((Seq Skip i1), h1) (i2, h2).
Proof.
intros.
apply mrun_step with (i2:=i1) (h2:=h1).
- apply run_seq_skip.
- apply mrun_step with (i2:=i2) (h2:=h2).
  * assumption.
  * apply mrun_refl.
Qed.



Theorem mrun_transitivity: 
forall i1 i2 i3 h1 h2 h3,
Run (i1, h1) (i2, h2) ->
Run (i2, h2) (i3, h3) ->
Multi_Run (i1, h1) (i3, h3).
Proof.
intros.
apply mrun_step with (i2:=i2) (h2:=h2).
- assumption.
- apply run_imp_mrun.
  assumption.
Qed.



Theorem unit_skip_l:
  forall i1 h1 x,
  Multi_Run (i1, h1) x ->
  Multi_Run (Seq Skip i1, h1) x.
Proof.
  intros.
  transitivity (i1,h1). (* apply m_run_trans with (y:=). *)
  - apply run_imp_mrun.
    apply run_seq_skip.
  - assumption.
Qed.


(* Run (Seq Sync Skip) h2 Skip h2 ==> h2 = [] *)

Lemma sync_imp_emptyhist:
forall h i h',
Run (Sync, h) (i, h') ->
h' = [].
Proof.
intros.
inversion H.
reflexivity.
Qed.


Inductive Normalised: inst -> (option inst * inst) -> Prop :=
| norm_unsync:
  forall i,
  Unsync i -> 
  Normalised i (None, i)
| norm_sync:
  Normalised Sync (Some Sync, Skip)
| norm_seq_dual:
  forall i i1 i2 j j1 j2,
  Normalised i (Some i1, i2) ->
  Normalised j (Some j1, j2) ->
  Normalised (Seq i j) (Some (Seq i1 (Seq i2 j1)), j2)
| norm_seq_r:
  forall i j j1 j2,
  Unsync i -> 
  Normalised j (Some j1, j2) ->
  Normalised (Seq i j) (Some (Seq i j1), j2)
| norm_seq_l:
  forall i i1 i2 j,
  Unsync j -> 
  Normalised i (Some i1, i2) ->
  Normalised (Seq i j) (Some i1, Seq i2 j)
| norm_for_step: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (For v r i) (Some (Seq i1 (For v r (Seq i2 i1))), i2) (* still needs to replace things here *)
| norm_for_nop: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (For v r i) (None, Skip)
| norm_loop_step: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (Loop v r i) (Some (Seq i1 (Loop v r (Seq i2 i1))), i2) (* still needs to replace things here *)
| norm_loop_nop: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (Loop v r i) (None, Skip)
.

Theorem unsync_normalisable:
  forall i,
  Unsync i ->
  Normalised i (None, i).
Proof.
intros.
apply norm_unsync.
assumption.
Qed.


Theorem none_normalisable_unsync:
  forall i,
  Normalised i (None, i) ->
  Unsync i.
Proof.
intros.
induction i; inversion H; assumption.
Qed.

Theorem some_normalisable_in_sync:
  forall i i1 i2,
  Normalised i (Some i1, i2) ->
  In Sync i.
Proof.
intros i.
induction i; intros; inversion H; subst; auto using in_sync. 
- apply IHi2 in H5. apply IHi1 in H3. 
  auto using in_seq_l.
- apply IHi2 in H5.
  auto using in_seq_r.
- apply IHi1 in H5. 
  auto using in_seq_l.
- apply IHi in H1.
  auto using in_for.
- apply IHi in H1.
  auto using in_loop.
Qed.


Lemma unsync_insync:
forall i,
Unsync i \/ In Sync i.
Proof.
intro.
induction i.
- left.
  apply unsync_skip.
- right.
  apply in_sync.
- destruct IHi1; destruct IHi2.
    + left.
      apply unsync_seq; assumption.
    + right.
      apply in_seq_r; assumption.
    + right.
      apply in_seq_l; assumption.
    + right. 
      apply in_seq_l; assumption.
- left.
  apply unsync_access.
- destruct IHi.
  * left. 
    apply unsync_for; assumption.
  * right.
    apply in_for; assumption.
- destruct IHi.
  * left. 
    apply unsync_loop; assumption.
  * right.
    apply in_loop; assumption.
Qed.


Theorem sync_normalisable:
  forall i,
  In Sync i ->
  exists i1 i2, 
  Normalised i (Some i1, i2).
Proof.
intros i.
induction i.
  - assert (HA: ~In Sync Skip). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
  - intro. 
    exists Sync.
    exists Skip.
    apply norm_sync.
  - intro.
    inversion H; subst; clear H.
    * apply IHi1 in H2. (*i |> i1 i2*)
      assert (EX: Unsync i2 \/ In Sync i2). { apply unsync_insync. }
      destruct EX.
      + (* unsync i2 *)
        inversion H2. inversion H0.
        exists x. exists (Seq x0 i2).
        auto using norm_seq_l.
      + apply IHi2 in H. (* sync i2 *)
        inversion H; clear H. inversion H0; clear H0.
        inversion H2; clear H2. inversion H0; clear H0.
        exists (Seq x1 (Seq x2 x)).
        exists x0.
        auto using norm_seq_dual.
   * apply IHi2 in H2. (*j |> j1 j2*)
     assert (EX: Unsync i1 \/ In Sync i1). { apply unsync_insync. }
     destruct EX; destruct H2 as (x, (y, APH)).
     + exists (Seq i1 x).
       exists y.
       auto using norm_seq_r.
     + apply IHi1 in H.
       destruct H as (x2, (y2, BPH)).
       exists (Seq x2 (Seq y2 x)).
       exists y.
       auto using norm_seq_dual.
  - assert (HA: ~In Sync (Access a)). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
  - intro. 
    inversion H; subst; clear H.
    apply IHi in H2.
    destruct H2 as (x, (y, AH)).
    exists (Seq x (For v r (Seq y x))). (*will need to inst here *)
    exists y.
    auto using norm_for_step.
 - intro. 
    inversion H; subst; clear H.
    apply IHi in H2.
    destruct H2 as (x, (y, AH)).
    exists (Seq x (Loop v l (Seq y x))). (*will need to inst here *)
    exists y.
    auto using norm_loop_step.
Qed.



(* sync_normalisable and unsync_normalisable *)
Theorem allnormalisable_or:
  forall i,
  (exists j1 j2, 
  (Normalised i (Some j1, j2)))
  \/ 
  exists j, 
  (Normalised i (None, j)).
Proof.
intros.
assert (EX: Unsync i \/ In Sync i). { apply unsync_insync. }
destruct EX.
- right.
  exists i.
  auto using unsync_normalisable. 
- left.
  auto using sync_normalisable. 
Qed.

Theorem allnormalisable:
  forall i,
  (exists j1 j2, 
  (Normalised i (j1, j2))).
Proof.
intro.
assert (EX: Unsync i \/ In Sync i). { apply unsync_insync. }
destruct EX.
- exists None. exists i.
  auto using unsync_normalisable. 
- apply sync_normalisable in H.
  eauto.
  destruct H as (i1, (i2, H1)).
  exists (Some i1).
  exists i2.
  assumption.
Qed.


Lemma mrun_sync:
  forall h,
  Multi_Run (Sync, h) (Skip, []).
Proof.
  intros.
  apply run_imp_mrun.
  apply run_sync.
Qed.
(*
Lemma mrun_seq_sync_skip:
  forall h,
  Multi_Run (Seq Sync Skip, h) (Sync, h).
Proof.
  intros.
  apply 
Qed.
*)

Lemma mrun_seq_skip:
  forall i h,
  Multi_Run (Seq Skip i, h) (i, h).
Proof.
  intros.
  apply run_imp_mrun.
  apply run_seq_skip.
Qed.

Lemma run_fun:
  forall x y,
  Run x y ->
  forall z,
  Run x z ->
  y = z.
Proof.
  intros x y H.
  induction H; intros; auto.
  - inversion H; subst; clear H.
    reflexivity.
  - inversion H0; subst; clear H0.
    assert (v0 = v) by eauto using gen_access_fun.
    subst.
    reflexivity.
  - inversion H0; subst; clear H0.
    + apply IHRun in H5.
      inversion H5; subst; clear H5.
      reflexivity.
    + inversion H; subst; clear H.
  - inversion H; subst; clear H.
    + inversion H4.
    + reflexivity.
  - inversion H0; subst; clear H0.
    assert (l0 = l) by eauto using r_step_fun.
    subst.
    reflexivity.
  - inversion H; subst; clear H.
    reflexivity.
  - inversion H; subst; clear H.
    reflexivity.
Qed.




(* If multi-run is performing a step, then we can decompose it. *)
Lemma multi_run_inv_step:
  forall i h1 j h2 i' h1',
  Multi_Run (i, h1) (j, h2) ->
  i <> j ->
  Run (i, h1) (i', h1') ->
  Multi_Run (i', h1') (j, h2).
Proof.
  intros.
  inversion H; subst; clear H.
  + contradiction.
  + assert (R: (i', h1') = (i2, h3)) by eauto using run_fun.
    inversion R; subst; auto.
Qed.

Lemma mrun_seq:
  forall i h j h' k,
  Run (i, h) (j, h') ->
  Multi_Run (Seq i k, h) (Seq j k, h').
Proof.
  intros.
  auto using run_imp_mrun, run_seq.
Qed.

Fixpoint Merge  (i: option inst) (j: inst) :=
match i with
| None => j
| (Some n) => Seq n j
end.

Lemma unsync_src_norm:
  forall i h x,
  Unsync i ->
  Run (i, h) x ->
  exists (i1 : option inst) (i2 : inst),
    Normalised i (i1, i2) /\ Multi_Run (Merge i1 i2, h) x.
Proof.
  intros.
  inversion H; subst.
  * exists None. exists Skip.
    inversion H0; auto using norm_unsync.
    (*
    split; simpl.
    + auto using norm_unsync. 
    + inversion H0.*)
  * exists None. exists (Seq i0 j).
    auto using norm_unsync, run_imp_mrun.
    (*
    split; simpl.
    + auto using norm_unsync.
    + apply run_imp_mrun in H0.
      assumption.*)
  * exists None. exists (Access a).
    auto using norm_unsync, run_imp_mrun.
    (*
    split; simpl.
    + auto using norm_unsync.
    + apply run_imp_mrun in H0. assumption.*)
  * exists None. exists (For v r i0).
    auto using norm_unsync, run_imp_mrun.
    (*
    split; simpl.
    + auto using norm_unsync.
    + apply run_imp_mrun in H0. assumption.
    *)
  * exists None. exists (Loop v r i0).
    split; simpl.
    + auto using norm_unsync.
    + apply run_imp_mrun in H0. assumption.
Qed.

Lemma in_sync_to_not_unsync:
  forall i,
  In Sync i ->
  ~ Unsync i.
Proof.
  induction i; intros; intros N; inversion H; subst; clear H;
    inversion N; subst; clear N.
  - apply IHi1 in H2; contradiction.
  - apply IHi2 in H2; contradiction.
  - apply IHi in H2; contradiction.
  - apply IHi in H2; contradiction.
Qed.




(* Normalisation is NOT a function in general! *)
Lemma norm_fun_unsync:
  forall i i2,
  Unsync i ->
  Normalised i (None, i2) ->
  forall j2,
  Normalised i (None, j2)  ->
  (i2 = j2).
Proof.
intros i i2 HUS HN. 
intros j2 HM.
induction i; inversion HN; subst; inversion HM; auto; subst.
- inversion HUS. 
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
Qed.



(*
Multi_Run (Seq (Seq Sync (Seq Skip j0)) j3, hi) (Seq Skip j, [])

Seq (Seq Skip j0) j3 -->* Seq Skip j ==> Seq j0 j3 =~= j
*)


(*
Inductive IEquivOne : inst -> inst -> Prop :=
| equiv_unit_lii:
  forall i j,
  IEquivOne i j -> 
  IEquivOne (Seq Skip i) j
| equiv_unit_lsi:
  forall i j, 
  IEquivOne i j -> 
  IEquivOne (Seq i Skip) j
| equiv_unit_ris:
  forall i j, 
  IEquivOne i j -> 
  IEquivOne i (Seq Skip j)
| equiv_unit_rii:
  forall i j, 
  IEquivOne i j -> 
  IEquivOne i (Seq j Skip)
| equiv_assoc_l:
  forall x y z x1 y1 z1,
  IEquivOne x x1 -> 
  IEquivOne y y1 -> 
  IEquivOne z z1 -> 
  IEquivOne (Seq x (Seq y z)) (Seq (Seq x1 y1) z1)
| equiv_assoc_r:
  forall x y z x1 y1 z1,
  IEquivOne x x1 -> 
  IEquivOne y y1 -> 
  IEquivOne z z1 -> 
  IEquivOne (Seq (Seq x y) z) (Seq x1 (Seq y1 z1)).
*)

Inductive IEquivOne : inst -> inst -> Prop :=
| equiv_unit_r:
  forall i,
  IEquivOne (Seq Skip i) i
| equiv_unit_l:
  forall i, 
  IEquivOne (Seq i Skip) i
| equiv_assoc:
  forall x y z,
  IEquivOne (Seq x (Seq y z)) (Seq (Seq x y) z).


(* Definition IEquivStar := clos_refl_sym_trans _ IEquivOne. *)

Notation iequivstar := (clos_refl_sym_trans_n1 _ IEquivOne).

Global Add Parametric Relation : _ iequivstar
    reflexivity proved by (rstn1_refl inst IEquivOne)                                   
    symmetry proved by (clos_rstn1_sym inst IEquivOne)
    transitivity proved by (clos_rstn1_trans inst IEquivOne)
  as equivstar_setoid.


Goal
  forall x,
    iequivstar x x.
Proof.
  intros.
  reflexivity.
Qed.


Goal
  forall x y z,
    iequivstar x y ->
    iequivstar y z ->
    iequivstar x z.
Proof.
  intros.
  transitivity y; assumption.
Qed.

Goal
  forall x y,
    iequivstar x y ->
    iequivstar y x.
Proof.
  intros.
  symmetry in H.
  assumption.
Qed.


(* Inductive INF : inst -> Prop := *)
(* | inf_seq: *)

(* define a "cleanup function" ? 0;P -> P etc *)
(* define a normalise sequencing function? (P;Q);R -> P;(Q;R) *) 
(*
Fixpoint igc (i :inst) : inst :=
  match i with
  | Seq Skip y => igc y
  | Access a => Access a
  | For e r y =>  For e r (igc y)
  | Loop e r y => Loop e r (igc y)
  | Skip => Skip
  | Sync => Sync
  | Seq x y => (Seq (igc x) (igc y))
  end.

Fixpoint ihnf (i :inst) : inst :=
  match i with
  | Seq (Seq x y) z => Seq (ihnf x) (Seq (ihnf y) (ihnf z))
  | Seq x y => Seq (ihnf x) (ihnf y)
  | Skip => Skip
  | Sync => Sync
  | Access a => Access a
  | For e r y => For e r (ihnf y)
  | Loop e r y => Loop e r (ihnf y)
  end.


Definition eqhead (i :inst) : inst := ihnf (igc i).
  
Lemma eqhead_bard:
  forall i i' j h h',
    eqhead i = eqhead j ->
    Run (i, h) (i',h') ->
    exists j',
      Run (j, h) (j',h').
Proof.
  intros.
  induction i.
  - inversion H.

    *)

Lemma sync_neq_skip_one:
  ~IEquivOne Sync Skip.
Proof.
  unfold not in *.
  intros.
  inversion H.
Qed.


       
Lemma Sync_in_eq_one_l:
  forall x y,
    IEquivOne y x ->
    In Sync x ->
    In Sync y.
Proof.
  intros x y H H0.
  induction H.
  - inversion H0; subst; apply in_seq_r; assumption.
  - apply in_seq_l. assumption.
  - inversion H0; subst.
    + inversion H2; subst.
      * apply in_seq_l. assumption.
      * apply in_seq_r. apply in_seq_l. assumption.
    + apply in_seq_r. apply in_seq_r. assumption.
Qed.
    
   
Lemma Sync_in_eq_one:
  forall x y,
    IEquivOne x y ->
    In Sync x ->
    In Sync y.
Proof.
  intros x y H H0.
  induction H.
  - inversion H0; subst.
    + inversion H2.
    + assumption.
  - inversion H0; subst.
    + assumption.
    + inversion H2.
  - inversion H0; subst.
    + apply in_seq_l.
      apply in_seq_l.
      assumption.
    + inversion H2; subst.
      * apply in_seq_l.
        apply in_seq_r.
        assumption.
      * apply in_seq_r.
        assumption.
Qed.

Lemma Access_in_eq_one:
  forall x y a,
    IEquivOne x y ->
    In (Access a) x ->
    In (Access a) y.
Proof.
  intros x y a H H0.
  induction H.
  - inversion H0; subst.
    + inversion H2.
    + assumption.
  - inversion H0; subst.
    + assumption.
    + inversion H2.
  - inversion H0; subst.
    + apply in_seq_l.
      apply in_seq_l.
      assumption.
    + inversion H2; subst.
      * apply in_seq_l.
        apply in_seq_r.
        assumption.
      * apply in_seq_r.
        assumption.
Qed.


       
Lemma Access_in_eq_one_l:
  forall x y a,
    IEquivOne y x ->
    In (Access a) x ->
    In (Access a) y.
Proof.
  intros x y a H H0.
  induction H.
  - inversion H0; subst; apply in_seq_r; assumption.
  - apply in_seq_l. assumption.
  - inversion H0; subst.
    + inversion H2; subst.
      * apply in_seq_l. assumption.
      * apply in_seq_r. apply in_seq_l. assumption.
    + apply in_seq_r. apply in_seq_r. assumption.
Qed.


Lemma Sync_in_iequivstar:
  forall x y,
    iequivstar x y ->
    In Sync x ->
    In Sync y.
Proof.
  intros x y H Hx. 
  induction H; intros.
  - inversion Hx; subst; assumption.
  - destruct H.
    * apply Sync_in_eq_one in H; assumption.
    * apply Sync_in_eq_one_l in H; assumption.
Qed.
                 

Theorem equiv_mrun:
  forall x x' y h h',
    iequivstar x y ->
    Run (x, h) (x', h') ->
    exists y', 
      (Multi_Run (y, h) (y', h') /\ iequivstar y y').
Proof.
  intros x x' y h h' HE HR.
  cofix H.
  


Lemma equiv_refliv:
forall x,
equivstar x x.
Proof.
intros.
induction x; auto using equiv_refl.
Qed.







Lemma equiv_simm:
forall x y,
IEquivOne x y ->
IEquivOne y x.
Proof.
intros.
Admitted.



Lemma equiv_transi:
forall x y z,
IEquivOne x y ->
IEquivOne y z ->
IEquivOne x z.
Proof.
intros.
generalize dependent z. 
induction H; intros.
- apply IHIEquivOne2 in H1. apply IHIEquivOne1. assumption. 
- assumption.
- apply IHIEquivOne in H0. apply equiv_unit_lii. assumption.
- apply IHIEquivOne in H0. apply equiv_unit_lsi. assumption.
- apply IHIEquivOne. apply equiv_trans with (j:=Seq Skip j).
  + apply equiv_unit_ris. apply equiv_refl.
  + assumption.
- apply IHIEquivOne. apply equiv_trans with (j:=Seq j Skip).
  + apply equiv_unit_rii. apply equiv_refl.
  + assumption.
- apply equiv_trans with (j:=Seq x1 (Seq y1 z1)).
  + inversion H2; subst.
    * 
  + apply equiv_assoc_l; auto using equiv_refl.
  + 
  

induction H; intros.
- assumption.
- apply IHIEquivOne in H0. auto using equiv_unit_lii.
- apply IHIEquivOne in H0. auto using equiv_unit_lii, equiv_unit_lsi, equiv_unit_ris, equiv_unit_rii.
- inversion H0; subst; clear H0.
  + apply IHIEquivOne. admit.
  + apply IHIEquivOne. assumption.
  + apply IHIEquivOne. assumption.
  + apply IHIEquivOne. admit.
  + apply IHIEquivOne. admit.
  + 
  
  * apply equiv_unit_ris. apply equiv_refliv.
  * assumption.
  * assumption.
  * assert (EQ: forall x,  IEquivOne (Seq Skip j) x -> IEquivOne j x). {
    intros x y HSE. 
    inversion HSE; subst.
    + apply equiv_unit_ris. apply equiv_refliv.
    + assumption.
    + assumption.
    + 
   }
    apply equiv_unit_ris in H1.
    rewrite -> EQ.
    apply equiv_unit_ris.  
    inversion H1; subst.
    + apply equiv_refliv.
    + apply  equiv_unit_lsi in H2.
    + apply equiv_unit_ris.  apply equiv_refliv.
    + assumption.
    + assumption.
    + apply equiv_unit_ris.
     
      assert (EQ: IEquivOne (Seq Skip j) j). { 
    assert (IHIEquivOne:= IHIEquivOne j0). 
    apply IHIEquivOne.

 auto using equiv_unit_lii, equiv_unit_lsi, equiv_unit_ris, equiv_unit_rii, equiv_refliv.
  
 * apply equiv_unit_ris. apply equiv_refliv.
  * 

auto using equiv_unit_lii, equiv_unit_lsi, equiv_unit_ris, equiv_unit_rii.


destruct x; auto using equiv_refl.
- destruct y.
  * 
  inversion H0; subst; auto using equiv_refl.
- 

Lemma sync_src_norm_seq:
forall i j i1 i2 j0 j3 j4 h' hi,
Normalised i (Some i1, i2) -> 
Normalised j (Some j0, j3) -> 
Run (Seq i j, hi) (Seq j4 j, h') -> 
Multi_Run (Seq (Seq i1 (Seq i2 j0)) j3, hi) (Seq j4 j, h').
Proof.
intros.
assert (Sij: In Sync i /\ In Sync j).  {
  apply some_normalisable_in_sync in H0.
  apply some_normalisable_in_sync in H. auto. }
destruct Sij as (Si, Sj).
induction i; inversion Si; 
inversion H; subst;
inversion H1; subst. inversion H3; subst.
- apply mrun_step with (i2:=Seq (Seq Skip (Seq Skip j0)) j3) (h2:=[]). 
  + eapply run_seq.
    eapply run_seq.
    eapply run_sync.
  + apply mrun_step with (i2:=Seq (Seq Skip j0) j3) (h2:=[]). 
    * apply run_seq. apply run_seq_skip.
    * apply mrun_step with (i2:=Seq j0 j3) (h2:=[]). 
      -- apply run_seq. apply run_seq_skip.
      -- apply mrun_step.
         ++ (* CONTINUE HERE *)
    

 
Lemma sync_src_norm:
forall i hi x,
Run (i, hi) x ->
In Sync i ->
exists i1 i2,
Normalised i (i1, i2) /\
Multi_Run (Merge i1 i2, hi) x.
Proof.
intro i.
assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
  destruct EX as (j1, (j2, NH)).
induction NH; subst; intros.
- apply in_sync_to_not_unsync in H1.
  contradiction.
- exists (Some Sync). exists Skip.
  split; simpl.
  * apply norm_sync.
  * destruct x as (i3,h3).
    assert (Hx: i3=Skip /\ h3=[]). { inversion H. auto. }
    destruct Hx as (Hi, Hh). subst.
    apply mrun_step with (i2:=Seq Skip Skip) (h2:=[]).
    + apply run_seq. assumption.
    + apply mrun_step with (i2:=Skip) (h2:=[]).
      ++ apply run_seq_skip.
      ++ apply mrun_refl.
- exists (Some (Seq i1 (Seq i2 j0))).
  exists j3.
  inversion H0; subst; clear H0. 
  * inversion H; subst.
    + apply IHNH1 in H5.
      -- destruct H5 as (i3, (i4, (Hn, Hm))).
          split.
         ++ admit.
         ++ apply mrun_step with (i2:=Seq (Seq ?Goal10 (Seq i2 j0)) j3) (h2:=h2) ; simpl. (* (Seq (Seq ?Goal10 (Seq i2 j0)) j3, ?h2)*)
            ** eapply run_seq. apply run_seq. admit.            ** 
                  
      -- assert (EQS:
      -- assumption.
    + 
    inversion H; subst.
    * assert (Hx := H5).
      apply IHNH1 in H5; auto.
      destruct H5 as (i3, (i4, (Hn, Hm))).
      split. 
      + apply norm_seq_dual; assumption.
      + apply IHNH1 in Hx; simpl.
        ++ inversion H; subst; clear H. 
           ** apply IHNH1 in H1.
              -- 
apply mrun_step with (i2:=Seq j4 j3) (h2:=h').
           ** destruct Hx as (i1', (i2', Hx')).
           assert (EQS: i1'=i3). { }
        ++ assumption.
        

{
        
      }
  assert (~ Unsync i). {
    intros N.
    Search (~ Unsync _ ).
    contradict H0.
  }
  split. 
    * apply norm_seq_dual; assumption.
    * simpl.
      destruct x as (xi, xh).
      inversion H; subst.
      + apply IHNH1 in H1.
        destruct H1 as (x1, (x2, RIH)).
        destruct RIH as (RIHN, RIHS).
Qed.
Theorem src_norm:
forall i hi x,
Run (i, hi) x ->
exists i1 i2,
Normalised i (i1, i2) /\
Multi_Run (Merge i1 i2, hi) x.
Proof.
intro i.
assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
  destruct EX as (j1, (j2, NH)).
induction NH; subst; intros.
- auto using unsync_src_norm.
- exists (Some Sync). exists Skip.
  split; simpl.
  * apply norm_sync.
  * destruct x as (i3,h3).
    assert (i3=Skip /\ h3=[]). { inversion H. auto. }
    destruct H0 as (Hi, Hh). subst.
    apply mrun_step with (i2:=Seq Skip Skip) (h2:=[]).
    + apply run_seq. assumption.
    + apply mrun_step with (i2:=Skip) (h2:=[]).
      ++ apply run_seq_skip.
      ++ apply mrun_refl.
- exists (Some (Seq i1 (Seq i2 j0))).
  exists j3.
  split. 
    * apply norm_seq_dual; assumption.
    * simpl.
      destruct x as (xi, xh).
      inversion H; subst.
      + apply IHNH1 in H1.
        destruct H1 as (x1, (x2, RIH)).
        destruct RIH as (RIHN, RIHS).
        
      apply mrun_step with (i2:=(Seq (Seq xi (Seq i2 j0)) j3)) (h2:= xh).
      + 
induction H; subst; inversion NH; subst.
- exists None. exists j2. split.
  * assumption.
  * admit.
- exists (Some Sync). exists Skip. split.
  * assumption.
  * 
  
      

  
  
- admit. 
- 
generalize dependent x.
intros.

intros.
assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
destruct EX as (j1, (j2, NH)).
eexists.
eexists.
split.
- eassumption.
- inversion H; subst; clear H; inversion NH; subst; simpl.
  * inversion H1.
  * transitivity (Seq Skip Skip, @nil access_val). 
    + apply mrun_seq.
      apply run_sync.
    + apply mrun_step with (i2:= Skip) (h2:=[]).
      ++ apply run_seq_skip.
      ++ apply mrun_refl.
  * transitivity (Skip, List.concat  v++ hi).
    + apply mrun_step with (i2:=Skip) (h2:=List.concat  v++ hi).
       ++ apply run_access. 
          assumption.
       ++ apply mrun_refl.
    + apply mrun_refl.
  * apply mrun_step with (i2:=Seq j k) (h2:=h').
    + auto using run_seq.
    + apply mrun_refl.
  * apply mrun_step with (i2:= Seq j j2) (h2:=h').
    + apply run_seq.
      
  * inversion H2.
(* JL TO CONTINUE HERE *)
        apply run_access.
apply mrun_step with (i2:=Seq Skip Skip) (h2:=[]).
    + eapply run_seq.
      apply run_sync.
    + apply mrun_seq.
    + 
    + 
- assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
  destruct EX as (j1, (j2, NH)).
 

Theorem src_norm:
forall i x hi,
Run (i, hi) x ->
exists i1 i2,
Normalised i (Some i1, i2) /\
Multi_Run (Seq i1 i2, hi) x.
Proof.
intros i hi x H.
remember (i, x) as a.
generalize dependent Heqa.
induction H; subst; intros; inversion Heqa; subst; clear Heqa.
- eexists.
  eexists.
  split. {
    apply norm_sync.
  }
  transitivity (Seq Skip Skip, @nil access_val).
  + auto using mrun_seq, run_sync.
  + apply mrun_seq_skip.
- 
(* The conclusion is not strong enough, we need to change it to
   Normalized i (o, i2) /\ MultiRun (merge o i2, hi) x
   where
     merge None i = i
     merge (Some i) j = Seq i j 
   *)

  
- assert (CA: forall z1 z2, ~Normalised Skip (Some z1, z2)). {

- 
induction i.
- assert (Unsync Skip).
  * apply unsync_skip.
  * apply norm_unsync.



(*
Theorem seq_mrun:
  forall i1 i2 i3 h1 h2 h3,
  Run i1 h1 i2 h2 ->
  Run i2 h2 i3 h3 ->
  MRun (Seq i1 i3, h1) (i3, h3).
Proof.
intros.
apply m_run_def.
apply mrun_step with (i2:=i3) (h2:=h3).
- apply run_seq.

generalize dependent i3.
generalize dependent h3.
inversion H; subst.
- intros.
  apply m_run_def.
  eapply mrun_step.
  * 
inversion H0; subst; clear H0.
induction H2.
  - apply m_run_def.
    eapply mrun_step.
      * 
  - *)

(*
Theorem run_seq_kip_r:
  forall i1 h1,
  Multi_Run (Seq i1 Skip, h1) (i1, h1).
Proof.
intros.
apply mrun_step with (i2:=i1) (h2:=h1).
- 
- apply mrun_refl.
*)

(*

Theorem unit_skip_r:
  forall i1 h1 h2,
  Multi_Run (i1, h1) (Skip, h2) ->
  Multi_Run (Seq i1 Skip, h1) (Skip, h2).
Proof.
intros.
induction i1; intros; apply mrun_step with (i2:=Skip) (h2:=h1).
  * apply run_seq_skip.
  * assumption.
  * 
- 
inversion H; subst; clear H.
- apply mrun_step with (i2:=Skip) (h2:=h2).
  * apply run_seq_skip.
  * apply mrun_refl.
- apply mrun_step with (i2:=Skip) (h2:=h2).
  * 
  * apply mrun_refl.

induction i1.
- inversion H1; subst.
  * apply m_run_def.
    apply mrun_step with (i2:=Skip) (h2:=h2).
      + apply run_seq_skip.
      + assumption.
  * inversion H.
- admit.
- admit.
- apply m_run_def.
  apply mrun_step with (i2:=Skip) (h2:=h2).  * destruct H1.
    + admit.
    + apply run_seq in H.
inversion H1; subst.
  * apply m_run_def.
    eapply mrun_step.
    + 
     
       
    + apply mrun_refl.

    inversion H3.
    apply mrun_step with (i2:=Skip) (h2:=h2).
      + apply run_seq.
      + assumption.
    

apply m_run_def.
induction i1.
- inversion H3; subst.
  * apply run_imp_mrun.
    apply run_seq_skip.
  * inversion H.
- 
  


Theorem unit_skip:
forall i1 i2 h1 h2,
Multi_Run i1 h1 i2 h2 ->
Multi_Run (Seq Skip i1) h1 i2 h2.
Proof.
intros.

*)

