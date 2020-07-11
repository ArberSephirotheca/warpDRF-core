Require Import Coq.Lists.List.
(* Require Import Coq.Strings.String. *)
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
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.
Require Hist.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | Seq: inst -> inst -> inst
  | Access: cond_access -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.


Fixpoint i_subst x v i :=
  match i with
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  | Access a => Access (cond_access_subst x v a)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  | Loop y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2'
  | Skip => Skip
  | Sync => Sync
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
      In k (Loop v r i)
| in_refl:
    forall x,
      In x x.

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


Lemma seq_sync_imp_emptyhist:
  forall z hi i2 h2,
    Run (Seq Sync z, hi) (i2, h2) ->
    (i2=Seq Skip z) /\ (h2=[]).
Proof.
  intros.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  auto.
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
  - assert (HA: ~In Sync (Access c)). 
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

Lemma mrun_mrun_seq:
  forall x y,
    Multi_Run x y ->
    forall i j h h',
      x = (i,h) ->
      y = (j,h') ->
      forall k,
      Multi_Run (Seq i k, h) (Seq j k, h').
Proof.
  intros x y HR.
  induction HR.
  - intros. inversion H; inversion H0; subst; clear H H0.
    reflexivity.
  - intros. inversion H1; inversion H0; subst; clear H1 H0.
    assert (IHHR:= IHHR i2 j h2 h' eq_refl eq_refl k).
    transitivity (Seq i2 k, h2).
    * apply mrun_step with (i2:= Seq i2 k) (h2:=h2).
    + apply run_seq. auto.
    + reflexivity.
      * assumption.
Qed.


Lemma mrun_mrun_seq_seq:
  forall x y,
    Multi_Run x y ->
    forall i j h h',
      x = (i,h) ->
      y = (j,h') ->
      forall k z,
      Multi_Run (Seq (Seq i k) z, h) (Seq (Seq j k) z, h').
Proof.
  intros x y HR.
  induction HR.
  - intros. inversion H; inversion H0; subst; clear H H0.
    reflexivity.
  - intros. inversion H1; inversion H0; subst; clear H1 H0.
    assert (IHHR:= IHHR i2 j h2 h' eq_refl eq_refl k z).
    transitivity (Seq (Seq i2 k) z, h2).
    * apply mrun_step with (i2:=Seq (Seq i2 k) z) (h2:=h2).
    + apply run_seq. apply run_seq. auto.
    + reflexivity.
      * assumption.
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
    forall i j,
      IEquivOne i j ->
      IEquivOne (Seq Skip i) j
| equiv_unit_l:
    forall i j,
      IEquivOne i j ->
      IEquivOne (Seq i Skip) j
| equiv_assoc:
    forall x y z x' y' z',
      IEquivOne x x' ->
      IEquivOne y y' ->
      IEquivOne z z' ->
      IEquivOne (Seq x (Seq y z)) (Seq (Seq x' y') z')
| equiv_eq:
    forall x,
      IEquivOne x x
| equiv_seq:
    forall x y x' y',
      IEquivOne x x' ->
      IEquivOne y y' ->
      IEquivOne (Seq x y) (Seq x' y')
| equiv_for:
    forall x y r l,
      IEquivOne x y ->
      IEquivOne (For l r x) (For l r y)
| equiv_loop:
    forall x y l r,
      IEquivOne x y ->
      IEquivOne (Loop l r x) (Loop l r y).
                

(* Definition IEquivStar := clos_refl_sym_trans _ IEquivOne. *)

Notation iequivstar := (clos_refl_sym_trans_n1 _ IEquivOne).

Global Add Parametric Relation : _ iequivstar
    reflexivity proved by (rstn1_refl inst IEquivOne)                                   
    symmetry proved by (clos_rstn1_sym inst IEquivOne)
    transitivity proved by (clos_rstn1_trans inst IEquivOne)
  as iequivstar_setoid.


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

(*
       
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

*)

Lemma run_seq_eq:
  forall y h x' h',
    Run (Seq Skip y, h) (x', h') ->
    (y=x' /\ h=h').
Proof.
  intros.
  inversion H; subst.
  - inversion H1.
  - auto.
Qed.


Lemma equiv_subst:
  forall x y ,
    IEquivOne x y ->
    forall l n,
    IEquivOne (i_subst l n x) (i_subst l n y).
Proof.
  intros x y HE.
  induction HE; intros; simpl.
  - apply equiv_unit_r. auto.
  - apply equiv_unit_l. auto.
  - apply equiv_assoc; auto.
  - apply equiv_eq.
  - apply equiv_seq; auto.
  - apply equiv_for.
    destruct (Set_VAR.MF.eq_dec _ _).
    * subst. assumption.
    * auto.
  - apply equiv_loop.
    destruct (Set_VAR.MF.eq_dec _ _).
    * subst. assumption.
    * auto.
Qed.


Theorem equiv_one_mrun_l:
  forall x y,
    IEquivOne x y ->
    forall x' h h',
      Run (x, h) (x', h') ->
      exists y', 
        (Multi_Run (y, h) (y', h') /\ (IEquivOne x' y' \/ x'=y')). 
Proof.
  intros x y HE.
  induction HE.
  - intros x' h h' HR.
    inversion HR; subst; clear HR.
    * inversion H0.
    * exists j. split.
    + reflexivity.
    + left. assumption.
  - intros x' h h' HR.
    inversion HR; subst; clear HR.
    * assert (IHHE := IHHE j0 h h').
      apply IHHE in H0.
      destruct H0 as (yhat, (H0r,H0e)).
      exists yhat.
      split.
    + assumption.
    + destruct H0e.
      ++ left. apply equiv_unit_l.  assumption.
      ++ subst. left. apply equiv_unit_l. apply equiv_eq.
      * inversion HE; subst.
        exists Skip. split.
        ** reflexivity.
        ** auto.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    * apply IHHE1 in H0.
      destruct H0 as (yhat, (H0R, H0E)).
      exists (Seq (Seq yhat y') z'). split.
      ** apply mrun_mrun_seq_seq with (x:=(x', h)) (y:=(yhat, h')).
      ++ assumption.
      ++ reflexivity.
      ++ reflexivity.
         ** left. apply equiv_assoc.
            +++ destruct H0E.
                *** assumption.
                *** subst. apply equiv_eq.
            +++ assumption.
            +++ assumption.
    * inversion HE1; subst; clear HE1.
    + exists (Seq y' z'). split.
      ++ apply run_imp_mrun. apply run_seq. apply run_seq_skip.
      ++ left. auto using equiv_seq.
  -  intros x0' h h' HR.
     exists x0'.
     split.
     + apply run_imp_mrun. assumption.
     + left. apply equiv_eq.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    + apply IHHE1 in H0.
      destruct H0 as (yhat, (H0R,H0E)).
      exists (Seq yhat y'). split.
      { eapply mrun_mrun_seq. eauto.
        * reflexivity.
        * reflexivity.
      }
      destruct H0E as [WEQ | SEQ].
      * left. apply equiv_seq; assumption.
      * subst. left. apply equiv_seq.
        ** apply equiv_eq.
        ** assumption.
    + inversion HE1; subst; clear HE1.
      exists y'. split. {
        apply run_imp_mrun. apply run_seq_skip.
      }
      left. assumption.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    exists (Loop l l0 y).
    split. {
      apply run_imp_mrun. apply run_for. assumption.
    }
    left. apply equiv_loop. assumption.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    * exists Skip. split. {
        apply run_imp_mrun. apply run_for_loop_nil.
      }
      right. reflexivity.
    * exists (Seq (i_subst l (NNum n) y) (Loop l l0 y)).
      split. {
        apply run_imp_mrun. apply run_for_loop_cons.
      }
      left. apply equiv_seq.
    + apply equiv_subst. assumption.
    + apply equiv_loop. assumption.
Qed.
(*



Lemma mrun_seq_skip_h:
  forall x h,
    Multi_Run (Seq Skip x, h) (x, h).
Proof.
  intros.
  apply mrun_step with (i2:=x) (h2:=h).
  - apply run_seq_skip.
  - reflexivity.
Qed.


Lemma run_seq_skip_h_eq:
  forall x h h',
    Run (Seq Skip x, h) (x, h') ->
    h = h'.
Proof.
  intros.
  inversion H; subst.
  - contradict H4. apply seq_skip_x_not_x.
  - reflexivity.
Qed.


Lemma mrun_seq_skip_h_eq:
  forall x h h',
    Multi_Run (Seq Skip x, h) (x, h') ->
    h = h'.
Proof.
  intros.
  inversion H; subst.
  - contradict H3.  apply seq_skip_x_not_x.
  - apply run_seq_skip in H3.
Qed.
*)
(*
Multi_Run (Seq x1 z, h) (z, h)
  ============================
  Multi_Run (Seq (Seq x1 Skip) z, h) (z, h)
*)


Lemma seq_skip_x_not_x:
  forall x y,
    Seq y x <> x.
Proof.
  intros.
  induction x; unfold not in *; intros; inversion H; subst.
  - contradiction.
Qed.

Lemma seq_skip_x_not_x_rev:
  forall x y,
   x <> Seq y x.
Proof.
  intros.
  induction x; unfold not in *; intros; inversion H; subst.
  - contradiction.
Qed.

(* i0 = Seq Skip (Seq Skip i0) *)

Lemma for_not_y:
  forall v r y,
    For v r y <> y.
Proof.
  intros.
  induction y; intro N; inversion N; subst.
  contradiction.
Qed.
  
Lemma y_in_for_y:
  forall v r y,
    In y (For v r y).
Proof.
  intros.
  apply in_for.
  apply in_refl.
Qed.




Lemma in_transitive:
  forall y z,
    In y z->
    forall x,
      In x y ->
      In x z.
Proof.
  intros y z .
  intros H.
  induction H; intros.
  - assumption.
  - assumption.
  - assumption.
  - assert (IHIn:= IHIn x H0).
    apply in_seq_l.
    assumption.
  - assert (IHIn:= IHIn x H0).
    apply in_seq_r.
    assumption.
  - assert (IHIn:= IHIn x H0).
    apply in_for.
    assumption.
  - assert (IHIn:= IHIn x H0).
    apply in_loop.
    assumption.
  - assumption.
Qed.

Lemma in_trans:
  forall x y z,
    In x y ->
    In y z ->
    In x z.
Proof.
  intros.
  apply in_transitive with (z:=z) in H.
  + assumption.
  + assumption.
Qed.
  

Global Add Parametric Relation : _ In
  transitivity proved by in_trans
  as iin_setoid.

Fixpoint size (i: inst) :=
  match i with
  | Skip => 0
  | Sync | Access _ => 1
  | Seq x y => S (size x + size y)
  | For _ _ x => S (size x)
  | Loop _ l x => S(size x * (length l))
  end.

Fixpoint forsize (i: inst) :=
  match i with
  | Skip | Sync | Access _ => 0
  | Seq x y => forsize x + forsize y
  | For _ _ x => S (forsize x)
  | Loop _ _ x => forsize x
  end.

Fixpoint loopsize (i: inst) :=
  match i with
  | Skip | Sync | Access _ => 0
  | Seq x y => loopsize x + loopsize y
  | For _ _ x => loopsize x
  | Loop _ l x => 2 * (length l) * S (loopsize x)
  end.

(* 
   for x -> loop x  ----> number of loops goes up, number of fors goes
   down (ast stays the same)
   (F, L, A) -> (F-1, L+k, A)

   loop x -> x ; loop x --> ast + number of fors goes up --> but
   #loops goes down
   # Should i not count stuff in Loops ?
   (F, L, A) -> (F, L-1, A-1)


   loop (for x) -> for x ; loop (for x)
   (F, L, A) -> (F+k, L-1; A-1)

Skip; x -> (F,L,A-1)

*) 

Definition ige i j :=
  (forsize i > forsize j)
  \/
  (
    (forsize i <= forsize j)
    /\
    (loopsize i > loopsize j)
  )
  \/
  (
    (forsize i <= forsize j)
    /\
    (loopsize i <= loopsize j)
    /\
    (size i > size j)        
  ).



Import Omega.


    
Lemma size_ge:
  forall i,
  size i >= 0.
Proof.
  induction i; simpl; intros; auto with *.
Qed.

    




Lemma forsize_ge:
  forall i,
  forsize i >= 0.
Proof.
  induction i; simpl; intros; auto with *.
Qed.


Lemma loopsize_ge:
  forall i,
  loopsize i >= 0.
Proof.
  induction i; simpl; intros; auto with *.
Qed.

(*
Lemma in_size: forall y x, In x y -> size x <= size y.
Proof.
  intros x y H.
  induction H; simpl; auto with *.
  - assert (length r >=0 ).
    {
Qed.

Lemma in_eq:
  forall x y,
  In x y ->
  In y x ->
  x = y.
Proof.
  intros x y H; induction H; intros; auto.
  - apply in_size in H0.
    apply in_size in H.
    assert (size i >= 0) by auto using size_ge.    
    assert (size j >= 0) by auto using size_ge.
    simpl in *.
    omega.
  - apply in_size in H0.
    apply in_size in H.
    assert (size i >= 0) by auto using size_ge.    
    assert (size j >= 0) by auto using size_ge.
    simpl in *.
    omega.
  - apply in_size in H0.
    apply in_size in H.
    assert (size i >= 0) by auto using size_ge.
    simpl in *.
    omega.
  - apply in_size in H0.
    apply in_size in H.
    assert (size i >= 0) by auto using size_ge.
    simpl in *.
    omega.
Qed.

Lemma in_asymmetric:
  forall x y,
    x <> y ->
    In x y ->
    ~In y x.
Proof.
  intros.
  intros N.
  assert (x = y) by auto using in_eq.
  contradiction.
Qed.


Lemma neq_size_neq:
  forall x y,
    (size x <> size y) ->
    x <> y.
Proof.
  intros.
  induction x; intro N; subst; simpl in *; contradict H;  reflexivity.
Qed.

*)
Lemma i_subst_forsize:
  forall i x n k,
    forsize i =  forsize (i_subst x (NNum n) i).
Proof.
  intros i.
  induction i; intros; simpl in *; try reflexivity.
  - assert (IHi1:=IHi1 x n).
    assert (IHi2:=IHi2 x n).
    rewrite IHi1.
    rewrite IHi2.
    reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
Qed.


Lemma i_subst_loopsize:
  forall i x n,
    loopsize i =
    loopsize (i_subst x (NNum n) i).
Proof.
    intros i.
    induction i; intros; simpl in *; try reflexivity.
  - assert (IHi1:=IHi1 x n).
    assert (IHi2:=IHi2 x n).
    rewrite IHi1.
    rewrite IHi2.
    reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
Qed.


Lemma i_subst_size:
  forall i x n,
    size i = size (i_subst x (NNum n) i).
Proof.
    intros i.
    induction i; intros; simpl in *; try reflexivity.
  - assert (IHi1:=IHi1 x n).
    assert (IHi2:=IHi2 x n).
    rewrite IHi1.
    rewrite IHi2.
    reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
  - assert (IHi:=IHi x n).
    destruct (Set_VAR.MF.eq_dec x v).
    + reflexivity.
    + rewrite IHi. reflexivity.
Qed.




Lemma ineq_intrm:
  forall i l, 
    S ( i + S ( l + ( l + 0)) * S ( i)) >
    i + ( l + ( l + 0)) * S ( i).
Proof.
Admitted.
   
Lemma run_runsize:
  forall x y,
    Run x y ->
    forall i hi j hj,
      x = (i, hi) ->
      y = (j, hj) ->
      ige i j.
Proof.
  intros x y HR.
  induction HR; intros ix hx jy hy Hx Hy;
    inversion Hx; inversion Hy; clear Hx Hy; subst.
  - simpl. unfold ige. right. simpl. omega.
  - simpl. unfold ige. right. simpl. omega.
  - assert (IHHR := IHHR i hx j hy eq_refl eq_refl).
    unfold ige in IHHR.
    unfold ige.
    simpl.
    assert (size i >= 0) by auto using size_ge.
    assert (size j >= 0) by auto using size_ge.
    assert (forsize i >= 0) by auto using forsize_ge.
    assert (forsize j >= 0) by auto using forsize_ge.
    destruct IHHR as [Hf | Ht].
    + left. omega.
    + right. omega.
  - unfold ige. right. right. split. {
      simpl. reflexivity.
    }
    simpl. omega.
  - unfold ige. left. simpl. auto.
  - unfold ige.
    assert (forsize i >= 0) by auto using forsize_ge.
    simpl.
    assert (HFS: forsize i = 0 \/ forsize i > 0). {
      omega.
    }
    destruct HFS as [FZ | FP].
    + right. right. omega.
    + left. omega.
  - unfold ige.
    assert (forsize i >= 0) by auto using forsize_ge.
    assert (loopsize i >= 0) by auto using loopsize_ge.
    assert (size i >= 0) by auto using size_ge.
    assert (forsize (i_subst x (NNum n) i) = forsize i). {
      symmetry.
      apply i_subst_forsize.
    }
    assert (size (i_subst x (NNum n) i) = size i). {
      symmetry.
      apply  i_subst_size.
    }
    assert (loopsize (i_subst x (NNum n) i) = loopsize i). {
      symmetry.      
      apply  i_subst_loopsize.
    }
    right.
    left.
    simpl.
    split. {
      omega.
    }
    rewrite H4.
    assert (HE: (length l + S (length l + 0)) = S (length l + (length l + 0))). {
      omega.
    }
    rewrite HE.
    apply ineq_intrm.
Qed.

Theorem unit_skip_r:
    forall x y,
    Run x y ->
    forall i z hi,
      x = (Seq i z, hi) ->
      y = (z, hi) -> 
      Multi_Run (Seq (Seq i Skip) z, hi) (z, hi).
Proof.
  intros. subst.
  inversion H; subst; clear H.
  - apply seq_skip_x_not_x in H4. contradiction.
  - transitivity (Seq Skip z, hi).
    + apply run_imp_mrun.
      apply run_seq.
      apply run_seq_skip.
    + apply run_imp_mrun.
      apply run_seq_skip.
Qed.


Lemma mrun_seq_skip_h:
  forall x h,
    Multi_Run (Seq Skip x, h) (x, h).
Proof.
  intros.
  apply mrun_step with (i2:=x) (h2:=h).
  - apply run_seq_skip.
  - reflexivity.
Qed.


Lemma run_seq_skip_h_eq:
  forall x h h',
    Run (Seq Skip x, h) (x, h') ->
    h = h'.
Proof.
  intros.
  inversion H; subst.
  - contradict H4. apply seq_skip_x_not_x.
  - reflexivity.
Qed.


Lemma norun:
  forall x y,
    Run x y ->
    forall i h,
      x = (i,h) ->
    forall j h',
      y = (j,h') ->
      i <> j.
Proof.
  intros x y HR.
  induction HR; intros ip hi Hx jp hj Hy.
  inversion Hx; inversion Hy; subst; discriminate.
  - inversion Hx; inversion Hy; subst.
    discriminate.
  - inversion Hx; inversion Hy; subst.
    assert (IHHR:=IHHR i hi eq_refl j hj eq_refl).
    intro N.
    inversion N.
    contradiction.
  - inversion Hx; inversion Hy; subst.
    intro N.
    apply seq_skip_x_not_x in N.
    contradiction.
  - inversion Hx; inversion Hy; subst.
    intro N.
    inversion N.
  - inversion Hx; inversion Hy; subst.
    discriminate.
  - inversion Hx; inversion Hy; subst.
    discriminate.
Qed.

Lemma skip_bottom:
  forall x y h j h',
    x = (Skip, h) ->
    y = (j, h') ->
    ~clos_trans_1n _ Run x y.
Proof.
  intros.
  intro N.
  induction N; subst.
  - inversion H1.
  - inversion H1.
Qed.



Inductive IBefore: inst -> inst -> Prop:=
| ibefore_sync:
      IBefore Sync Skip
| ibefore_access:
    forall a,
      IBefore (Access a) Skip
| ibefore_seq:
    forall i j k,
      IBefore i j ->
      IBefore (Seq i k) (Seq j k)
| ibefore_seq_skip:
    forall i,
      IBefore (Seq Skip i) i
| ibefore_for:
    forall r l i x,
      IBefore (For x r i) (Loop x l i)
| ibefore_for_loop_nil:
    forall x i,
      IBefore (Loop x [] i) Skip
| ibefore_for_loop_cons:
    forall x n i l,
      IBefore (Loop x (n::l) i) (Seq (i_subst x (NNum n) i) (Loop x l i)).

Lemma run_ibefore:
  forall x y,
    Run x y ->
    forall i h,
      x=(i,h) ->
      forall j h',
        y=(j,h') ->
        IBefore i j.
Proof.
  intros x y HR.
  induction HR; intros ip hp Hi jp hp' Hj; subst; inversion Hi; inversion Hj; subst.
  - apply ibefore_sync.
  - apply ibefore_access.
  - apply ibefore_seq.
    assert (IHHR:=IHHR i hp eq_refl j hp' eq_refl).
    assumption.
  - apply ibefore_seq_skip.
  - apply ibefore_for.
  - apply ibefore_for_loop_nil.
  - apply ibefore_for_loop_cons.
Qed.



Lemma ibefore_neq:
  forall x y,
    IBefore x y ->
    x <> y.
Proof.
  intros x y H.
  induction H.
  - discriminate.
  - discriminate.
  - intro N.
    inversion N; subst.
    contradict IHIBefore.
    reflexivity.
  - apply seq_skip_x_not_x.
  - intro N.
    inversion N.
  - discriminate.
  - intro N.
    inversion N.
Qed. 



Theorem list_n_l :
  forall (x:nat) (l:list nat),
    l <> x :: l.
Proof.
  intros.
  induction l.
  - discriminate.
  - intro N.
    inversion N; subst.
    contradiction.
Qed.


Lemma ibefore_anti:
  forall x y,
    IBefore x y ->
    ~IBefore y x.
Proof.
  intros x y HB.
  induction HB; intro N; inversion N; subst.
  - contradiction.
  - apply seq_skip_x_not_x_rev in H2.
    contradiction.
  - apply seq_skip_x_not_x_rev in H2.
    contradiction.
  - assert (HSS: forall u, u <> Seq Skip (Seq Skip u)). {
      intros.
      induction u; unfold not in *; intros; inversion H; subst.
      + assert (IHu2:= IHu2 H3).
        contradiction.
    }
    apply HSS in H0.
    contradiction.
  - contradict H2.
    apply list_n_l.
  - contradict H.
    apply list_n_l.
Qed.


Notation ibeforeplus := (clos_trans_n1 _ IBefore).

(*
Global Add Parametric Relation : _ ibeforeplus
    transitivity proved by (clos_rst1n_trans inst ibeforeplus)
  as ibeforeplus_setoid.
*)

Lemma ibeforeplus_skip:
  forall x,
    ~ibeforeplus Skip x.
Proof.
  intro x.
  intro N.
  induction N.
  - inversion H.
  - contradiction.
Qed.



Lemma ibefore_anti_star:
  forall x y,
    IBefore x y ->
    ~clos_trans_n1 _ IBefore y x.
Proof.
  intros x y HC.
  induction HC.
  - intro N.
    apply ibeforeplus_skip in N.
    contradiction.
  - intro N.
    apply ibeforeplus_skip in N.
    contradiction.
  - admit.
  - intro N.
    inversion N; subst.
    + inversion H; subst.
      * apply seq_skip_x_not_x_rev in H3.
        contradiction.
      * assert (HT: (size i0) <> size (Seq Skip (Seq Skip i0))). {
          simpl. omega.
        }
        apply neq_size_neq in HT.
        contradiction.
      * apply list_n_l in H3; auto.
    + inversion H; subst; clear H.
      *  



      
      * inversion
        
        
        

         

Lemma mrun_ibefore:
  forall x y,
    clos_trans_1n _ Run x y ->
    forall i h,
      x=(i,h) ->
      forall j h',
        y=(j,h') ->
          clos_trans_1n _ IBefore i j.
Proof.
  intros x y HR.
  induction HR.
  - intros ip hp Hx jp hpp Hy.
    inversion Hx; inversion Hy; subst.
    eapply run_ibefore in H; eauto.
    apply clos_trans_t1n_iff.
    constructor 1.
    assumption.
  - intros ip hp Hx jp hpp Hy.
    inversion Hx; inversion Hy; subst.
    destruct y as (iy,hy).
    assert (IHHR:= IHHR iy hy eq_refl jp hpp eq_refl).
    eapply run_ibefore in H; eauto.
    constructor 2 with (y:=iy).
    + assumption.
    + assumption.
Qed. 
    
   
Lemma mrun_refl_inst:
  forall x y,
    clos_trans_1n _ Run x y ->
    forall i h h',
    x = (i, h) ->
    y=  (i, h') ->
    h=h'.
Proof.
  intros x y HR.
  induction HR.
  -  intros j h0 h1 Hx Hy;inversion Hx; inversion Hy; subst.
     eapply run_ibefore in H; eauto.
     apply ibefore_neq in H.
     contradiction.
  -  intros j h0 h1 Hx Hy;inversion Hx; inversion Hy; subst.
     destruct y as (yi,yh).
     assert (IHHR:=IHHR yi yh h1 eq_refl).
     eapply run_ibefore in H; eauto.
     eapply mrun_ibefore in HR; eauto.
     Search IBefore.
    
     contradict H.
     
 
  
  inversion HR; subst.
  - intros j h0 h1 Hx Hy;inversion Hx; inversion Hy; subst.
    reflexivity.
  - intros j h0 h' Hx Hy;inversion Hx; inversion Hy; subst; clear Hx Hy.
    assert (NEQ: j<>i2). {
      eapply norun in H; eauto.
    }
    inversion H; subst.
    + inversion H0; subst.
      inversion H4.
    + inversion H0; subst. inversion H5.
    + inversion H0; subst.
      * inversion H; subst.
        ** contradict NEQ.
           reflexivity.
        ** contradict H6.
           apply seq_skip_x_not_x_rev.
      * 
           
           symmetry.
        intro N.
        
        
        inversion H2; subst.
        -- 
       
      
    inversion H0; subst; clear H0.
    + contradict NEQ.
      reflexivity.
    + 
  
    
    
    
    + 
  - 

  
  intros j.
  induction j; intros h0 h1 Hx Hy;inversion Hx; inversion Hy; subst.
  - inversion HR; subst.
    + reflexivity.
    + inversion H4.
  - inversion HR; subst.
    + reflexivity.
    + inversion H4; subst.
      inversion H6; subst.
      inversion H5.
  - inversion HR; subst.
    + reflexivity.
    + inversion H6; subst; clear H6.
      * eapply norun in H4; eauto. contradict H4.
        reflexivity.
      * inversion H4; subst.
        -- eapply norun in H4; eauto.
           contradict H4.

reflexivity.

           inversion H4; subst.
           ++ 
        
        
     
  inversion HR; subst.
  - reflexivity.
  -


    assert (HIJ: j<>i2). {
      eapply norun in H4; eauto.
    }
     apply multi_run_inv_step with (i':=j) (h1':=h1) in H6.
     + 
  
  induction HR.
  - intros j h0 h1 Hx Hy.
    inversion Hx; inversion Hy; subst.
    reflexivity.
  - intros j h5 h6 Hx Hy.
    inversion Hx; inversion Hy; subst; clear Hx Hy.
    assert (HIJ: j<>i2). {
      eapply norun in H; eauto.
    }
    
   

      
    inversion H; subst; clear H.
    + inversion HR; subst; clear HR. inversion H2.
    + inversion HR; subst; clear HR. inversion H3.
    + assert (HJI: j0 = i). {
        

      inversion HR; subst; clear HR.
      * eapply norun in H1; eauto. contradiction.
      * assert (IHHR:=IHHR (Seq j0 k) h2 h6 eq_refl).
        assert (HJI: j0 = i). {
          transitivity (i2,h0).
    
            

Lemma mrun_seq_skip_h_eq:
  forall x y,
    Multi_Run x y ->
    forall i h h', 
      x = (Seq Skip i, h) ->
      y = (i, h') ->
      h = h'.
Proof.
  intros x y HR.
  induction HR.
  - intros i0 h0 h' Hi Hj.
    inversion Hi; inversion Hj; subst.
    reflexivity.
  - intros i0 h0 h' Hi Hj.
    inversion H; inversion Hi; inversion Hj; subst; clear Hi Hj H.
    + inversion H5.
    + inversion H6.
    + inversion H6; subst; clear H6.
      inversion H1.
    + inversion H5; subst; clear H5.
      


      assert (HT: i = Skip). {
        inversion H6.
        reflexivity.
      }
      subst.
      inversion H1.
    + inversion H5. subst.
      inversion HR; subst.
      * reflexivity.
      * inversion H2; subst.
        -- 
      assert (IHHR := IHHR i2 h2 h').
      
      assert (HT: i0 = k). {
        inversion H6.
        reflexivity.
      }
      subst.
      
                      
    inversion Hi; inversion Hj; subst; clear Hi Hj.
    inversion H; subst; clear H.
    + inversion H1.
    + 
      assert (IHHR := IHHR i2 h2 h').
    
  - contradict H3.  apply seq_skip_x_not_x.
  - 

Theorem unit_skip_star_r:
  forall x y,
    Multi_Run x y ->
    forall i z hi,
      x = (Seq i z, hi) ->
      y = (z, hi) -> 
      Multi_Run (Seq (Seq i Skip) z, hi) y.
Proof.
  intros x y HR.
  induction HR.
  - intros j z hj Hx Hy.
    inversion Hx; inversion Hy; subst.
    apply seq_skip_x_not_x in H2. contradiction.
  - intros i z hi Hx Hy.
    assert (HB: Seq i z <> z). {
      apply seq_skip_x_not_x.
    }
    inversion Hx; subst; clear Hx.
    inversion Hy; subst; clear Hy.
    assert (IHHR := IHHR i z hi).
    assert (HIJ: i2 = Seq i z). {
      inversion H; subst; clear H.
      + inversion H1; subst.
        ++ 

      
    inversion H; subst; clear H.
    + 
    + assert (HIJ: i = j). {
        inversion H1; subst; clear H1; auto.
        * inversion HR; subst; clear HR.
          ++ apply seq_skip_x_not_x in H. contradiction.
          ++ inversion H2; subst; clear H2.
             ** inversion H0.
             ** inversion H4; subst.
                +++
    apply unit_skip_r with (x:=(Seq i z, hi)) (y:=(z, hi)).
    
    + apply run_seq.
    + apply run_imp_mrun in H.
    inversion H; subst; clear H.
    + 
    + reflexivity.
Qed.
    
    inversion HR; subst; clear HR.
    + reflexivity.
    + inversion H; subst.
      * 

    intros. inversion H0; inversion H1; subst; clear H0 H1.
    assert (IHHR := IHHR i z h2).
    eapply unit_skip_r; eauto.
    inversion H; subst; clear H.
    + 
    
    
    inversion H; subst; clear H. (* WEDS HERE *)
    +  assert (IHHR := IHHR eq_refl).
    
    transitivity (i2,h2).
    + eapply unit_skip_r; eauto.
      
    + assumption.
    eapply unit_skip_r in H; eauto.
    + 
      

Lemma eq_skip_mrun:
  forall x y,
    IEquivOne x y ->
    y = Skip ->
    forall z h,
      Multi_Run (Seq x z, h) (z, h).
Proof.
  intros x y HE HS z h.
  induction x.
  - apply run_imp_mrun. apply run_seq_skip.
  - inversion HE; subst. inversion H0.
  - inversion HE; subst; clear HE.
    + apply IHx2 in H2.
      transitivity (Seq x2 z, h).
      * apply run_imp_mrun. apply run_seq. apply run_seq_skip.
      * assumption.
    + apply IHx1 in H2.
      
      transitivity (Seq (Seq Skip Skip) z, h).
      * assert (HMR: Multi_Run (Seq x1 z, h) (Seq Skip z, h)). {
          
        
      induction H2.
      * 
      pose x1 = (Seq x1 z, h).
      inversion H2; subst; clear H2.
      * apply seq_skip_x_not_x in H. contradiction.
      * transitivity (i2,h2).
        ** inversion H3; subst; clear H3.
           ++ 
             
      * 
 

Theorem equiv_one_mrun_r:
  forall x y,
    IEquivOne y x ->
    forall x' h h',
      Run (x, h) (x', h') ->
      exists y', 
        (Multi_Run (y, h) (y', h') /\ (IEquivOne y' x' \/ y'=x')). 
Proof.
  intros x y HE.
  induction HE.
  - intros x' h h' HR.
    assert (IHHE := IHHE x' h h' HR).
    destruct IHHE as (yhat, IHHE).
    destruct IHHE as (Ha, Hb).
    exists yhat.
    split. {
      transitivity (i,h).
      + apply run_imp_mrun. apply run_seq_skip.
      + assumption.
    }
    assumption.
  - intros x' h h' HR.
    assert (IHHE := IHHE x' h h' HR).
    destruct IHHE as (yhat, IHHE).
    destruct IHHE as (Ha, Hb).
    exists (Seq yhat Skip). split. {
      eapply mrun_mrun_seq; eauto.
    }
    left. apply equiv_unit_l.
    destruct Hb as [Hq|He].
    + assumption.
    + subst. apply equiv_eq.
  - intros xp h hp HR.
    inversion HR; subst; clear HR.
    inversion H0; subst; clear H0.
    + assert (IHHE1 := IHHE1 j0 h hp H1).
      destruct IHHE1 as (yhat, (GHEa, GHEb)).
      exists (Seq yhat (Seq y z)). split. { 
        eapply mrun_mrun_seq; eauto.
      }
      destruct GHEb as [Hq|He]; left.
      * apply equiv_assoc.
        ** assumption.
        ** assumption.
        ** assumption.
      * subst. apply equiv_assoc.
        ** apply equiv_eq.
        ** assumption.
        ** assumption.
    + admit.
  - intros. exists x'.
        
     

        exists (Seq y z). split. {
          
          
          apply mrun_mrun_seq_seq.
        }
        left.
        apply equiv_seq.
        ** assumption.
        ** assumption.
      *
        left. apply equiv_seq.
        ** apply equiv_unit_r.
           admit.
        ** 
        apply run_imp_mrun.
      left.
        ** 
           
        
        
      * left. apply equiv_assoc.
      * 
    
    inversion HR; subst; clear HR.
    * exists i
    * exists j. split.
    + reflexivity.
    + left. assumption.
  - intros x' h h' HR.
    inversion HR; subst; clear HR.
    * assert (IHHE := IHHE j0 h h').
      apply IHHE in H0.
      destruct H0 as (yhat, (H0r,H0e)).
      exists yhat.
      split.
    + assumption.
    + destruct H0e.
      ++ left. apply equiv_unit_l.  assumption.
      ++ subst. left. apply equiv_unit_l. apply equiv_eq.
      * inversion HE; subst.
        exists Skip. split.
        ** reflexivity.
        ** auto.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    * apply IHHE1 in H0.
      destruct H0 as (yhat, (H0R, H0E)).
      exists (Seq (Seq yhat y') z'). split.
      ** apply mrun_mrun_seq_seq with (x:=(x', h)) (y:=(yhat, h')).
      ++ assumption.
      ++ reflexivity.
      ++ reflexivity.
         ** left. apply equiv_assoc.
            +++ destruct H0E.
                *** assumption.
                *** subst. apply equiv_eq.
            +++ assumption.
            +++ assumption.
    * inversion HE1; subst; clear HE1.
    + exists (Seq y' z'). split.
      ++ apply run_imp_mrun. apply run_seq. apply run_seq_skip.
      ++ left. auto using equiv_seq.
  -  intros x0' h h' HR.
     exists x0'.
     split.
     + apply run_imp_mrun. assumption.
     + left. apply equiv_eq.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    + apply IHHE1 in H0.
      destruct H0 as (yhat, (H0R,H0E)).
      exists (Seq yhat y'). split.
      { eapply mrun_mrun_seq. eauto.
        * reflexivity.
        * reflexivity.
      }
      destruct H0E as [WEQ | SEQ].
      * left. apply equiv_seq; assumption.
      * subst. left. apply equiv_seq.
        ** apply equiv_eq.
        ** assumption.
    + inversion HE1; subst; clear HE1.
      exists y'. split. {
        apply run_imp_mrun. apply run_seq_skip.
      }
      left. assumption.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    exists (Loop l l0 y).
    split. {
      apply run_imp_mrun. apply run_for. assumption.
    }
    left. apply equiv_loop. assumption.
  - intros x0' h h' HR.
    inversion HR; subst; clear HR.
    * exists Skip. split. {
        apply run_imp_mrun. apply run_for_loop_nil.
      }
      right. reflexivity.
    * exists (Seq (i_subst l (NNum n) y) (Loop l l0 y)).
      split. {
        apply run_imp_mrun. apply run_for_loop_cons.
      }
      left. apply equiv_seq.
    + apply equiv_subst. assumption.
    + apply equiv_loop. assumption.
Qed.


  
  intros x x' y h h' HE HR.
  inversion HE; subst; clear HE.
  - exists x'. split.
    + transitivity (x,h).
      * apply mrun_seq_skip.
      * auto using run_imp_mrun.
    + right. reflexivity.
  - exists (Seq x' Skip). split.
    + transitivity (Seq x' Skip,h').
      *  apply run_imp_mrun.
         apply run_seq. assumption.
      * reflexivity.
    + left. apply equiv_unit_l.
  - inversion HR; subst; clear HR.
    * inversion H0; subst; clear H0.
    + exists (Seq j0 (Seq y0 z)). split.
      ++ apply run_imp_mrun.
         auto using run_seq.
      ++ left. apply equiv_assoc.
    + exists (Seq j z). split.
      ++ apply run_imp_mrun.
         auto using run_seq_skip.
      ++ right. reflexivity.
Qed.


Lemma equiv_inc_star:
  forall x y,
    (IEquivOne x y \/ x=y) ->
    iequivstar x y.
Proof.
  intros.
  (* Print clos_refl_sym_trans_n1. *)
  destruct H.
  - apply rstn1_trans with (y:=x).
    left. assumption. reflexivity.
  - subst. reflexivity.
Qed.

Theorem equiv_one_mrun_star_r:
  forall x x' y h h',
    IEquivOne y x ->
    Run (x, h) (x', h') ->
    exists y', 
      Multi_Run (y, h) (y', h')  /\ iequivstar y' x'.
Proof.
  intros.
  assert (HE: exists y' : inst, Multi_Run (y, h) (y', h') /\ (IEquivOne y' x' \/ y'=x')). {
    eauto using equiv_one_mrun_r.
  }
  destruct HE as (y0, (HM, HEQ)).
  apply equiv_inc_star in HEQ.
  exists y0.
  split; assumption.
Qed.

Theorem equiv_one_mrun_star_l:
  forall x x' y h h',
    IEquivOne x y ->
    Run (x, h) (x', h') ->
    exists y', 
      Multi_Run (y, h) (y', h')  /\ iequivstar x' y'.
Proof.
  intros.
  assert (HE: exists y' : inst, Multi_Run (y, h) (y', h') /\ (IEquivOne x' y' \/ x'=y')). {
    eauto using equiv_one_mrun_l. }
  destruct HE as (y0, (HM, HEQ)).
  apply equiv_inc_star in HEQ.
  exists y0.
  split; assumption.
Qed.






Lemma unit_skip_par_intrm:
  forall x y,
    Multi_Run x y ->
    forall i z hi,
      x = (Seq i z, hi) ->
      y = (z, hi) ->
      Multi_Run x (Seq Skip z, hi).
Proof.
  intros x y HR.
  intros i z hi Hx Hy.
  induction i; inversion Hy; inversion Hx; subst.
  - reflexivity.
  - assert (HIE: hi = []). {
      inversion HR; subst; clear HR.
      + apply seq_skip_x_not_x in H4. contradiction.
      + apply seq_sync_imp_emptyhist in H4.
        destruct H4 as (Hi,Hh).
        subst.
        




Lemma mrun_eq_sim_r:
  forall a b, 
  Multi_Run a b ->
  forall x h x' h',
    a= (x, h) ->
    b= (x', h') ->
    forall y,
      IEquivOne y x ->
      exists y', 
        Multi_Run (y, h) (y', h')  /\ (iequivstar y' x').
Proof.
  intros a b HR.
  induction HR.
  - intros. inversion H; inversion H0; subst; clear H H0.
    exists y. split.
    * apply mrun_refl.
    *  apply equiv_inc_star. auto.
  - intros. inversion H1; inversion H0; subst; clear H0 H1.
    assert (IHHR := IHHR i2 h2 x' h' eq_refl eq_refl).
    apply equiv_one_mrun_r with (y:=y) in H.
    + destruct H as (y2, (HMR, [HMO | HME])).
      * apply IHHR in HMO.
        destruct HMO as (yhat, (HMOa, HMOb)).
        ** exists yhat. split. {
             transitivity (y2,h2); auto.
           }
           auto.
      *  subst.  exists x'. split. {
             etransitivity; eauto.
           }
         reflexivity.
    + assumption.    
Qed.

Lemma mrun_eq_sim_l:
  forall a b, 
  Multi_Run a b ->
  forall x h x' h',
    a= (x, h) ->
    b= (x', h') ->
    forall y,
      IEquivOne x y ->
      exists y', 
        Multi_Run (y, h) (y', h')  /\ (iequivstar x' y').
Proof.
  intros a b HR.
  induction HR; intros.
  -  inversion H; inversion H0; subst; clear H H0.
     exists y. split.
     + reflexivity.
     + apply equiv_inc_star. auto.
  - assert (IHHR := IHHR i2 h2 i3 h3 eq_refl eq_refl).
    apply equiv_one_mrun_l with (y:=y) in H.
    inversion H1; inversion H0; subst; clear H0 H1.
    + destruct H as (y2, (HMR, [HMO | HME])).
      * apply IHHR in HMO.
        destruct HMO as (yhat, (HMOa, HMOb)).
        ** exists yhat. split. {
             transitivity (y2,h2); auto.
           }
           auto.
      * subst. exists x'.  split. {
             etransitivity; eauto.
           }
        reflexivity.
    + inversion H1; inversion H0; subst; clear H1 H0.
      assumption.
Qed.
             

  
Theorem equiv_star_mrun:
  forall x y,
    iequivstar x y ->
    forall x' h h',
      Run (x, h) (x', h') ->
      exists y', 
        Multi_Run (y, h) (y', h') /\  iequivstar x' y'.
Proof.
  intros x y HE.
  induction HE; intros.
  - exists x'. split.
    * auto using run_imp_mrun.
    * reflexivity.
  - destruct H.
    * apply IHHE in H0.
      destruct H0 as (yhat, (H0R, H0E)).
      apply mrun_eq_sim_l with (x:=y) (h:=h) (x':=yhat) (h':=h') (y:=z) in H0R.
      destruct H0R as (yp, (H0Rl, H0Rr)).
    + exists yp. split. {
        auto.
      }
      transitivity (yhat).
      ++ assumption.
      ++ assumption.
    + reflexivity.
    + reflexivity.
    + assumption.
      * apply IHHE in H0.
        destruct H0 as (yhat, (H0R, H0E)).
        apply mrun_eq_sim_r with (x:=y) (h:=h) (x':=yhat) (h':=h') (y:=z) in H0R.
        destruct H0R as (yp, (H0Rl, H0Rr)).
        + exists yp. split. {
        auto.
      }
      transitivity (yhat).
      ++ assumption.
      ++ symmetry. assumption.
        + reflexivity.
        + reflexivity.
        + assumption.
Qed.


Theorem wequiv_star_mrun:
  forall a b,
    Multi_Run a b ->
    forall x h x' h',
      a = (x, h) -> 
      b = (x', h') ->
      forall y,
        iequivstar x y ->
        exists y', 
          Multi_Run (y, h) (y', h') /\  iequivstar x' y'.
Proof.
  intros a b HR.
  induction HR.
  - intros. inversion H; inversion H0; subst; clear H0 H.
    exists y. split.
    * reflexivity.
    * assumption.
  - intros. inversion H0; inversion H1; subst; clear H0 H1.
    assert (IHHR := IHHR i2 h2 x' h' eq_refl eq_refl).
    apply equiv_star_mrun with (y:=y) in H.
    * destruct H as (yhat, (HMR, HME)).
      assert (IHHR := IHHR yhat HME).
      destruct IHHR as (yp, (IHa, IHb)).
      exists yp.
      split.
    + transitivity (yhat, h2). assumption. assumption.
    + assumption.
      * assumption.
Qed.

     
Lemma sync_src_norm:
  forall i j,
    Normalised i j ->
    forall i1 i2,
      j = (i1,i2) ->
      forall x h,
        Run (i,h) x ->
        Multi_Run (Merge i1 i2, h) x.
Proof.
  intros i j HN.
  induction HN.
  - intros. inversion H0; subst. simpl. apply run_imp_mrun. assumption.
  - intros. inversion H; subst. simpl. transitivity (Seq Skip Skip, @nil access_val).
    + apply run_imp_mrun. apply run_seq. apply run_sync.
    + inversion H0; subst. apply run_imp_mrun. apply run_seq_skip.
  - intros. inversion H; subst; clear H.
    assert (IHHN1 := IHHN1 (Some i1) i2 eq_refl).
    inversion H0; subst; clear H0. simpl.
    + assert  (IHHN1 := IHHN1 (j0,h') h).
      apply IHHN1 in H4.
      simpl in H4.
      apply mrun_mrun_seq with (i:=(Seq i1 i2)) (j:=j0) (h:=h) (h':=h') (k:=(Seq j1 i3)) in H4.
      * assert (HEQ: iequivstar  (Seq (Seq i1 i2) (Seq j1 i3)) (Seq (Seq i1 (Seq i2 j1)) i3)). {
          constructor 2.
          transitivity (Seq (Seq (Seq i1 i2) j1) i3).
          ** admit.
          ** 

      
      transitivity (Seq (Seq j0 j1) i3 , h').
      * eapply mrun_mrun_seq; eauto.
        ** 

        

    
forall i hi x,
Run (i, hi) x ->
In Sync i ->
exists i1 i2,
Normalised i (i1, i2) /\
Multi_Run (Merge i1 i2, hi) x.

Lemma sync_src_norm_seq:
forall i i1 i2,
  Normalised i (Some i1, i2) ->
  forall j j0 j3,
    Normalised j (Some j0, j3) ->
    forall hi j4 h',
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

