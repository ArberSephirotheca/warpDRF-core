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

