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
Require Import Hist.
Require Import Omega.
Require Import Lia.

Import ListNotations.


Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | If
  | Hole
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.


  
Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Sync => Sync
  | If => If
  | Hole => Hole
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  | Loop y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2'
  end.


Notation history := (list access_val).

Notation mhistory := (list history).

(* Why can't I use this in the sig of Run? *)
Notation histpair := (mhistory * history).

Context `{T:Tasks}.


Inductive Run: ((mhistory * history) * inst) -> (mhistory * history) -> Prop :=
| run_skip:
    forall x,
    Run (x, Skip) x
| run_sync:
  forall h hs,
    Run ((hs, h), Sync) (h::hs, [])
| run_seq:
    forall i j x y z,
      Run (x, i) y ->
      Run (y,j) z ->
      Run (x, Seq i j) z
| run_for:
  forall r l i x h,
  RStep r l ->
  Run (x, (For x r i)) ((Loop x l i), h)



      
| run_loop_nil:
  forall x i h,
  Run ((Loop x [] i), h) (Skip, h)
| run_loop_cons:

