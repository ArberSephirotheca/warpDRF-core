Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import RExp.
Require Import AExp.
Require Import Util.
Require Import Tasks.
Require Import PairInUtil.
Require Import Tictac.
Require Import Hist.

Require Import NatUtil.
Require Import Hist.
Require TClos.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Sorting.SetoidList.
Require Mem.
From Stdlib Require Import List.
Require R.Empty.
Require R.Step.

Import ListNotations.

(* ====================================== *)
(*                Syntax                  *)
(* ====================================== *)

Inductive t : Type :=
| Read: var -> nexp -> t -> t
| Write: nexp -> nexp -> t
| Seq: t -> t -> t
| Cond: bexp -> t -> t -> t
| Loop: var -> range -> t -> t
| Skip
| Decl: var -> t -> t
.

