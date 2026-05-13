From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Core Require Import Util.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import PairInUtil.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Hist.

Require Import NatUtil.
From Faial.Core Require Import Hist.
Require TClos.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Sorting.SetoidList.
Require Mem.
From Stdlib Require Import List.
From Faial.Expr Require SIMT.R.Empty.
From Faial.Expr Require SIMT.R.Step.

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

