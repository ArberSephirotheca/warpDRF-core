From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.

Section Defs.
  Inductive inst :=
  | Skip: inst
  | If: bexp -> inst -> inst -> inst
  | Seq: inst -> inst -> inst
  | MemAcc: access_exp -> inst
  | For : var -> range -> inst -> inst
  .
End Defs.
