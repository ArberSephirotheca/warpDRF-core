From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.

Section Defs.
  Inductive t :=
  | Skip: t
  | If: bexp -> t -> t -> t
  | Seq: t -> t -> t
  | MemAcc: access_exp -> t
  | For : var -> range -> t -> t
  | Decl : var -> t -> t
  .
End Defs.
