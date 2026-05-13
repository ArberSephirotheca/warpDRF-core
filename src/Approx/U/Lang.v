From Faial.Approx Require Import Var.
From Faial.Approx Require Import NExp.
From Faial.Approx Require Import BExp.
From Faial.Approx Require Import RExp.
From Faial.Approx Require Import AExp.

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
