Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import RExp.
Require Import AExp.

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
