From Faial.Core Require Import Var.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.

Inductive t :=
| Read : var -> nexp -> t -> t
| Write : nexp -> nexp -> t
| Seq : t -> t -> t
| Cond : bexp -> t -> t -> t
| Barrier : nat -> t
| AddZero
| Skip.

(* Read binders have the same scope as in Approx.D.Subst. *)
Fixpoint subst x v code :=
  match code with
  | Read y address body =>
      Read y (n_subst x v address)
        (if VAR.eq_dec x y then body else subst x v body)
  | Write address contents =>
      Write (n_subst x v address) (n_subst x v contents)
  | Seq first rest => Seq (subst x v first) (subst x v rest)
  | Cond test yes no => Cond (b_subst x v test) (subst x v yes) (subst x v no)
  | Barrier site => Barrier site
  | AddZero => AddZero
  | Skip => Skip
  end.
