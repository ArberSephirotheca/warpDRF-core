From Faial.Approx.D Require Import Lang.
From Faial.Core Require Import Var.

Fixpoint t (x:var) (s:Lang.t) : Prop :=
  match s with
  | Read y _ s
  | Decl y s
  | Loop y _ s
    => x = y \/ t x s
  | Write _ _
  | Skip
    => False
  | Seq s1 s2
  | Cond _ s1 s2
    => t x s1 \/ t x s2
  end.