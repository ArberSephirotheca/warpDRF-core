Require Import RExp.
Require Import NExp.
Require Import Tictac.
From Stdlib Require Import Lia.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> nat -> Prop :=
  | def:
    forall e1 e2 n1 n2 n,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    n1 <= n ->
    S n < n2 ->
    t (e1, e2) n.

End Defs.