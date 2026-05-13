Require Trace.
From Faial.Expr Require Import SIMT.A.Exp.
Require D.Lang.
Require D.LRun.
  Inductive t : D.Lang.t -> access_val * Trace.t -> Prop :=
    def:
      forall base tid M1 M2 h a l s,
      D.LRun.t tid base M1 s h M2 l ->
      List.In a h ->
      t s (a, l).
