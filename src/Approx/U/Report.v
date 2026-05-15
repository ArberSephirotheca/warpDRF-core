Require Trace.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Approx.U Require Lang.
From Faial.Approx.U Require LRun.
  Inductive t : U.Lang.t -> access_val * Trace.t -> Prop :=
    def:
      forall tid h a l s,
      U.LRun.t tid s h l ->
      List.In a h ->
      t s (a, l).
