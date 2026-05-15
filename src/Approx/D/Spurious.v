Require Trace.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Approx.D Require Lang.
From Faial.Approx.D Require LRun.
From Faial.Approx.D Require Report.
From Faial.Approx.U Require Report.
From Faial.Approx.D Require Infer.

Inductive t : D.Lang.t -> access_val * Trace.t -> Prop :=
  def:
    forall s r,
    U.Report.t (Infer.f s) r ->
    ~ D.Report.t s r ->
    t s r.
