Require Trace.
From Faial.Expr Require Import SIMT.A.Exp.
Require D.Lang.
Require D.LRun.
Require D.Report.
Require U.Report.
Require D.Infer.

Inductive t : D.Lang.t -> access_val * Trace.t -> Prop :=
  def:
    forall s r,
    U.Report.t (Infer.f s) r ->
    ~ D.Report.t s r ->
    t s r.
