From Faial.Core Require Import Var.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.
From Faial.Drf.U Require Var.
From Faial.Drf.U Require Occurs.
From Faial.Drf.U Require Import CSeq.

Section Defs.
  Fixpoint Distinct (c:t) :=
    match c with
    | Skip | MemAcc _ => True
    | If _ c1 c2 | Seq c1 c2 => Distinct c1 /\ Distinct c2
    | For x _ c => ~ Var.t x c /\ Distinct c
    end.

  Lemma distinct_subst:
    forall c,
    Distinct c ->
    forall x v,
    Distinct (f x v c).
  Proof.
    induction c; simpl; auto; intros.
    - intuition.
    - intuition.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        intuition.
      }
      intuition.
      apply Var.inv_subst in H2.
      intuition.
  Qed.

  Lemma distinct_c_seq:
    forall c1 c2,
    Distinct c1 ->
    Distinct c2 ->
    Distinct (c_seq c1 c2).
  Proof.
    induction c1; simpl; intros; auto.
    destruct H as (d1, d2).
    auto.
  Qed.

  Definition CClosed P :=
    forall x, ~ Occurs.t x P.
End Defs.
