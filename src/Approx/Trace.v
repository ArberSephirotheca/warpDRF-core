From Faial.Approx Require Import Var.
From Faial.Approx Require Import Tictac.
Section Defs.
  Inductive t :=
  | skip
  | seq: t -> t -> t
  | iter: var * nat -> t -> t -> t
  | then_branch: t -> t
  | else_branch: t -> t.
End Defs.

Module Loop.
  Inductive t : Trace.t -> var -> nat -> nat -> Prop :=
  | next:
    forall x lo l1 l2 hi,
    l2 <> skip ->
    t l2 x (S lo) hi ->
    t (Trace.iter (x, lo) l1 l2) x lo hi
  | skip:
    forall x n l,
    t (Trace.iter (x, n) l skip) x n (S n).

  Lemma hi_func:
    forall l x lo hi1,
    t l x lo hi1 ->
    forall hi2,
    t l x lo hi2 ->
    hi1 = hi2.
  Proof.
    intros l x lo hi1 H.
    induction H.
    all: intros hi2 Hi.
    all: invc Hi.
    all: subst.
    all: intuition.
  Qed.

  Lemma func:
    forall l x lo1 hi1,
    t l x lo1 hi1 ->
    forall y lo2 hi2,
    t l y lo2 hi2 ->
    x = y /\ lo1 = lo2 /\ hi1 = hi2.
  Proof.
    intros l x lo1 hi1 H.
    induction H.
    all: intros.
    - invc H1.
      + intuition.
        eauto using hi_func.
      + contradiction.
    - invc H.
      + contradiction.
      + auto.
  Qed.
End Loop.