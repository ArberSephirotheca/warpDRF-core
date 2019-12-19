Require Import Coq.Lists.List.
Require Import Var.
Import ListNotations.
Require Coq.omega.Omega.

Section Defs.

  Inductive nbin :=
  | NPlus
  | NMinus
  | NMult
  | NDiv
  | NMod.

  Inductive nexp :=
  | NNum : nat -> nexp
  | NVar : var -> nexp
  | NBin : nbin ->  nexp -> nexp -> nexp.

  Definition add := NBin NPlus.
  Definition sub := NBin NMinus.
  Definition mul := NBin NMult.
  Definition div := NBin NDiv.
  Definition mod := NBin NMod.

  Inductive nrel := NEq | NLe | NLt.

  Inductive brel := BOr | BAnd.

  Inductive bexp :=
  | BBool: bool -> bexp
  | NRel : nrel -> nexp -> nexp -> bexp
  | BRel : brel -> bexp -> bexp -> bexp
  | BNot : bexp -> bexp.

  Inductive mode := R | W.

  Definition mode_eqb m1 m2 :=
  match m1, m2 with
  | R, R | W, W => true
  | _, _ => false
  end.

  Definition range := (nexp * nexp) % type.

End Defs.

Section SO.

  Definition eval_nbin o :=
  match o with
  | NPlus => Nat.add
  | NMinus => Nat.sub
  | NMult => Nat.mul
  | NDiv => Nat.div
  | NMod => Nat.modulo
  end.

  Inductive NStep: nexp -> nat -> Prop :=
  | nstep_num:
    forall n,
    NStep (NNum n) n
  | nstep_bin:
    forall n1 n2 o e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin o e1 e2) (eval_nbin o n1 n2). 

  Inductive IStep: list nexp -> list nat -> Prop :=
  | i_step_nil:
    IStep [] []
  | i_step_cons:
    forall i l e n,
    IStep i l ->
    NStep e n ->
    IStep (e::i) (n::l).

  Definition eval_nrel (o:nrel) :=
  match o with
  | NEq => Nat.eqb
  | NLt => Nat.ltb
  | NLe => Nat.leb
  end.

  Definition eval_brel (o:brel) :=
  match o with
  | BOr => orb
  | BAnd => andb
  end.

  Inductive BStep: bexp -> bool -> Prop :=
  | bstep_bool:
    forall b,
    BStep (BBool b) b
  | bstep_nrel:
    forall e1 e2 n1 n2 o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    BStep (NRel o e1 e2) (eval_nrel o n1 n2)
  | bstep_brel:
    forall e1 e2 b1 b2 o,
    BStep e1 b1 ->
    BStep e2 b2 ->
    BStep (BRel o e1 e2) (eval_brel o b1 b2).

  (*
  Program Function range_list (lo high: nat) :=
  if Nat.leb high lo then nil
  else lo :: range_list (S lo) high.
*)

  Inductive RangeList : nat -> nat -> list nat -> Prop :=
  | range_list_empty:
    forall low high,
    low >= high ->
    RangeList low high []
  | range_list_cons:
    forall low high l,
    low < high ->
    RangeList (S low) high l ->
    RangeList low high (low::l). 

  Inductive RStep: range -> list nat -> Prop :=
  | rstep_def:
    forall e1 e2 n1 n2 l,
    NStep e1 n1 ->
    NStep e2 n2 ->
    RangeList n1 n2 l ->
    RStep (e1, e2) l.

  Fixpoint n_subst x (v:nat) e :=
  match e with
  | NBin o e1 e2 => NBin o (n_subst x v e1) (n_subst x v e2)
  | NVar y => if VAR.eq_dec x y then (NNum v) else e  
  | NNum n => NNum n
  end.

  Fixpoint b_subst x v e :=
  match e with
  | NRel o e1 e2 => NRel o (n_subst x v e1) (n_subst x v e2)
  | BRel o e1 e2 => BRel o (b_subst x v e1) (b_subst x v e2)
  | BNot b => BNot (b_subst x v b)
  | BBool b => BBool b
  end.

  Fixpoint i_subst x v l :=
  match l with
  | [] => []
  | n :: l => n_subst x v n :: i_subst x v l
  end.

  Definition r_subst x v (r:range) :=
  let (n1, n2) := r in
  (n_subst x v n1, n_subst x v n2).
(*
  Definition NonemptyRange (r:nat * nat) := let (n1, n2) := r in n1 < n2. 

  Definition EmptyRange (r:nat * nat) := let (n1, n2) := r in n1 >= n2.

  Definition InRange n (r:nat * nat) := let (n1, n2) := r in n >= n1 /\ n < n2.

  Definition inc (r:nat * nat) :=
  let (n1, n2) := r in
  (NNum (S n1), NNum n2).

*)

  Lemma n_step_fun:
    forall n n1 n2,
    NStep n n1 ->
    NStep n n2 ->
    n1 = n2.
  Proof.
    induction n; intros;
    inversion H; inversion H0; subst; clear H H0.
    - trivial.
    - assert (n5 = n7) by eauto.
      assert (n6 = n8) by eauto.
      subst.
      trivial.
  Qed.  

  Section range_list_fun.
    Import Omega.
    Lemma range_list_fun:
      forall l1 n1 n2 l2,
      RangeList n1 n2 l1 ->
      RangeList n1 n2 l2 ->
      l1 = l2.
    Proof.
      induction l1; intros; inversion H; subst; clear H. {
        inversion H0; subst; clear H0. {
          reflexivity.
        }
        omega.
      }
      inversion H0; subst; clear H0. {
        omega.
      }
      erewrite IHl1; eauto.
    Qed.
  End range_list_fun.

  Lemma r_step_fun:
    forall r n1 n2,
    RStep r n1 ->
    RStep r n2 ->
    n1 = n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n0 = n4) by eauto using n_step_fun.
    assert (n3 = n5) by eauto using n_step_fun.
    subst.
    assert (n1 = n2) by eauto using range_list_fun.
    assumption.
  Qed.
End SO.


