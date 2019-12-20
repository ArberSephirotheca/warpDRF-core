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
  | n_step_num:
    forall n,
    NStep (NNum n) n
  | n_step_bin:
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
  | b_step_bool:
    forall b,
    BStep (BBool b) b
  | b_step_nrel:
    forall e1 e2 n1 n2 o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    BStep (NRel o e1 e2) (eval_nrel o n1 n2)
  | b_step_brel:
    forall e1 e2 b1 b2 o,
    BStep e1 b1 ->
    BStep e2 b2 ->
    BStep (BRel o e1 e2) (eval_brel o b1 b2).

  (*
  Program Function range_list (lo high: nat) :=
  if Nat.leb high lo then nil
  else lo :: range_list (S lo) high.
*)

  Inductive InvRangeList : nat -> nat -> list nat -> Prop :=
  | inv_range_list_empty:
    forall n m,
    n >= m ->
    InvRangeList n m []
  | inv_range_list_cons:
    forall n m l,
    n <= m ->
    InvRangeList n m l ->
    InvRangeList n (S m) (m :: l).

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
  | r_step_def:
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

    Lemma range_list_inv_1:
      forall n,
      RangeList 0 n [] ->
      n = 0.
    Proof.
      intros.
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_2:
      forall l n,
      RangeList n 0 l ->
      l = [].
    Proof.
      destruct l; intros. {
        reflexivity.
      }
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_3:
      forall l n1 n2,
      RangeList n1 n2 l ->
      n1 >= n2 ->
      l = [].
    Proof.
      induction l; intros; auto.
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_4:
      forall n1 n2,
      RangeList n1 n2 [] ->
      n1 >= n2.
    Proof.
      intros.
      inversion H; subst; clear H.
      assumption.
    Qed.

    Lemma range_list_inv_5:
      forall n1 n2 n3 l,
      RangeList n1 n2 (n3 :: l) ->
      n3 = n1.
    Proof.
      intros.
      inversion H; subst; clear H.
      reflexivity.
    Qed.

    Lemma range_list_inv_succ_nil:
      forall n1 n2,
      RangeList (S n1) (S n2) [] ->
      RangeList n1 n2 [].
    Proof.
      intros.
      inversion H; subst; clear H.
      assert (n1 >= n2) by auto with *.
      apply range_list_empty.
      assumption.
    Qed.

    Lemma range_list_inv_cons:
      forall l n1 n2 a,
      RangeList n1 (S n2) (l ++ [a]) ->
      a = n2.
    Proof.
      induction l; simpl; intros. {
        inversion H; subst; clear H.
        apply range_list_inv_succ_nil in H5.
        inversion H5; subst; clear H5.
        omega.
      }
      inversion H; subst; clear H.
      apply IHl in H5.
      subst.
      reflexivity.
    Qed.

    Lemma range_list_inv_cons_2:
      forall l n1 n2,
      RangeList n1 (S n2) (l ++ [n2]) ->
      RangeList n1 n2 l /\ n1 <= n2.
    Proof.
      induction l; simpl; intros;
      inversion H; subst; clear H.
      - split; auto using le_n.
        apply range_list_empty.
        apply le_n.
      - inversion H4; subst; clear H4. {
          apply range_list_inv_3 in H5; auto.
          destruct l; inversion H5.
        }
        apply IHl in H5.
        destruct H5.
        split. {
          apply range_list_cons; auto.
        }
        omega.
    Qed.

    Lemma range_list_succ:
      forall l n1 n2,
      n1 <= n2 ->
      RangeList n1 n2 l ->
      RangeList n1 (S n2) (l ++ [n2]).
    Proof.
      induction l; intros. {
        apply range_list_inv_4 in H0.
        assert (n1 = n2) by omega.
        subst.
        apply range_list_cons.
        + omega.
        + apply range_list_empty.
          omega.
      }
      simpl.
      assert (a = n1) by eauto using range_list_inv_5.
      subst.
      apply range_list_cons.
      + omega.
      + inversion H0; subst; clear H0.
        apply IHl in H5; auto.
    Qed.

    Lemma range_list_inv_spec:
      forall l n1 n2,
      RangeList n1 n2 (rev l) <-> InvRangeList n1 n2 l.
    Proof.
      induction l; intros. {
        simpl; split; intros.
        + inversion H; subst; clear H.
          apply inv_range_list_empty.
          assumption.
        + inversion H; subst; clear H.
          apply range_list_empty.
          assumption.
      }
      simpl.
      split.
      - intros.
        destruct n2. {
          apply range_list_inv_2 in H.
          destruct (rev l); inversion H.
        }
        assert (a = n2) by eauto using range_list_inv_cons. 
        subst.
        apply range_list_inv_cons_2 in H.
        destruct H as (Hr, Hle).
        apply inv_range_list_cons; auto.
        apply IHl.
        assumption.
      - intros.
        assert (S a = n2). {
          inversion H; subst; clear H.
          apply IHl in H5.
          reflexivity.
        }
        subst.
        inversion H; subst; clear H.
        apply IHl in H4.
        apply range_list_succ; auto.
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

  Inductive NTypes (l: list var) : nexp -> Prop :=
  | n_types_num:
    forall n,
    NTypes l (NNum n)
  | n_types_var:
    forall v,
    List.In v l ->
    NTypes l (NVar v)
  | n_types_nbin:
    forall x y o,
    NTypes l x ->
    NTypes l y ->
    NTypes l (NBin o x y).

  Inductive RTypes l : range -> Prop :=
  | r_types_def:
    forall n1 n2,
    NTypes l n1 ->
    NTypes l n2 ->
    RTypes l (n1, n2).

  Lemma n_progress:
    forall e,
    NTypes [] e ->
    exists n, NStep e n.
  Proof.
    induction e; intros.
    - eauto using n_step_num.
    - inversion H; subst; clear H.
      contradiction.
    - inversion H; subst; clear H.
      destruct IHe1 as (n1, Hn1); auto.
      destruct IHe2 as (n2, Hn2); auto.
      eauto using n_step_bin.
  Qed.

  Lemma inv_range_list_progress:
    forall n1 n2, exists l, InvRangeList n1 n2 l.
  Proof.
    intros n1 n2; generalize dependent n1.
    induction n2; intros.
    - exists []. apply inv_range_list_empty.
      auto with *.
    - destruct (Compare_dec.le_ge_dec n1 (S n2)). {
        apply Lt.le_lt_or_eq in l.
        destruct l. {
          assert (n1 <= n2) by auto with *.
          destruct (IHn2 n1) as (l, IHl).
          exists (n2::l).
          auto using inv_range_list_cons.
        }
        subst.
        exists [].
        apply inv_range_list_empty.
        apply le_n.
      }
      exists [].
      apply inv_range_list_empty.
      assumption.
  Qed.

  Lemma range_list_progress:
    forall n1 n2, exists l, RangeList n1 n2 l.
  Proof.
    intros.
    destruct (inv_range_list_progress n1 n2) as (l, Hinv).
    exists (rev l).
    apply range_list_inv_spec.
    assumption.
  Qed.

  Lemma r_progress:
    forall r,
    RTypes [] r ->
    exists l, RStep r l.
  Proof.
    intros.
    destruct r as (e1, e2).
    inversion H; subst; clear H.
    destruct (n_progress e1) as (n1, Hn1); auto.
    destruct (n_progress e2) as (n2, Hn2); auto.
    destruct (range_list_progress n1 n2) as (l, Hr).
    exists l.
    eauto using r_step_def.
  Qed.
End SO.


