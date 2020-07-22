Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.
Require Hist.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | MemAcc: cond_access -> inst -> inst
  | For : var -> range -> inst -> inst -> inst
  | Loop : var -> list nat -> inst -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | MemAcc a i => MemAcc (cond_access_subst x v a) (i_subst x v i)  
  | For y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2' (i_subst x v i3)
  | Loop y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2' (i_subst x v i3)
  | Skip => Skip
  end.

  Import Hist.

  Notation history := (list access_val).

  Definition state := (history * inst) % type.

  Inductive In (x:var) : inst -> Prop :=
  | in_acc_1:
    forall e i,
    CIn x e ->
    In x (MemAcc e i)
  | in_acc_2:
    forall e i,
    In x i ->
    In x (MemAcc e i)
  | in_for_1:
    forall r i1 i2 y,
    RIn x r ->
    In x (For y r i1 i2)
  | in_for_2:
    forall r i1 i2,
    In x (For x r i1 i2)
  | in_for_3:
    forall r i1 i2 y,
    In x i1 ->
    In x (For y r i1 i2)
  | in_for_4:
    forall r i1 i2 y,
    In x i2 ->
    In x (For y r i1 i2)
  | in_loop_1:
    forall l i1 i2,
    In x (Loop x l i1 i2)
  | in_loop_2:
    forall l y i1 i2,
    In x i1 ->
    In x (Loop y l i1 i2)
  | in_loop_3:
    forall l y i1 i2,
    In x i2 ->
    In x (Loop y l i1 i2).

  Inductive Var (x:var) : inst -> Prop :=
  | var_acc:
    forall p i,
    Var x i ->
    Var x (MemAcc p i)
  | var_for_1:
    forall r i1 i2,
    Var x (For x r i1 i2)
  | var_for_2:
    forall r y i1 i2,
    Var x i2 ->
    Var x (For y r i1 i2)
  | var_for_3:
    forall r i1 i2 y,
    Var x i1 ->
    Var x (For y r i1 i2)
  | var_loop_1:
    forall l i1 i2,
    Var x (Loop x l i1 i2)
  | var_loop_2:
    forall y i1 i2 l,
    Var x i1 ->
    Var x (Loop y l i1 i2)
  | var_loop_3:
    forall y i1 i2 l,
    Var x i2 ->
    Var x (Loop y l i1 i2).

  Inductive InRange x : inst -> Prop := 
  | in_range_access:
    forall e i,
    InRange x i ->
    InRange x (MemAcc e i)
  | in_range_for_eq:
    forall y r i1 i2,
    RIn x r ->
    InRange x (For y r i1 i2)
  | in_range_for_l:
    forall r y i1 i2,
    InRange x i1 ->
    InRange x (For y r i1 i2)
  | in_range_for_r:
    forall r i1 i2 y,
    InRange x i2 ->
    InRange x (For y r i1 i2)
  | in_range_loop_l:
    forall y l i1 i2,
    InRange x i1 ->
    InRange x (Loop y l i1 i2)
  | in_range_loop_r:
    forall y i1 i2 l,
    InRange x i2 ->
    InRange x (Loop y l i1 i2).

  Lemma var_not_in_acc:
    forall x e i,
    ~ Var x (MemAcc e i) ->
    ~ Var x i.
  Proof.
    intros.
    intros N.
    contradict H.
    auto using var_acc.
  Qed.

  Lemma var_not_in_loop:
    forall x y l i1 i2,
    ~ Var x (Loop y l i1 i2) ->
    x <> y /\ ~ Var x i1 /\ ~ Var x i2.
  Proof.
    intros.
    repeat split; intros N; subst; contradict H;
      auto using var_loop_1, var_loop_2, var_loop_3.
  Qed.

  Lemma var_loop_to_for:
    forall x y i1 i2 l r,
    Var x (Loop y l i1 i2) ->
    Var x (For y r i1 i2).
  Proof.
    intros.
    inversion H; subst; clear H; auto using var_for_1, var_for_2, var_for_3.
  Qed.

  Lemma in_loop_to_for:
    forall x y i j l r,
    In x (Loop y l i j) ->
    In x (For y r i j).
  Proof.
    intros.
    inversion H; subst; clear H; auto using in_for_1, in_for_2, in_for_3, in_for_4.
  Qed.

  Lemma in_range_loop_to_for:
    forall x y i j l r,
    InRange x (Loop y l i j) ->
    InRange x (For y r i j).
  Proof.
    intros.
    inversion H; subst; clear H; auto using in_range_for_eq, in_range_for_l, in_range_for_r.
  Qed.

  Lemma var_loop_cons:
    forall x y l i1 i2 n,
    Var x (Loop y l i1 i2) ->
    Var x (Loop y (n :: l) i1 i2).
  Proof.
    intros.
    inversion H; subst; clear H.
    - auto using var_loop_1.
    - auto using var_loop_2.
    - auto using var_loop_3.
  Qed.

  Fixpoint seq (i1 i2:inst) :=
  match i1 with
  | Skip => i2
  | MemAcc e i3 => MemAcc e (seq i3 i2)
  | For x r i3 i4 => For x r i3 (seq i4 i2)
  | Loop x r i3 i4 => Loop x r i3 (seq i4 i2)
  end.

  Lemma in_range_inv_seq:
    forall x i j,
    InRange x (seq i j) ->
    InRange x i \/ InRange x j.
  Proof.
    induction i; simpl; intros; auto.
    - inversion H; subst; clear H.
      apply IHi in H1.
      destruct H1; auto using in_range_access.
    - inversion H; subst; clear H; eauto using in_range_for_eq, in_range_for_l.
      apply IHi2 in H1.
      destruct H1; auto using in_range_for_r.
    - inversion H; subst; clear H; auto using in_range_loop_l.
      apply IHi2 in H1.
      destruct H1; auto using in_range_loop_r.
  Qed.

  Infix ";;" := seq (at level 50).

  Lemma i_subst_seq:
    forall x n i1 i2,
    i_subst x n (i1 ;; i2) = i_subst x n i1 ;; i_subst x n i2.
  Proof.
    induction i1; simpl; intros.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi.
      rewrite cond_access_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      rewrite r_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        rewrite IHi2.
        subst.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi; auto.
      rewrite cond_access_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
      rewrite r_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        destruct (Set_VAR.MF.eq_dec x v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
  Qed.

  Lemma var_seq_inv:
    forall x i1 i2,
    Var x (seq i1 i2) ->
    Var x i1 \/ Var x i2.
  Proof.
    induction i1; simpl; intros.
    - auto.
    - inversion H; subst; clear H.
      apply IHi1 in H1.
      destruct H1; auto using var_acc.
    - inversion H; subst; clear H; auto using var_for_1, var_for_3.
      apply IHi1_2 in H1.
      destruct H1; auto using var_for_2.
    - inversion H; subst; clear H; auto using var_loop_1, var_loop_2.
      apply IHi1_2 in H1.
      destruct H1; auto using var_loop_3.
  Qed.

  Lemma in_seq_inv:
    forall x i j,
    In x (seq i j) ->
    In x i \/ In x j.
  Proof.
    induction i; simpl; intros.
    - auto.
    - inversion H; subst; clear H.
      + auto using in_acc_1.
      + apply IHi in H1.
        destruct H1; auto.
        auto using in_acc_2.
    - inversion H; subst; clear H; auto using in_for_1, in_for_2, in_for_3.
      apply IHi2 in H1.
      destruct H1; auto using in_for_4.
    - inversion H; subst; clear H; auto using in_loop_1, in_loop_2.
      apply IHi2 in H1.
      destruct H1; auto using in_loop_3.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      apply IHi in H1.
      auto using var_acc.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using var_for_1, var_for_2, var_for_3.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using var_loop_1, var_loop_2, var_loop_3.
  Qed.


  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      apply IHi in H1.
      auto using in_range_access.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using in_range_for_l, in_range_for_r.
        + apply in_r_subst_neq in H1; auto using in_range_for_eq.
          intros N.
          inversion N.
        + apply in_r_subst_neq in H1; auto using in_range_for_eq.
          intros N.
          inversion N.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using in_range_loop_l, in_range_loop_r.
  Qed.

  Lemma in_range_loop_cons:
    forall x y l i j n,
    InRange x (Loop y l i j) ->
    InRange x (Loop y (n :: l) i j).
  Proof.
    intros.
    inversion H; subst; clear H; auto using in_range_loop_l, in_range_loop_r.
  Qed.

  Lemma in_subst_inv_1:
    forall y x n i,
    In y (i_subst x (NNum n) i) ->
    In y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      + apply cond_access_in_subst_neq in H1; auto using in_acc_1.
        intros N.
        inversion N.
      + auto using in_acc_2.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using in_for_1, in_for_2, in_for_3, in_for_4.
      + apply in_r_subst_neq in H1; auto using in_for_1.
        intros N.
        inversion N.
      + apply in_r_subst_neq in H1; auto using in_for_1.
        intros N.
        inversion N.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using in_loop_1, in_loop_2, in_loop_3.
  Qed.

  Lemma var_iter_loop:
    forall x y n i1 i2 l,
    Var y (seq (i_subst x (NNum n) i1) i2) ->
    Var y (Loop x l i1 i2).
  Proof.
    intros.
    apply var_seq_inv in H.
    destruct H as [N|N]. {
      apply var_subst_inv_1 in N.
      auto using var_loop_2.
    }
    auto using var_loop_3.
  Qed.

  (** Parallelize an access for [n] tasks. *)

  Context `{T:Tasks}.

  Inductive Run: inst -> history -> Prop :=
  | run_skip:
    Run Skip []
  | run_access:
    forall i h e v,
    GenAccess TID e TID_COUNT v ->
    Run i h ->
    Run (MemAcc e i) (List.concat v ++ h)
  | run_for:
    forall r l i1 i2 x h,
    RStep r l ->
    Run (Loop x l i1 i2) h ->
    Run (For x r i1 i2) h
  | run_loop_cons:
    forall x n i1 i2 h1 h2 l,
    Run (i_subst x (NNum n) i1) h1 ->
    Run (Loop x l i1 i2) h2 ->
    Run (Loop x (n::l) i1 i2) (h1 ++ h2)
  | run_loop_nil:
    forall x i1 i2 h,
    Run i2 h ->
    Run (Loop x [] i1 i2) h.

  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, Skip).


  Definition Safe (s:state) := let (h, _) := s in Hist.Safe h.

  Lemma run_inv_loop:
    forall x l i1 i2 h,
    Run (Loop x l i1 i2) h ->
    exists h1 h2, Run (Loop x l i1 Skip) h1 /\ Run i2 h2 /\ h = h1 ++ h2. 
  Proof.
    intros.
    remember (Loop _ _ _ _).
    generalize dependent x.
    generalize dependent i1.
    generalize dependent i2.
    generalize dependent l.
    induction H; intros; try inversion Heqi; subst; try clear Heqi. {
      destruct (IHRun2 _ _ _ _ eq_refl) as (h3, (h4, (?, (?,?)))).
      subst.
      exists (h1 ++ h3).
      exists h4.
      rewrite app_assoc.
      repeat split; auto.
      constructor; auto.
    }
    exists [].
    exists h.
    split; auto.
    constructor.
    constructor.
  Qed.

  Lemma in_loop_cons:
    forall x y l i j n,
    In x (Loop y l i j) ->
    In x (Loop y (n::l) i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    - auto using in_loop_1.
    - auto using in_loop_2.
    - auto using in_loop_3.
  Qed.
  
End C1.
