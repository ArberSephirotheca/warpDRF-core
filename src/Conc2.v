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
Require Import Exp.
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.
Require Hist.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip: inst
  | If: bexp -> inst -> inst -> inst
  | Seq: inst -> inst -> inst
  | MemAcc: access_exp -> inst
  | For : var -> range -> inst -> inst
  .

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | If b i j => If (b_subst x v b) (i_subst x v i) (i_subst x v j)
  | Seq i j => Seq (i_subst x v i) (i_subst x v j)
  | MemAcc a => MemAcc (access_subst x v a)  
  | For y r i =>
    let i' := if VAR.eq_dec x y then i else i_subst x v i in
    For y (r_subst x v r) i'
  end.

  Import Hist.

  Notation history := (list access_val).

  Fixpoint In (x:var) i :=
  match i with
  | Skip => False
  | MemAcc e => access_in x e
  | If b i j => BIn x b \/ In x i \/ In x j
  | Seq i j => In x i \/ In x j
  | For y r i => x = y \/ RIn x r \/ In x i
  end.

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => Var x i \/ Var x j
  | For y _ i (*| Loop y _ i*) => x = y \/ Var x i
  end.

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => InRange x i \/ InRange x j
  | For _ r i => RIn x r \/ InRange x i
  end.

  Infix ";;" := Seq (at level 50).

  Lemma i_subst_seq:
    forall x n i1 i2,
    i_subst x n (i1 ;; i2) = i_subst x n i1 ;; i_subst x n i2.
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_eq.
      reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi.
      rewrite r_subst_subst_eq.
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
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_neq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi; auto.
      rewrite r_subst_subst_neq; auto.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; destruct H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_r_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_subst_inv_1:
    forall y x n i,
    In y (i_subst x (NNum n) i) ->
    In y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_b_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct H; auto.
    - eapply access_in_subst_neq; eauto.
      intros N.
      inversion N.
    - destruct H; auto.
      + apply in_r_subst_neq in H; eauto.
        intros N.
        inversion N.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (** Parallelize an access for [n] tasks. *)

  Context `{T:Tasks}.
  Inductive Run (n:nat) : inst -> history -> Prop :=
  | run_skip:
    Run n Skip []
  | run_access:
    forall e v,
    access_step (e, NNum n) v ->
    Run n (MemAcc e) v
  | run_seq:
    forall i j h1 h2,
    Run n i h1 ->
    Run n j h2 ->
    Run n (Seq i j) (h1 ++ h2)
  | run_if_true:
    forall i j b h,
    BStep b true ->
    Run n i h ->
    Run n (If b i j) h
  | run_if_false:
    forall i j b h,
    BStep b false ->
    Run n j h ->
    Run n (If b i j) h
  | run_for_cons:
    forall e1 e2 n1 n2 i x h1 h2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run n (i_subst x (NNum n1) i) h1 ->
    Run n (For x (NNum (S n1), NNum n2) i) h2 ->
    Run n (For x (e1, e2) i) (h1 ++ h2)
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run n (For x (e1, e2) i) [].

  Inductive RunAll : nat -> inst -> history -> Prop :=
  | run_all_zero:
    forall i,
    RunAll 0 i []
  | run_all_succ:
    forall i n h1 h2,
    Run n (i_subst TID (NNum n) i) h1 ->
    RunAll n i h2 ->
    RunAll (S n) i (h1 ++ h2).

  Inductive Run2 (n1 n2:nat): inst -> history -> history -> Prop :=
  | run2_skip:
    Run2 n1 n2 Skip [] []

  | run2_access:
    forall e v1 v2,
    access_step (access_subst TID (NNum n1) e, NNum n1) v1 ->
    access_step (access_subst TID (NNum n2) e, NNum n2) v2 ->
    Run2 n1 n2 (MemAcc e) v1 v2

  | run2_seq:
    forall i j hi1 hj1 hi2 hj2,
    Run2 n1 n2 i hi1 hi2 ->
    Run2 n1 n2 j hj1 hj2 ->
    Run2 n1 n2 (Seq i j) (hi1 ++ hj1) (hi2 ++ hj2)

  | run2_if:
    forall i j b b1 b2 hi1 hi2 hj1 hj2,
    BStep (b_subst TID (NNum n1) b) b1 ->
    BStep (b_subst TID (NNum n2) b) b2 ->
    Run2 n1 n2 i hi1 hi2 ->
    Run2 n1 n2 j hj1 hj2 ->
    Run2 n1 n2 (If b i j) (if b1 then hi1 else hj1) (if b2 then hi2 else hj2)

  | run2_for:
    forall e1 e2 i x h1 h2,
    Run2 n1 n2 (If (NRel NLt e1 e2)
      (Seq (i_subst x e1 i) (For x (NBin NPlus (NNum 1) e1, e2) i))
      Skip) h1 h2 ->
    Run2 n1 n2 (For x (e1, e2) i) h1 h2.

  Lemma run_all_inv_in:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    exists m h',
    m < n /\ Run m (i_subst TID (NNum m )i) h' /\ incl h' h /\ List.In x h'.
  Proof.
    intros n i h H.
    induction H; intros. { contradiction. }
    apply in_app_or in H1.
    destruct H1.
    - exists n.
      exists h1.
      eauto using InUtil.incl_app_refl_l with *.
    - edestruct IHRunAll as (m, (h, (Hl, (Hr, (Hi,Hj))))); eauto.
      exists m.
      exists h.
      auto using incl_appr with *.
  Qed.

End C1.
