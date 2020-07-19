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
  (*| Loop : var -> list nat -> inst -> inst*)
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
(*  | Loop y r i =>
    let i' := if VAR.eq_dec x y then i else i_subst x v i in
    Loop y r i'*)
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
  (*| Loop y l i => x = y \/ In x i*)
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
(*  | Loop _ _ i => InRange x i*)
  end.
(*
  Lemma var_not_in_loop:
    forall x y l i,
    ~ Var x (Loop y l i) ->
    x <> y /\ ~ Var x i.
  Proof.
    intros.
    repeat split; intros N; subst; contradict H; simpl; auto.
  Qed.

  Lemma var_loop_to_for:
    forall x y i l r,
    Var x (Loop y l i) ->
    Var x (For y r i).
  Proof.
    intros.
    inversion H; subst; clear H; simpl; auto.
  Qed.

  Lemma in_loop_to_for:
    forall x y i l r,
    In x (Loop y l i) ->
    In x (For y r i).
  Proof.
    intros.
    inversion H; subst; clear H; simpl; auto.
  Qed.

  Lemma in_range_loop_to_for:
    forall x y i l r,
    InRange x (Loop y l i) ->
    InRange x (For y r i).
  Proof.
    intros.
    simpl in *; auto.
  Qed.

  Lemma var_loop_cons:
    forall x y l i n,
    Var x (Loop y l i) ->
    Var x (Loop y (n :: l) i).
  Proof.
    intros.
    inversion H; subst; clear H; simpl; auto.
  Qed.
*)
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
(*    - destruct (Set_VAR.MF.eq_dec x v). {
        reflexivity.
      }
      rewrite IHi.
      reflexivity.*)
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
      (*
    - destruct (Set_VAR.MF.eq_dec y v). {
        destruct (Set_VAR.MF.eq_dec x v). {
          subst.
          contradiction.
        }
        subst.
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        auto.
      }
      rewrite IHi; auto.*)
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; destruct H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
(*    - destruct (Set_VAR.MF.eq_dec x v); auto.*)
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
(*    - destruct (Set_VAR.MF.eq_dec x v); auto.*)
  Qed.
(*
  Lemma in_range_loop_cons:
    forall x y l i n,
    InRange x (Loop y l i) ->
    InRange x (Loop y (n :: l) i).
  Proof.
    intros.
    auto.
  Qed.
*)
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
(*    - destruct (Set_VAR.MF.eq_dec x v); auto.*)
  Qed.
(*
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
*)
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
    Run n i h1 ->
    RunAll n i h2 ->
    RunAll (S n) i (h1 ++ h2).


  Lemma run_all_inv_in:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    exists m h',
    m < n /\ Run m i h' /\ incl h' h /\ List.In x h'.
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

(*
  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, Skip).


  Definition Safe (s:state) := let (h, _) := s in Hist.Safe h.
*)
(*
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
  *)
End C1.
