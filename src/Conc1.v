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
Require Import Acc.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Acc: access_exp -> inst -> inst
  | For : var -> range -> inst -> inst -> inst
  | Loop : var -> list nat -> inst -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Acc a i => Acc (access_subst x v a) (i_subst x v i)  
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
    access_in x e ->
    In x (Acc e i)
  | in_acc_2:
    forall e i,
    In x i ->
    In x (Acc e i)
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
    Var x (Acc p i)
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

  Lemma var_not_in_acc:
    forall x e i,
    ~ Var x (Acc e i) ->
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
  | Acc e i3 => Acc e (seq i3 i2)
  | For x r i3 i4 => For x r i3 (seq i4 i2)
  | Loop x r i3 i4 => Loop x r i3 (seq i4 i2)
  end.

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
      rewrite access_subst_subst_eq.
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
      rewrite access_subst_subst_neq; auto.
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

  Inductive Step: state -> state -> Prop :=
  | step_access:
    forall h e v i,
    GenAccess TID e TID_COUNT v ->
    Step (h, Acc e i) (List.concat v ++ h, i)
  | step_for:
    forall x r h l i1 i2,
    RStep r l ->
    Step (h, For x r i1 i2) (h, Loop x l i1 i2)
  | step_loop_step:
    forall h x n l i1 i2,
    Step (h, Loop x (n::l) i1 i2) (h, seq (i_subst x (NNum n) i1) (Loop x l i1 i2))
  | step_loop_skip:
    forall h x i1 i2,
    Step (h, Loop x [] i1 i2) (h, i2).

  Inductive Run: inst -> history -> Prop :=
  | run_skip:
    Run Skip []
  | run_access:
    forall i h e v,
    GenAccess TID e TID_COUNT v ->
    Run i h ->
    Run (Acc e i) (List.concat v ++ h)
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

  Definition MStep := clos_refl_trans _ Step.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Section Iter.
  Variable h:history.
  Definition step_iter i : option state :=
    match i with
    | Acc e j =>
      match gen_access TID e TID_COUNT with
      | Some l => Some (List.concat l ++ h, j) 
      | None => None
      end
    | For x r i1 i2 =>
      match r_step r with
      | Some l => Some (h, Loop x l i1 i2)
      | None => None
      end 
    | Loop _ [] _ j => Some (h, j)
    | Loop x (n::l) i1 i2 => Some (h, seq (i_subst x (NNum n) i1) (Loop x l i1 i2))
    | Skip => None
    end.
  End Iter.

  Definition step (s:state) := let (h, p) := s in step_iter h p.

  Lemma step_iter_to_prop:
    forall i h s,
    step_iter h i = Some s ->
    Step (h, i) s.
  Proof.
    destruct i; simpl; intros.
    - inversion H.
    - destruct (gen_access _ _) eqn:Hg; inversion H; subst; clear H.
      apply gen_access_to_prop in Hg.
      auto using step_access.
    - destruct (r_step r) eqn:Hr. {
        apply r_step_to_prop in Hr.
        inversion H; subst; clear H.
        constructor; auto.
      }
      inversion H.
    - destruct l; inversion H; subst; clear H. {
        constructor.
      }
      constructor.
  Qed.

  Lemma prop_to_step_iter:
    forall i h s,
    Step (h, i) s ->
    step_iter h i = Some s.
  Proof.
    intros.
    destruct i; inversion H; subst; clear H; simpl; auto.
    - apply prop_to_gen_access in H4.
      rewrite H4.
      reflexivity.
    - apply prop_to_r_step in H6.
      rewrite H6.
      reflexivity.
  Qed.

  Lemma step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    intros.
    destruct s1 as (h, i).
    simpl in *.
    auto using step_iter_to_prop.
  Qed.

  Lemma prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    intros.
    destruct s1 as (h, i).
    apply prop_to_step_iter.
    auto.
  Qed.

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
End C1.

Module Examples.
  Section Defs.

  Instance two_tasks : Tasks.
  Proof.
    apply (Build_Tasks 2) with
      (TID:=variable "TID")
      (T1:=variable "T1")
      (T2:=variable "T2").
    - intros N; inversion N.
    - intros N; inversion N.
    - intros N; inversion N.
    - apply le_n.
  Defined.

  Notation b_step := BStep.

  Infix "-->" := Step (at level 150).

  (* Helper function *)
  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match step s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.


  Let hello_world := Acc (NNum 0, BBool true) Skip.

  Goal step ([], hello_world) = Some
  ([{| OneDim.tid := 1; OneDim.index := 0 |};
   {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) .
  Proof. auto. Qed.

  (* BAD: *)
  (* for x < n {
       [tid + x] 
     } *)

  Let x := variable "x".
  Let i1 := Acc (add (NVar TID) (NVar x), BBool true) Skip.

  Definition BAD :=
    For x (NNum 0, NNum 2) i1 Skip.


  Goal run 8 ([], BAD) =
    (6,
       ([{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip)
    ).
  Proof. auto. Qed.

  (* GOOD: *)
  (*
    for x < n {
      [x] if tid == x
    }
   *)

  Infix "==" :=  (NRel NEq)  (at level 50, left associativity).
  Notation "'Var' x" := (NVar (variable x)) (at level 30).
  Coercion NNum: nat >-> nexp.
  Coercion variable: string >-> var.
  Coercion NVar: var >-> nexp.
  Definition nrange := (nat*nat) % type.
  Definition n_range (p:nrange) : range := let (x,y) := p in (NNum x, NNum y).
  Coercion n_range: nrange >-> range.
  Notation "'FOR' x 'IN' n1 'TO' n2 'DO' i1 'OD'" := (For x (@pair nexp nexp n1 n2) i1) (at level 20).

  Infix "WHEN" := (fun x y => (@pair nexp bexp x y)) (at level 60).

  Open Scope string_scope.
  Definition GOOD1 :=
    (FOR "x" IN  0 TO 2 DO
      (Acc ("x" WHEN TID == "x") Skip)
    OD)
    Skip.

  Compute GOOD1.

  Goal run 8 ([], GOOD1) =
    (6,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
  Proof. auto. Qed.

  Definition GOOD2 :=
      Acc (NNum 9, BBool true) Skip.


  Goal run 10 ([], GOOD2) =
    (1,
    ([{| OneDim.tid := 1; OneDim.index := 9 |}; {| OneDim.tid := 0; OneDim.index := 9 |}], Skip))
    .
  Proof. compute. auto. Qed.

  End Defs.
End Examples.
