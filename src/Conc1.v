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
Require SymExe.

Import ListNotations.

Module C1.
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
    if VAR.eq_dec x y
    then For y r i2 (i_subst x v i3)
    else For y (r_subst x v r) (i_subst x v i2) (i_subst x v i3) 
  | Loop y r i2 i3 =>
    if VAR.eq_dec x y
    then Loop y r i2 (i_subst x v i3)
    else Loop x r (i_subst x v i2) (i_subst x v i3)
  | Skip => Skip
  end.

  Import Hist.

  Notation history := Hist.history.

  Definition state := (history * inst) % type.

  Variable TID_COUNT: nat.
  Variable TID : var.

  Fixpoint seq (i1 i2:inst) :=
  match i1 with
  | Skip => i2
  | Acc e i3 => Acc e (seq i3 i2)
  | For x r i3 i4 => For x r i3 (seq i4 i2)
  | Loop x r i3 i4 => Loop x r i3 (seq i4 i2)
  end.

  (** Parallelize an access for [n] tasks. *)

  Inductive Step: state -> state -> Prop :=
  | step_access:
    forall s e v i,
    GenAccess TID e TID_COUNT v ->
    Step (s, Acc e i) (List.flat_map id v ++ s, i)
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

  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, Skip).

  Definition Safe (s:state) := let (h, _) := s in Hist.Safe h.

  Definition MStep := clos_refl_trans _ Step.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Definition BStep := BigStep _ Step Value.

  Section Step2.
    Inductive Step2 (tid1 tid2:nat): state -> state -> Prop :=
    | step2_access_1:
      forall h e v1 v2 i,
      access_step (access_subst TID (NNum tid1) e, NNum tid1) v1 ->
      access_step (access_subst TID (NNum tid2) e, NNum tid2) v2 ->
      tid2 < tid1 ->
      Step2 tid1 tid2 (h, Acc e i) (v1 ++ v2 ++ h, i)
    | step2_access_2:
      forall h e v1 v2 i,
      access_step (access_subst TID (NNum tid1) e, NNum tid1) v1 ->
      access_step (access_subst TID (NNum tid2) e, NNum tid2) v2 ->
      tid1 < tid2 ->
      Step2 tid1 tid2 (h, Acc e i) (v2 ++ v1 ++ h, i)
    | step2_for:
      forall x r l h i1 i2,
      RStep r l ->
      Step2 tid1 tid2 (h, For x r i1 i2) (h, Loop x l i1 i2)
    | step2_loop_step:
      forall h x n l i1 i2,
      Step2 tid1 tid2 (h, Loop x (n::l) i1 i2) (h, seq (i_subst x (NNum n) i1) (Loop x l i1 i2))
    | step2_loop_skip:
      forall h x i1 i2,
      Step2 tid1 tid2 (h, Loop x [] i1 i2) (h, i2).

  Definition proj2 t1 t2 (s:state) := let (h, p) := s in (Hist.proj2 t1 t2 h, p).
  End Step2.

  Section Iter.
  Variable h:history.
  Fixpoint step_iter i : option state :=
    match i with
    | Acc e j =>
      match gen_access TID e TID_COUNT with
      | Some l => Some (List.flat_map id l ++ h, j) 
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

  Lemma step2_proj2:
    forall s1 s2,
    Step s1 s2 ->
    forall t1 t2,
    t1 < TID_COUNT ->
    t2 < TID_COUNT ->
    t1 <> t2 ->
    Step2 t1 t2 (proj2 t1 t2 s1) (proj2 t1 t2 s2).
  Proof.
    intros.
    induction H; simpl; try (constructor; auto; fail).
    assert (Hx := H0); assert (Hy := H1). 
    eapply gen_access_lt in H0; eauto.
    eapply gen_access_lt in H1; eauto.
    destruct H0 as (l1, (Hs1, Hi1)).
    destruct H1 as (l2, (Hs2, Hi2)).
    rewrite Hist.proj2_app.
    destruct (Hist.gen_access_proj2 _ _ _ _ H t1 t2) as [(Ha,Hb)|(Ha,Hb)]; eauto. {
      rewrite Hb.
      rewrite <- app_assoc.
      assert (R2: gen_access_item TID e t2 = l2). {
        unfold gen_access_item in *.
        apply access_step_to_eval1 in Hs2.
        rewrite Hs2 in *.
        reflexivity.
      }
      assert (R1: gen_access_item TID e t1 = l1). {
        unfold gen_access_item in *.
        apply access_step_to_eval1 in Hs1.
        rewrite Hs1 in *.
        reflexivity.
      }
      rewrite R1. rewrite R2.
      apply step2_access_2; auto.
    }
    rewrite Hb.
    rewrite <- app_assoc.
    assert (R2: gen_access_item TID e t2 = l2). {
      unfold gen_access_item in *.
      apply access_step_to_eval1 in Hs2.
      rewrite Hs2 in *.
      reflexivity.
    }
    assert (R1: gen_access_item TID e t1 = l1). {
      unfold gen_access_item in *.
      apply access_step_to_eval1 in Hs1.
      rewrite Hs1 in *.
      reflexivity.
    }
    rewrite R1. rewrite R2.
    apply step2_access_1; auto.
  Qed.

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

End C1.
End C1.

Module Examples.
  Section Defs.
  Import C1.

  Definition TID := variable "TID".

  Definition TID_NUM := 2.

  Notation b_step := (BStep TID_NUM TID).

  Infix "-->" := (Step TID_NUM TID) (at level 150).

  (* Helper function *)
  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match step TID_NUM TID s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.


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
  auto. Qed.

  (* GOOD: *)
  (*
    for x < n {
      [x] if tid == x
    }
   *)

  Infix "==" :=  (NRel NEq)  (at level 50, left associativity).
  Notation "'Var' x" := (NVar (variable x)) (at level 30).
(*  Notation "[ x ] 'if' y" := (Acc (x, y)) (at level 20).*)

  Definition GOOD1 :=
    let x := variable "x" in
    For x (NNum 0, NNum 2) (
      Acc (NVar x, NRel NEq (NVar TID) (NVar x)) Skip
    ) Skip.

  Compute GOOD1.

  Goal run 8 ([], GOOD1) =
    (6,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
    compute.
  auto. Qed.

  Definition GOOD2 :=
      Acc (NNum 9, BBool true) Skip.


  Goal run 10 ([], GOOD2) =
    (1,
    ([{| OneDim.tid := 1; OneDim.index := 9 |}; {| OneDim.tid := 0; OneDim.index := 9 |}], Skip))
    .
    compute.
  auto. Qed.


  End Defs.
End Examples.
