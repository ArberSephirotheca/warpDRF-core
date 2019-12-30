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

Import ListNotations.

Module C1.
Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Acc: access_exp -> inst
  | Seq : inst -> inst -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Acc a => Acc (access_subst x v a)  
  | Seq p1 p2 => Seq (i_subst x v p1) (i_subst x v p2)
  | For y r p2 => if VAR.eq_dec x y then i else (For y (r_subst x v r) (i_subst x v p2)) 
  | Loop y r p2 => if VAR.eq_dec x y then i else (Loop x r (i_subst x v p2)) 
  | Skip => Skip
  end.

  Import Hist.

  Notation history := Hist.history.

  Definition state := (history * inst) % type.

  Variable TID_COUNT: nat.
  Variable TID : var.

  (** Parallelize an access for [n] tasks. *)

  Inductive Step: state -> state -> Prop :=
  | step_access:
    forall s e v,
    GenAccess TID e TID_COUNT v ->
    Step (s, Acc e) (List.flat_map id v ++ s, Skip)
  | step_seq_step:
    forall s1 s2 p1 p2 p3,
    Step (s1, p1) (s2, p2) ->
    Step (s1, Seq p1 p3) (s2, Seq p2 p3)
  | step_seq_skip:
    forall s p,
    Step (s, Seq Skip p) (s, p)
  | step_for:
    forall x r p l s,
    RStep r l ->
    Step (s, For x r p) (s, Loop x l p)
  | step_loop_step:
    forall s x n l p,
    Step (s, Loop x (n::l) p) (s, Seq (i_subst x n p) (Loop x l p))
  | step_loop_skip:
    forall s x p,
    Step (s, Loop x [] p) (s, Skip).

  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, Skip).

  Fixpoint upper_bound n l : nat :=
  match l with
  | [] => n
  | n :: l => upper_bound n l
  end.

  Definition bounds l :=
  match l with
  | [] => (0, 0) (* should not appear *)
  | [ _ ] => (0, 0) (* should not appear *)
  | n1 :: n2 :: l => (n1, upper_bound n2 l)
  end.

  Definition Safe (s:state) := let (h, _) := s in Hist.Safe h.

  Definition MStep := clos_refl_trans _ Step.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Definition BStep := BigStep _ Step Value.

  Section Step2.
    Inductive Step2 (tid1 tid2:nat): state -> state -> Prop :=
    | step2_access_1:
      forall s e v1 v2,
      access_step (access_subst TID tid1 e, NNum tid1) v1 ->
      access_step (access_subst TID tid2 e, NNum tid2) v2 ->
      tid2 < tid1 ->
      Step2 tid1 tid2 (s, Acc e) (v1 ++ v2 ++ s, Skip)
    | step2_access_2:
      forall s e v1 v2,
      access_step (access_subst TID tid1 e, NNum tid1) v1 ->
      access_step (access_subst TID tid2 e, NNum tid2) v2 ->
      tid1 < tid2 ->
      Step2 tid1 tid2 (s, Acc e) (v2 ++ v1 ++ s, Skip)
    | step2_seq_step:
      forall s1 s2 p1 p2 p3,
      Step2 tid1 tid2 (s1, p1) (s2, p2) ->
      Step2 tid1 tid2 (s1, Seq p1 p3) (s2, Seq p2 p3)
    | step2_seq_skip:
      forall s p,
      Step2 tid1 tid2 (s, Seq Skip p) (s, p)
    | step2_for:
      forall x r p l s,
      RStep r l ->
      Step2 tid1 tid2 (s, For x r p) (s, Loop x l p)
    | step2_loop_step:
      forall s x n l p,
      Step2 tid1 tid2 (s, Loop x (n::l) p) (s, Seq (i_subst x n p) (Loop x l p))
    | step2_loop_skip:
      forall s x p,
      Step2 tid1 tid2 (s, Loop x [] p) (s, Skip).

  Definition proj2 t1 t2 (s:state) := let (h, p) := s in (Hist.proj2 t1 t2 h, p).
  End Step2.

  Fixpoint step_iter h p : option state :=
    match p with
    | Acc e =>
      match gen_access TID e TID_COUNT with
      | Some l => Some (List.flat_map id l ++ h, Skip) 
      | None => None
      end
    | Seq Skip p => Some (h, p) 
    | Seq e1 e2 =>
      match step_iter h e1 with
      | Some (h, e3) => Some (h, Seq e3 e2)
      | None => None
      end 
    | For x r p =>
      match r_step r with
      | Some l => Some (h, Loop x l p)
      | None => None
      end 
    | Loop x [] p => Some (h, Skip)
    | Loop x (n::l) p => Some (h, Seq (i_subst x n p) (Loop x l p))
    | Skip => None
    end.

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
    forall p h s,
    step_iter h p = Some s ->
    Step (h, p) s.
  Proof.
    induction p; simpl; intros.
    - inversion H.
    - destruct (gen_access _ _) eqn:Hg; inversion H; subst; clear H.
      apply gen_access_to_prop in Hg.
      auto using step_access.
    - destruct p1.
      + inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
    - destruct (r_step r) eqn:Hr; inversion H; subst; clear H.
      apply r_step_to_prop in Hr.
      constructor; auto.
    - destruct l;
      inversion H; subst; clear H;
      constructor.
  Qed.

  Lemma prop_to_step_iter:
    forall p h s,
    Step (h, p) s ->
    step_iter h p = Some s.
  Proof.
    induction p; intros; inversion H; subst; clear H; simpl; auto.
    - apply prop_to_gen_access in H3.
      rewrite H3.
      reflexivity.
    - apply IHp1 in H4.
      destruct p1; try (inversion H4; fail); rewrite H4; reflexivity.
    - apply prop_to_r_step in H5.
      rewrite H5.
      reflexivity.
  Qed.

  Lemma step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    intros.
    destruct s1 as (h, p).
    simpl in *.
    auto using step_iter_to_prop.
  Qed.

  Lemma prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    intros.
    destruct s1 as (h, p).
    apply prop_to_step_iter.
    auto.
  Qed.

End C1.
End C1.

Module Examples.
  Section Defs.
  Import C1.

  Definition TID := variable 0.

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

  Let x := variable 1.
  Let i1 := Acc (add (NVar TID) (NVar x), BBool true).
  Definition BAD :=
    For x (NNum 0, NNum 2) i1.

  Goal run 8 ([], BAD) =
    (8,
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

  Definition GOOD1 :=
    let x := variable 1 in
    For x (NNum 0, NNum 2) (
      Acc (NVar x, NRel NEq (NVar TID) (NVar x))
    ).

  Goal run 10 ([], GOOD1) =
    (8,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
    compute.
  auto. Qed.

  Definition GOOD2 :=
      Acc (NNum 9, BBool true).


  Goal run 10 ([], GOOD2) =
    (1,
    ([{| OneDim.tid := 1; OneDim.index := 9 |}; {| OneDim.tid := 0; OneDim.index := 9 |}], Skip))
    .
    compute.
  auto. Qed.

  End Defs.
End Examples.
