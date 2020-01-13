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

    Inductive StepProj (tid:nat): state -> state -> Prop :=
    | step_proj_access:
      forall h e v i,
      access_step (access_subst TID (NNum tid) e, NNum tid) v ->
      StepProj tid (h, Acc e i) (v ++ h, i)
    | step_proj_for:
      forall x r l h i1 i2,
      RStep r l ->
      StepProj tid (h, For x r i1 i2) (h, Loop x l i1 i2)
    | step_proj_loop_step:
      forall h x n l i1 i2,
      StepProj tid (h, Loop x (n::l) i1 i2) (h, seq (i_subst x (NNum n) i1) (Loop x l i1 i2))
    | step_proj_loop_skip:
      forall h x i1 i2,
      StepProj tid (h, Loop x [] i1 i2) (h, i2).

  Definition proj2 t1 t2 (s:state) := let (h, p) := s in (Hist.proj2 t1 t2 h, p).
  Definition proj t (s:state) := let (h, p) := s in (Hist.proj t h, p).

  End Step2.

  Definition BStep2 T1 T2 := BigStep _ (Step2 T1 T2) Value.

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
(*
  Lemma step_to_step_proj:
    forall s1 s2,
    Step s1 s2 ->
    forall t1,
    t1 < TID_COUNT ->
    StepProj t1 (proj t1 s1) (proj t1 s2).
  Proof.
    intros.
    induction H; simpl; try (constructor; auto; fail).
    edestruct gen_access_lt as (l, (Hs, Hi)); eauto.
    rewrite Hist.proj_app.
    assert (R: Hist.proj t1 l = l). {
      apply proj_id in Hs.
      assumption.
    }
    eapply gen_access_proj_lt in H; eauto.
    rewrite H.
    unfold gen_access_item.
    assert (R1 := Hs).
    apply access_step_to_eval1 in R1.
    rewrite R1.
    constructor.
    assumption.
  Qed.
*)
  Axiom tid_nonempty: TID_COUNT > 0.

  Lemma tid_exists:
    exists t, t < TID_COUNT.
  Proof.
    assert (Hx := tid_nonempty).
    destruct TID_COUNT. {
      inversion Hx.
    }
    eauto with *.
  Qed.

  Definition step_hist p :=
    match p with
    | Acc e _ =>
      match gen_access TID e TID_COUNT with
      | Some v => flat_map id v
      | None => []
      end
    | Skip
    | For _ _ _ _ 
    | Loop _ _ _ _ => []
    end.
  Definition step_prog i :=
    match i with
    | Acc _ i => i
    | For x r i1 i2 =>
      match r_step r with
      | Some l => Loop x l i1 i2
      | None => Skip
      end
    | Loop _ [] _ i => i
    | Loop x (n::l) i1 i2 => seq (i_subst x (NNum n) i1) (Loop x l i1 i2)
    | Skip => Skip
    end.

  Lemma step_inv_state:
    forall h p s,
    Step (h, p) s ->
    s = (step_hist p ++ h, step_prog p).
  Proof.
    intros.
    destruct p; simpl; inversion H; subst; clear H.
    - apply prop_to_gen_access in H4.
      rewrite H4.
      reflexivity.
    - apply prop_to_r_step in H6.
      rewrite H6.
      reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma step_proj_to_step:
    forall h p,
    (forall t1, t1 < TID_COUNT -> StepProj t1 (Hist.proj t1 h, p) (Hist.proj t1 (step_hist p ++ h), step_prog p)) ->
    Step (h, p) (step_hist p ++ h, step_prog p).
  Proof.
    intros.
    destruct tid_exists as (t1, Hlt).
    assert (Hx := H _ Hlt).
    destruct p; simpl; inversion Hx; subst; clear Hx.
    - assert (Hx := H1).
      apply access_step_to_gen_access with (m:=TID_COUNT) in H1; auto; destruct H1 as (l, Hl).
      assert (Hg := Hl).
      apply prop_to_gen_access in Hl.
      rewrite Hl in *.
      rewrite Hist.proj_app in H4.
      constructor.
      assumption.
    - destruct (r_step _) eqn:Hs; inversion H6; subst; clear H6.
      apply r_step_to_prop in Hs.
      constructor; assumption.
    - constructor.
    - constructor.
  Qed.

  Lemma step_to_step_proj:
    forall h p,
    Step (h, p) (step_hist p ++ h, step_prog p) ->
    forall t1,
    t1 < TID_COUNT ->
    StepProj t1 (Hist.proj t1 h, p) (Hist.proj t1 (step_hist p ++ h), step_prog p).
  Proof.
    intros.
    inversion H; subst; clear H; simpl.
    - assert (Hg := H2).
      apply prop_to_gen_access in H2.
      rewrite H2 in *.
      rewrite Hist.proj_app.
      erewrite gen_access_proj_lt; eauto.
      unfold gen_access_item.
      eapply gen_access_to_access_step_lt in Hg; eauto.
      destruct Hg as (l, Ha).
      apply access_step_to_eval1 in Ha.
      rewrite Ha.
      constructor.
      apply access_eval1_to_step in Ha.
      assumption.
    - assert (Hx := H2).
      apply prop_to_r_step in Hx.
      rewrite Hx in *.
      inversion H4; subst; clear H4.
      constructor.
      assumption.
    - constructor.
    - constructor.
  Qed.

  Definition RedProj t1 h p :=
    StepProj t1 (Hist.proj t1 h, p) (Hist.proj t1 (step_hist p ++ h), step_prog p).

  Definition Red h p := Step (h, p) (step_hist p ++ h, step_prog p).

  Definition RedSafe h p := Safe (step_hist p ++ h, step_prog p).

  Definition RedProjSafe t1 t2 h p := Safe2 (Hist.proj t1 (step_hist p ++ h)) (Hist.proj t2 (step_hist p ++ h)).

  Lemma red_proj_iff_red:
    forall h p,
    (forall t1, t1 < TID_COUNT -> RedProj t1 h p) <-> Red h p.
  Proof.
    unfold Red, RedProj; split; intros;
      auto using step_proj_to_step, step_to_step_proj.
  Qed.

  Lemma red_safe_to_red_proj_safe:
    forall h p t1 t2,
    Red h p ->
    RedSafe h p ->
    t1 < TID_COUNT ->
    t2 < TID_COUNT ->
    t1 <> t2 ->
    RedProjSafe t1 t2 h p.
  Proof.
    unfold RedSafe, RedProjSafe, Red; intros.
    inversion H; subst; clear H.
    - simpl in *.
      erewrite prop_to_gen_access in *; eauto.
      edestruct gen_access_to_access_step_lt with (m:=t1) as (l1, Ha1); eauto.
      edestruct gen_access_to_access_step_lt with (m:=t2) as (l2, Ha2); eauto.
      repeat rewrite proj_app.
      erewrite gen_access_proj_rw; eauto.
      erewrite gen_access_proj_rw; eauto.
      simpl.
  Qed.

  Theorem step_proj_spec:
    forall h p,
    Red h p /\ RedSafe h p
    <->
    (forall t1 t2, t1 < TID_COUNT -> t2 < TID_COUNT -> t1 <> t2 ->
      RedProj t1 h p /\ RedProj t2 h p /\ RedProjSafe t1 t2 h p).
  Proof.
    split; intros.
    - destruct H as (Hr, Hs).
      repeat split.
      + apply red_proj_iff_red; assumption.
      + apply red_proj_iff_red; assumption.
      + 
      repeat split; auto using step_to_step_proj.
      destruct s2 as (h2, p2); simpl.
      unfold Safe2.
      intros.
      apply Hist.in_proj_inv in H.
      apply Hist.in_proj_inv in H3.
      destruct H as (Hi1, He1).
      destruct H3 as (Hi2, He2).
      subst.
      eauto.
    - 
  Qed.

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

Module C1SX.
Section Defs.
  Import SymExe.
  Context {A:Access}.
  Definition t := (Hist.history * C1.inst) % type.
  Variable TID_COUNT: nat.
  Variable TID: var.

  Inductive Red: t -> list t -> Prop :=
  | red_acc:
    forall e v h c, 
    Hist.GenAccess TID e TID_COUNT v ->
    Red (h, C1.Acc e c) [(List.flat_map id v ++ h, c)]
  | red_for:
    forall h x r l c1 c2,
    RStep r l ->
    Red (h, C1.For x r c1 c2) [(h, C1.Loop x l c1 c2)]
  | red_branch_cons:
    forall h l c1 c2 n x,
    Red (h, C1.Loop x (n::l) c1 c2) [(h, C1.i_subst x (NNum n) c1); (h, C1.Loop x l c1 c2) ]
  | red_branch_nil:
    forall h x c1 c2,
    Red (h, C1.Loop x [] c1 c2) [(h, c2)].

  Definition is_value (s:t) :=
    let (h, p) := s in
    match p with
    | C1.Skip => true
    | _ => false
    end.

  Definition red (s:t) :=
  let (h, c) := s in
  match c with
  | C1.Acc e c =>
    match Hist.gen_access TID e TID_COUNT with
    | Some l => Some [(List.flat_map id l ++ h, c)]
    | None => None
    end
  | C1.For x r c1 c2 =>
    match r_step r with
    | Some l => Some [(h, C1.Loop x l c1 c2)]
    | _ => None
    end
  | C1.Loop x (n::l) c1 c2 => Some [(h, C1.i_subst x (NNum n) c1); (h, C1.Loop x l c1 c2)]
  | C1.Loop _ [] _ c => Some [(h,c)]
  | C1.Skip => None
  end.

  Lemma red_to_prop:
    forall a s,
    red a = Some s -> Red a s.
  Proof.
    intros.
    destruct a as (h, i).
    simpl in *.
    destruct i.
    - inversion H.
    - destruct (Hist.gen_access _ _ _) eqn:Hg; inversion H; subst.
      constructor; auto using Hist.gen_access_to_prop.
    - destruct (r_step r) eqn:Hr; inversion H; subst; clear H.
      constructor; auto using r_step_to_prop.
    - destruct l; inversion H; constructor.
  Qed.

  Lemma prop_to_red:
    forall a s,
    Red a s ->
    red a = Some s.
  Proof.
    intros.
    destruct a as (h, []); simpl; inversion H; subst; clear H; auto.
    - apply Hist.prop_to_gen_access in H4.
      rewrite H4.
      reflexivity.
    - apply prop_to_r_step in H6.
      rewrite H6.
      reflexivity.
  Qed.

  Lemma red_to_value_false:
    forall a s,
    red a = Some s ->
    is_value a = false.
  Proof.
    intros.
    destruct a as (h, []); simpl in *; auto.
    inversion H.
  Qed.

  Lemma value_true_to_leaf:
    forall a, is_value a = true -> red a = None.
  Proof.
    intros.
    destruct a as (h, []); inversion H.
    auto.
  Qed.

  Instance C1_Lang : Lang t := {
    AStep := Red;
    a_is_value := is_value;
    red_leaf := red;
    red_leaf_to_a_step := red_to_prop;
    a_step_to_red_leaf := prop_to_red;
    step_to_is_value_false := red_to_value_false;
    (*step_is_value_true := value_true_to_leaf;*)
  }.
End Defs.

Module Examples.
  Definition TID := variable "TID".

  Definition TID_NUM := 2.  
  Definition step := @SymExe.step _ (C1_Lang TID_NUM TID).
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

  Let i1 := C1.Acc (add (NVar TID) (NVar (variable "x")), BBool true) C1.Skip.
  Definition BAD :=
    C1.For (variable "x") (NNum 0, NNum 2) i1 C1.Skip.

  Compute run 8 [([], BAD)].

  Definition GOOD1 :=
    let x := variable "x" in
    C1.For x (NNum 0, NNum 2) (
      C1.Acc (NVar x, NRel NEq (NVar TID) (NVar x)) C1.Skip
    ) C1.Skip.

  Compute run 8 [([], GOOD1)].

End Examples.


End C1SX.

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
