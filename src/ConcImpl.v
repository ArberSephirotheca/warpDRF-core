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
Require Import Conc.
Import ListNotations.
Require Hist.
Require Import AccExpImpl.
Section C1.
  Context {A:Access}.
  Import Hist.
  Notation history := (list access_val).

  (** Parallelize an access for [n] tasks. *)

  Context `{T:Tasks}.

  Inductive Step: state -> state -> Prop :=
  | step_access:
    forall h e v i,
    GenAccess TID e TID_COUNT v ->
    Step (h, MemAcc e i) (List.concat v ++ h, i)
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

  Section Iter.
  Variable h:history.
  Definition step_iter i : option state :=
    match i with
    | MemAcc e j =>
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


  Let hello_world := MemAcc (NNum 0, BBool true) Skip.

  Goal step ([], hello_world) = Some
  ([{| OneDim.tid := 1; OneDim.index := 0 |};
   {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) .
  Proof. auto. Qed.

  (* BAD: *)
  (* for x < n {
       [tid + x] 
     } *)

  Let x := variable "x".
  Let i1 := MemAcc (add (NVar TID) (NVar x), BBool true) Skip.

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
      (MemAcc ("x" WHEN TID == "x") Skip)
    OD)
    Skip.

  Compute GOOD1.

  Goal run 8 ([], GOOD1) =
    (6,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
  Proof. auto. Qed.

  Definition GOOD2 :=
      MemAcc (NNum 9, BBool true) Skip.


  Goal run 10 ([], GOOD2) =
    (1,
    ([{| OneDim.tid := 1; OneDim.index := 9 |}; {| OneDim.tid := 0; OneDim.index := 9 |}], Skip))
    .
  Proof. compute. auto. Qed.

  End Defs.
End Examples.
