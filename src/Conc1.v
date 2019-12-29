Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
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

  Inductive GenAccess a: nat -> list (list access_val) -> Prop :=
  | gen_access_zero:
    GenAccess a 0 []
  | gen_access_succ:
    forall n v l,
    GenAccess a n l ->
    access_step (access_subst TID n a, NNum  n) v ->
    GenAccess a (S n) (v::l).

  Inductive Step: state -> state -> Prop :=
  | step_acc:
    forall s e v,
    GenAccess e TID_COUNT v ->
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

  Fixpoint gen_access a n :=
    let a_step n := access_eval1 (access_subst TID n a, NNum n) in 
    match n with
    | 0 => Some []
    | S n =>
      match a_step n, gen_access a n with
      | Some v, Some l => Some (v :: l)
      | _, _ => None
      end
    end.

  Fixpoint step_iter h p : option state :=
    match p with
    | Acc e =>
      match gen_access e TID_COUNT with
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

  Definition GOOD :=
    let x := variable 1 in
    For x (NNum 0, NNum 2) (
      Acc (NVar x, NRel NEq (NVar TID) (NVar x))
    ).

  Goal run 10 ([], GOOD) =
    (8,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
    compute.
  auto. Qed.
  End Defs.
End Examples.
