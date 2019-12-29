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
Require Conc1.

Import ListNotations.

Module C2.
  Section Defs.
  Context {A:Access}.

  Inductive inst :=
  | Skip
  | Cond: bexp -> inst -> inst
  | Acc: access_exp * nexp -> inst
  | Seq : inst -> inst -> inst
  | Decl : var -> range -> inst -> inst
  | Branch : var -> list nat -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Cond b i => Cond (b_subst x v b) (i_subst x v i)
  | Acc (a, e) => Acc (access_subst x v a, n_subst x v e)  
  | Seq i1 i2 => Seq (i_subst x v i1) (i_subst x v i2)
  | Decl y r i2 => if VAR.eq_dec x y then i else (Decl y (r_subst x v r) (i_subst x v i2)) 
  | Branch y r i2 => if VAR.eq_dec x y then i else (Branch x r (i_subst x v i2)) 
  end.

  Notation history := Hist.history.

  Definition state1 := (history * inst) % type.

  Inductive Step1: state1 -> state1 -> Prop :=
  | step_cond_true:
    forall b s i,
    BStep b true ->
    Step1 (s, (Cond b i)) (s, i)
  | step_cond_false:
    forall b s i,
    BStep b false ->
    Step1 (s, (Cond b i)) (s, Skip)
  | step_acc:
    forall s e v,
    access_step e v ->
    Step1 (s, Acc e) (v ++ s, Skip)
  | step_decl:
    forall x r p l s,
    RStep r l ->
    Step1 (s, Decl x r p) (s, Branch x l p).

  Inductive state :=
  | Empty: state
  | Leaf: (history * inst) -> state
  | Par: state -> state -> state
  | Join: state -> inst -> state.

  Inductive Step: state -> state -> Prop :=
  (* Leaf reduction *)
  | step_leaf:
    (*

      s1 --> s2
      ---------
      s1 ==> s2

     *)
    forall s1 s2,
    Step1 s1 s2 ->
    Step (Leaf s1) (Leaf s2)
  | step_seq:
    (*

      (h, i1;i2) ==> (h,i1) |> i2

     *)
    forall h i1 i2,
    Step (Leaf (h, Seq i1 i2)) (Join (Leaf (h, i1)) i2)
  (* Par reduction *)
  | step_par_l:
    (*

            s1 --> s2
      ---------------------
      s1 || s3 ==> s2 || s3

     *)
    forall s1 s2 s3,
    Step s1 s2 -> 
    Step (Par s1 s3) (Par s2 s3)
  | step_par_empty_l:
    (*

      {} || s ==> s

     *)
    forall s,
    Step (Par Empty s) s
  | step_par_empty_r:
    (*

      s || {} ==> s

     *)
    forall s,
    Step (Par s Empty) s
  | step_par_r:
    (*

                     s1 --> s2
        -----------------------------------
        (h, skip) || s1 ==> (h, skip) || s2

     *)
    forall h s1 s2,
    Step s1 s2 ->
    Step (Par (Leaf (h, Skip)) s1) (Par (Leaf (h, Skip)) s2)
  (* Join reduction *)
  | step_join_leaf:
    (*

      (h, skip) |> i ==> (h, i)

     *)
    forall h i,
    Step (Join (Leaf (h, Skip)) i) (Leaf (h, i))
  | step_join_unfold:
    (*

      (h, skip) || s  |>  i ==> (h, i)  ||  s |> i

     *)
    forall h i s,
    Step (Join (Par (Leaf (h, Skip)) s) i) (Par (Leaf (h, i)) (Join s i))
  | step_join_step:
    (*

    s1 -> s2
    -------
    s1 |> i ==> s2 |> i

     *)
    forall s1 s2 i,
    Step s1 s2 ->
    Step (Join s1 i) (Join s2 i)
  (* Branch reduction *)
  | step_branch_nil:
    (*

    (h, x \in [] p) ==> {}

     *)
    forall h x p,
    Step (Leaf (h, Branch x [] p)) Empty
  | step_branch_cons:
    forall h x n l p,
    (*
    
    (h, x \in n::l p) ==> (h, p[x=n]) || (h, x \in l p)
    
     *)
    Step
      (Leaf (h, Branch x (n::l) p))
      (Par (Leaf (h, i_subst x n p)) (Leaf (h, Branch x l p))).

  Definition step1 (s:state1) :=
  let (h, p) := s in
  match p with
  | Cond b i =>
    match b_step b with
    | Some true => Some (Leaf (h, i))
    | Some false => Some Empty
    | _ => None
    end
  | Acc e =>
    match access_eval1 e with
    | Some v => Some (Leaf (v ++ h, Skip))
    | None => None
    end
  | Decl x r p =>
    match r_step r with
    | Some l => Some (Leaf (h, Branch x l p))
    | _ => None
    end 
  | _ => None
  end.

  Fixpoint step (s:state) : option state :=
  match s with
  | Leaf (h, p) =>
    match p with
    | Cond _ _ | Acc _ | Decl _ _ _ => step1 (h, p)
    | Seq i1 i2 => Some (Join (Leaf (h, i1)) i2)
    | Branch x (n::l) p => Some (Par (Leaf (h, i_subst x n p)) (Leaf (h, Branch x l p)))
    | Branch _ [] _ => Some Empty 
    | Skip => None 
    end
  | Par s1 s2 =>
    match s1, s2 with
    | Empty, s | s, Empty => Some s
    | Leaf (_, Skip), Leaf (_, Skip) => None
    | Leaf (_, Skip), _ =>
      match step s2 with
      | Some s2 => Some (Par s1 s2)
      | None => None
      end
    | Par (Leaf s1) s2, s3 => Some (Par (Leaf s1) (Par s2 s3))
    | _, _ =>
      match step s1 with
      | Some s1 => Some (Par s1 s2)
      | None => None
      end
    end
  | Join s i =>
    match s with
    | Empty => Some Empty
    | Leaf (h, Skip) => Some (Leaf (h, i))
    | Par (Leaf (h, Skip)) s2 => Some (Par (Leaf (h, i)) (Join s2 i)) 
    | _ =>
      match step s with
      | Some s => Some (Join s i)
      | _ => None
      end
    end
  | Empty => None
  end.

  Inductive Value: state -> Prop :=
  | value_skip:
    forall h,
    Value (Leaf (h, Skip))
  | value_par:
    forall s1 s2,
    Value s1 ->
    Value s2 ->
    Value (Par s1 s2).

  Definition BStep := BigStep _ Step Value.
End Defs.
End C2.

Module Compiler.
  Import Conc1.
  Section Defs.
  Context {A:Access}.
  Variable TID_COUNT: nat.
  Variable TID : var.

  Fixpoint proj (t:nexp) (c:C1.inst) : C2.inst :=
    match c with
    | C1.Skip => C2.Skip
    | C1.Acc a => C2.Acc (a, t)
    | C1.Seq i1 i2 => C2.Seq (proj t i1) (proj t i2)
    | C1.For x r i => C2.Decl x r (proj t i)
    | C1.Loop x l i => C2.Branch x l (proj t i) 
    end.

  Variable T1: var.
  Variable T2: var.

  Definition asgn x (n:nexp) i :=
    (C2.Decl x (n, add n (NNum 1)) i).

  Definition do_proj x c :=
    asgn TID (NVar x) (proj (NVar x) c).

  Definition translate (c:C1.inst) : C2.inst :=
    C2.Decl T1 (NNum 0, NNum TID_COUNT) (
      C2.Decl T2 (NNum 0, NNum TID_COUNT) (
        C2.Cond (NRel NLt (NVar T1) (NVar T2)) (
          C2.Seq
            (do_proj T1 c)
            (do_proj T2 c)
        )
      )
    ).

(*
  Theorem soudness:
    forall c,
    C1.BStep c v ->
    C2.BStep (translate c v) w. 
*)
  End Defs.
End Compiler.

Module Examples.
  Import Compiler.
  Import C2.

  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match C2.step s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.

  Definition HELLO1 n := Leaf ([],
    Decl (variable 0) (NNum 0, NNum 2) (
      Acc ((NVar (variable 0), BBool true), n)
    )
  ).

  Definition HELLO1_VAL t :=  Par (Leaf ([{| OneDim.tid := t; OneDim.index := 0 |}], Skip))
         (Leaf ([{| OneDim.tid := t; OneDim.index := 1 |}], Skip)).

  Goal snd (run 300 (HELLO1 (NNum 9))) = HELLO1_VAL 9.
    auto.
  Qed.

  Definition HELLO2 := Leaf ([],
    Decl (variable 1) (NNum 0, NNum 2) (
    Decl (variable 0) (NNum 0, NNum 2) (
      Acc ((NVar (variable 0), BBool true), (NVar (variable 1)))
    )
    )
  ).
  
  Compute run 24 HELLO2.

  Definition HELLO3 n := Leaf ([],
    Seq (Decl (variable 0) (NNum 0, NNum 2) (
      Acc ((NVar (variable 0), BBool true), n)
    )) (Acc ((NNum 9, BBool true), NNum 9))
  ).
  
  Compute run 23 (HELLO3 (NNum 3)).


  Definition GOOD1 :=
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.GOOD1.

  Compute run 200 (Leaf ([], GOOD1)).

  Definition GOOD2 :=
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.GOOD2.

  Compute run 90 (Leaf ([], GOOD2)).

  Definition BAD := 
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.BAD.

  Compute run 300 (Leaf ([], BAD)).

End Examples.
