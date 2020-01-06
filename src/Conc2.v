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
(*  | Cond: bexp -> inst -> inst *)
  | Acc: access_exp * nexp -> inst
  | Seq : inst -> inst -> inst
  | Decl : var -> range -> inst -> inst
  | Branch : var -> list nat -> inst -> inst
  | Asgn : var -> nexp -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
(*  | Cond b i => Cond (b_subst x v b) (i_subst x v i)*)
  | Acc (a, e) => Acc (access_subst x v a, n_subst x v e)  
  | Seq i1 i2 => Seq (i_subst x v i1) (i_subst x v i2)
  | Decl y r i2 => if VAR.eq_dec x y then i else (Decl y (r_subst x v r) (i_subst x v i2)) 
  | Branch y r i2 => if VAR.eq_dec x y then i else (Branch x r (i_subst x v i2)) 
  | Asgn y n i2 => if VAR.eq_dec x y then i else (Asgn y (n_subst x v n) (i_subst x v i2)) 
  end.

  Notation history := Hist.history.

  Definition state1 := (history * inst) % type.

  Inductive state :=
  | Empty: state
  | Leaf: (history * inst) -> state
  | Par: state -> state -> state
  | Join: state -> inst -> state.

  Definition is_par p :=
  match p with
  | Par _ _ => true
  | _ => false
  end.

  Definition is_par_l_leaf s :=
   match s with
   | Par (Leaf (_, Skip)) _ => true
   | _ => false
   end.

  Inductive Step: state -> state -> Prop :=
  (* Leaf reduction *)
  | step_asgn:
    forall x e i h n,
    NStep e n ->
    Step (Leaf (h, Asgn x e i)) (Leaf (h, (i_subst x (NNum n) i)))

  | step_decl:
    forall x r p l h,
    RStep r l ->
    Step (Leaf (h, Decl x r p)) (Leaf (h, Branch x l p))

  | step_acc:
    forall h e v,
    access_step e v ->
    Step (Leaf (h, Acc e)) (Leaf (v ++ h, Skip))
(*
  | step_cond_true:
    forall b s i,
    BStep b true ->
    Step (Leaf (s, (Cond b i))) (Leaf (s, i))

  | step_cond_false:
    forall b s i,
    BStep b false ->
    Step (Leaf (s, (Cond b i))) Empty
*)
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
    is_par s1 = false ->
    Step s1 s2 -> 
    Step (Par s1 s3) (Par s2 s3)
  | step_par_empty:
    (*

      {} || s ==> s

     *)
    forall s,
    Step (Par Empty s) s
  | step_par_r:
    (*

                     s1 --> s2
        -----------------------------------
        (h, skip) || s1 ==> (h, skip) || s2

     *)
    forall h s1 s2,
    Step s1 s2 ->
    Step (Par (Leaf (h, Skip)) s1) (Par (Leaf (h, Skip)) s2)

  | step_par_par:
    forall s1 s2 s3,
    Step (Par (Par s1 s2) s3) (Par s1 (Par s2 s3))

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
    is_par_l_leaf s1 = false ->
    Step (Join s1 i) (Join s2 i)
  | step_join_empty:
    forall i,
    Step (Join Empty i) Empty
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
      (Par (Leaf (h, i_subst x (NNum n) p)) (Leaf (h, Branch x l p))).

  Definition red_par f s1 s2 :=
    match s1, s2 with
    | Empty, s => Some s
    | Par s1' s2', _ => Some (Par s1' (Par s2' s2))
    | Leaf (_, Skip), _ =>
      match f s2 with
      | Some s2 => Some (Par s1 s2)
      | None => None
      end
    | _, _ =>
      match f s1 with
      | Some s1 => Some (Par s1 s2)
      | None => None
      end
    end.

  Inductive RedPar f: state -> state -> state -> Prop :=
  | red_par_1:
    forall s,
    RedPar f Empty s s
  | red_par_2:
    forall h s1 s2,
    f s1 = Some s2 ->
    RedPar f (Leaf (h, Skip)) s1 (Par (Leaf (h, Skip)) s2)
  | red_par_3:
    forall s1 s2 s3,
    RedPar f (Par s1 s2) s3 (Par s1 (Par s2 s3))
  | red_par_4:
    forall s1 s2 s3,
    is_par s1 = false ->
    f s1 = Some s3 ->
    RedPar f s1 s2 (Par s3 s2).

  Lemma red_par_inv_some:
    forall f s1 s2 s3,
    red_par f s1 s2 = Some s3 ->
    RedPar f s1 s2 s3.
  Proof.
    unfold red_par; intros.
    destruct s1.
    - inversion H.
      clear H.
      constructor.
    - destruct p as (?, []) eqn:Hy; subst;
        destruct s2; inversion H; subst; clear H; try constructor;
        destruct (f _) eqn:Hf; inversion H1; subst; clear H1; constructor; auto;
        intros N; inversion N.
    - inversion H; subst; clear H.
      constructor.
    - destruct s2; inversion H; subst; clear H; try constructor;
        destruct (f _) eqn:Hf; inversion H1; subst; clear H1; constructor; auto;
        intros N; inversion N.
  Qed.

  Lemma some_to_red_par f (f_none: f Empty = None) (f_leaf_skip: forall h, f (Leaf (h, Skip)) = None) :
    forall s1 s2 s3,
    RedPar f s1 s2 s3 ->
    red_par f s1 s2 = Some s3.
  Proof.
    intros.
    inversion H; simpl; auto; clear H.
    - subst.
      rewrite H0.
      reflexivity.
    - subst.
      destruct s1; simpl in *; try rewrite H0; auto.
      + rewrite f_none in *.
        inversion H1.
      + destruct p as (h, []); simpl in *; destruct (f s2) eqn:He;
        try rewrite f_leaf_skip in *; try inversion H1; rewrite H2; auto.
      + inversion H0.
      + rewrite H1.
        reflexivity.
  Qed.

  Definition red_join f s i :=
    match s with
    | Empty => Some Empty
    | Leaf (h, Skip) => Some (Leaf (h, i))
    | Par (Leaf (h, Skip)) s2 => Some (Par (Leaf (h, i)) (Join s2 i)) 
    | _ =>
      match f s with
      | Some s => Some (Join s i)
      | _ => None
      end
    end.

  Inductive RedJoin f: state -> inst -> state -> Prop :=
  | red_join_1:
    forall i,
    RedJoin f Empty i Empty
  | red_join_2:
    forall h i,
    RedJoin f (Leaf (h, Skip)) i (Leaf (h, i))
  | red_join_3:
    forall h s i,
    RedJoin f (Par (Leaf (h, Skip)) s) i (Par (Leaf (h, i)) (Join s i))
  | red_join_4:
    forall s1 s2 i,
    is_par_l_leaf s1 = false ->
    f s1 = Some s2 ->
    RedJoin f s1 i (Join s2 i).

  Lemma red_join_inv_some:
    forall f s1 i s2,
    red_join f s1 i = Some s2 ->
    RedJoin f s1 i s2.
  Proof.
    unfold red_join; intros.
    destruct s1.
    - inversion H; subst.
      constructor.
    - destruct p as (h, []); inversion H; subst; clear H;
      try constructor;
      destruct (f _) eqn:He; inversion H1; subst; constructor; auto.
    - destruct s1_1; destruct (f _) eqn:He; inversion H; subst; try constructor; auto;
      destruct p as (h, p);
        destruct p; inversion H; subst; constructor; auto.
    - destruct (f _) eqn:He; inversion H; subst; constructor; auto.
  Qed.

  Lemma some_to_red_join f (f_empty: f Empty = None) (f_leaf: forall h, f (Leaf (h, Skip)) = None):
    forall s1 i s2,
    RedJoin f s1 i s2 ->
    red_join f s1 i = Some s2.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
    unfold red_join.
    destruct s1; simpl in *.
    - rewrite f_empty in *; inversion H1.
    - destruct p as (h, []); try rewrite H1; auto.
      rewrite f_leaf in *.
      inversion H1.
    - destruct s1_1; try rewrite H1; auto.
      destruct p as (h, []); auto.
      inversion H0.
    - rewrite H1; auto.
  Qed.

  Definition red_leaf (s:history * inst) :=
    let (h, p) := s in
    match p with
(*    | Cond b i =>
      match b_step b with
      | Some true => Some (Leaf (h, i))
      | Some false => Some Empty
      | None => None
      end *)
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
    | Asgn x e i =>
      match n_step e with
      | Some n => Some (Leaf (h, i_subst x (NNum n) i))
      | None => None
      end
    | Seq i1 i2 => Some (Join (Leaf (h, i1)) i2)
    | Branch x (n::l) p => Some (Par (Leaf (h, i_subst x (NNum n) p)) (Leaf (h, Branch x l p)))
    | Branch _ [] _ => Some Empty 
    | Skip => None 
    end.

  Inductive RedLeaf: (history * inst) -> state -> Prop :=
(*  | read_leaf_1:
    forall b i h,
    b_step b = Some true ->
    RedLeaf (h, Cond b i) (Leaf (h, i))
  | red_leaf_2:
    forall b i h,
    b_step b = Some false ->
    RedLeaf (h, Cond b i) Empty *)
  | red_leaf_3:
    forall h e v,
    access_eval1 e = Some v ->
    RedLeaf (h, Acc e) (Leaf (v ++ h, Skip))
  | red_leaf_4:
    forall h x r p l,
    r_step r = Some l ->
    RedLeaf (h, Decl x r p) (Leaf (h, Branch x l p))
  | red_leaf_5:
    forall h i1 i2,
    RedLeaf (h, Seq i1 i2) (Join (Leaf (h, i1)) i2)
  | red_leaf_6:
    forall h l i n x,
    RedLeaf (h, Branch x (n::l) i) (Par (Leaf (h, i_subst x (NNum n) i)) (Leaf (h, Branch x l i)))
  | red_leaf_7:
    forall h x i,
    RedLeaf (h, Branch x [] i) Empty
  | red_leaf_8:
    forall h x e i n,
    n_step e = Some n ->
    RedLeaf (h, Asgn x e i) (Leaf (h, i_subst x (NNum n) i)).

  Lemma red_leaf_inv_some:
    forall s1 s2,
    red_leaf s1 = Some s2 ->
    RedLeaf s1 s2.
  Proof.
    intros.
    destruct s1 as (h, []); simpl in *.
    - inversion H.
(*    - destruct (b_step _) eqn:Hb.
      destruct b0; inversion H; clear H; subst; try (constructor; auto).
      inversion H.*)
    - destruct (access_eval1 _) eqn:Hp; inversion H; subst; clear H.
      constructor; auto.
    - inversion H; subst; clear H.
      constructor.
    - destruct (r_step _) eqn:Hr; inversion H; subst.
      constructor; auto.
    - destruct l; inversion H; subst; constructor.
    - destruct (n_step _) eqn:Hs; inversion H; subst; constructor; auto.
  Qed.

  Fixpoint step (s:state) : option state :=
  match s with
  | Leaf s => red_leaf s
  | Par s1 s2 => red_par step s1 s2
  | Join s i => red_join step s i
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

  Theorem step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    induction s1; intros; simpl in *.
    - inversion H.
    - apply red_leaf_inv_some in H.
      inversion H; subst; clear H; constructor;
        auto using b_step_to_prop, access_eval1_to_step, r_step_to_prop, n_step_to_prop.
    - apply red_par_inv_some in H.
      inversion H; subst; clear H; try (constructor; auto).
    - apply red_join_inv_some in H.
      inversion H; subst; try constructor; auto.
  Qed.

  Theorem prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    induction s1; intros; simpl; inversion H; clear H; simpl; auto; subst.
    - apply prop_to_n_step in H1.
      rewrite H1.
      reflexivity.
    - apply prop_to_r_step in H1.
      rewrite H1.
      reflexivity.
    - apply access_step_to_eval1 in H1.
      rewrite H1.
      reflexivity.
(*    - apply prop_to_b_step in H1.
      rewrite H1.
      reflexivity.
    - apply prop_to_b_step in H1.
      rewrite H1.
      reflexivity. *)
    - apply IHs1_1 in H4.
      apply some_to_red_par; auto.
      constructor; auto.
    - apply IHs1_2 in H3.
      rewrite H3.
      reflexivity.
    - apply IHs1 in H2.
      apply some_to_red_join; auto.
      constructor; auto.
  Qed.

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

  Definition do_proj x c :=
    proj (NVar x) (C1.i_subst TID (NVar x) c).

  Definition translate (c:C1.inst) : C2.inst :=
      (C2.Decl T1 (NNum 1, NNum TID_COUNT)
        (C2.Decl T2 (NNum 0, NVar T1)
          (C2.Seq (do_proj T1 c) (do_proj T2 c))
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

  Fixpoint hists s :=
  match s with
  | Par (Leaf (h, i)) s2 => h :: hists s2
  | _ => []
  end.

  Definition run_h steps s := hists (snd (run steps s)).


  Definition HELLO1 n := Leaf ([],
    Decl (variable 0) (NNum 0, NNum 2) (
      Acc ((NVar (variable 0), BBool true), n)
    )
  ).

  Definition HELLO1_VAL t :=  Par (Leaf ([{| OneDim.tid := t; OneDim.index := 0 |}], Skip))
         (Par (Leaf ([{| OneDim.tid := t; OneDim.index := 1 |}], Skip))
          Empty).

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

  (**
  
    var t \in (0, 2) {
      var x \in (0, 2) {
        [x] by t
      }
    }
  
    *)

  
  Compute run 24 HELLO2.

  Infix "||" := Par.
  Notation "{}" := Empty.
  Notation "x 'by' y" := {| OneDim.tid := y; OneDim.index := x |} (at level 50, left associativity).


  Definition HELLO3 n := Leaf ([],
    Seq (Decl (variable 0) (NNum 0, NNum 2) (
      Acc ((NVar (variable 0), BBool true), n)
    )) (Acc ((NNum 9, BBool true), NNum 9))
  ).
  
  Compute run 17 (HELLO3 (NNum 10)).


  Definition GOOD1 :=
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.GOOD1.

  Compute GOOD1.

  Definition body x :=
    Decl (variable 1) (NNum 0, NNum 2)
        (Acc (NVar (variable 1), NRel NEq x (NVar (variable 1)), x)).

  Compute Conc1.Examples.GOOD1.
  Compute GOOD1.

  Compute run_h 40 (Leaf ([], GOOD1)). (* 39 *)

  (* ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) *)

  Definition GOOD2 :=
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.GOOD2.

  Compute run_h 17 (Leaf ([], GOOD2)). (* 12 *)

  Definition BAD := 
    translate 2 (variable 0) (variable 2) (variable 3) Conc1.Examples.BAD.
(*
  Compute BAD.
*)
  Compute (run_h 68 (Leaf ([], BAD))). (* 68 *)

  Compute hists (snd (run 68 (Leaf ([], BAD)))).
  (*
        [{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}]
  *)

End Examples.
