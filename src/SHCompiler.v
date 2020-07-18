Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Sets.Ensembles.
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
Require Conc.
Require Import SetTh.
Import ListNotations.
Require Import RangeList.
Require Import Tasks.
Require Import SymExec.
Require LoopFree.
Require SymHist.

Section Compiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Fixpoint proj (c:inst (I:=LoopFree.LoopAcc)) : inst (I:=SymHist.SymAcc) :=
    match c with
    | Skip => Skip
    | MemAcc a c1 => MemAcc (I:=SymHist.SymAcc) (a, NVar TID) (proj c1)
    | Decl x r c1 c2 => Decl x r (proj c1) (proj c2)
    | Branch x l c1 c2 => Branch x l (proj c1) (proj c2)
    | Fork i j => Fork (proj i) (proj j)
    end.

  Definition do_proj x i := i_subst TID (NVar x) (proj i).

  Definition translate (c:inst) : inst :=
      (Decl T1 (NNum 1, NNum TID_COUNT)
        (Decl T2 (NNum 0, NVar T1)
          (seq (do_proj T1 c) (do_proj T2 c))
        Skip)
      Skip).

  Fixpoint split (c:inst (I:=LoopFree.LoopAcc)) : inst (I:=SymHist.SymAcc) :=
    match c with
    | Skip => Skip
    | MemAcc a c =>
      MemAcc (I:=SymHist.SymAcc) (a, NVar T1)
        (MemAcc (I:=SymHist.SymAcc) (a, NVar T2) (split c))
    | Decl x r c1 c2 => Decl x r (split c1) (split c2)
    | Branch x l c1 c2 => Branch x l (split c1) (split c2)
    | Fork i j => Fork (split i) (split j)
    end.

  Definition X_translate (c:inst) : inst :=
      (Decl T1 (NNum 1, NNum TID_COUNT)
        (Decl T2 (NNum 0, NVar T1)
          (split c)
        Skip)
      Skip).

  Lemma in_proj_to_in:
    forall x i,
    x <> TID ->
    In x (proj i) ->
    In x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0;
      auto using
        in_acc_1,
        in_acc_2,
        in_decl_1,
        in_decl_2,
        in_decl_3,
        in_decl_4,
        in_branch_1,
        in_branch_2,
        in_branch_3,
        in_fork_1,
        in_fork_2.
    apply in_acc_1.
    simpl in *.
    destruct H2 as [Hx|Hx]; auto.
    inversion Hx; subst; clear Hx.
    contradiction.
  Qed.

  Lemma proj_seq:
    forall i j,
    proj (seq i j) = seq (proj i) (proj j).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
    - rewrite IHi1;
      rewrite IHi2.
      reflexivity.
  Qed.

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (i_subst x (NNum n) i) = i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  End Defs.

End Compiler.
(*
Module Examples.
  Import SymHist.
  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match SymHist.step s with
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
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    )
    Skip
  ).

  Definition HELLO1_VAL t :=  Par (Leaf ([{| OneDim.tid := t; OneDim.index := 0 |}], Skip))
         (Par (Leaf ([{| OneDim.tid := t; OneDim.index := 1 |}], Skip))
          Empty).

  Goal snd (run 300 (HELLO1 (NNum 9))) = HELLO1_VAL 9.
    auto.
  Qed.

  Definition HELLO2 := Leaf ([],
    Decl (variable "tid") (NNum 0, NNum 2) (
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), (NVar (variable "tid"))) Skip
    ) Skip
    )
    Skip
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
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    ) (Acc ((NNum 9, BBool true), NNum 9) Skip)
  ).
  
  Compute run 17 (HELLO3 (NNum 10)).


  Definition GOOD1 :=
    translate 2 Conc.Examples.TID (variable "T1") (variable "T2") Conc.Examples.GOOD1.

  Compute GOOD1.

  Definition body x :=
    Decl (variable "x") (NNum 0, NNum 2)
        (Acc (NVar (variable "x"), NRel NEq x (NVar (variable "x")), x) Skip) Skip.

  Compute Conc.Examples.GOOD1.
  Compute GOOD1.

  Compute run_h 40 (Leaf ([], GOOD1)). (* 39 *)

  (* ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) *)

  Definition GOOD2 :=
    translate 2 Conc.Examples.TID (variable "T1") (variable "T2") Conc.Examples.GOOD2.

  Compute run 10 (Leaf ([], GOOD2)). (* 10 *)

  Definition BAD := 
    translate 2 Conc.Examples.TID (variable "T1") (variable "T2") Conc.Examples.BAD.
(*
  Compute BAD.
*)
  Compute (run_h 36 (Leaf ([], BAD))). (* 35 *)

  Compute hists (snd (run 36 (Leaf ([], BAD)))).
  (*
        [{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}]
  *)

End Examples.
*)