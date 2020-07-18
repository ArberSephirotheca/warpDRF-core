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
Require Import SymExec2.
Require LoopFree2.
Require SymHist2.

Section Compiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Fixpoint proj (c:Conc2.inst) : inst (I:=SymHist2.SymAcc) :=
    match c with
    | Conc2.Skip => Skip
    | Conc2.Seq i j => Seq (proj i) (proj j)
    | Conc2.If b i j => If b (proj i) (proj j)
    | Conc2.MemAcc a => MemAcc (I:=SymHist2.SymAcc) (a, NVar TID)
    | Conc2.For x r i => Decl x r (proj i)
    | Conc2.Loop x l i => Branch x l (proj i)
    end.

  Definition do_proj x i := i_subst TID (NVar x) (proj i).

  Definition translate c : inst :=
    Decl T1 (NNum 1, NNum TID_COUNT)
      (Decl T2 (NNum 0, NVar T1)
        (Seq (do_proj T1 c) (do_proj T2 c))).

  Lemma in_proj_to_in:
    forall x i,
    x <> TID ->
    In x (proj i) ->
    Conc2.In x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0; auto.
    + destruct H1; auto.
    + inversion H1; subst; clear H1.
      contradiction.
    + destruct H1; auto.
  Qed.

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (Conc2.i_subst x (NNum n) i) = i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
  Qed.

  End Defs.

End Compiler.
