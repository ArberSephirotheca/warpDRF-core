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
Import ListNotations.


Module Type ACC.
  Parameter E: Type.
  Parameter A: Type.
  Parameter a_subst: var -> nat -> E -> E.
  (* Prefix the access expression with an index. *)
  Parameter e_prefix_index: E -> nexp -> E.
  Parameter a_prefix_index: A -> nat -> A.
  Parameter AStep: E -> list A -> Prop.
  Parameter Safe: A -> A -> Prop.
  Axiom a_step_fun:
    forall e l1 l2,
    AStep e l1 ->
    AStep e l2 ->
    l1 = l2.
  Axiom safe_annotate:
    forall a1 a2 n,
    Safe a1 a2 <-> Safe (a_prefix_index a1 n) (a_prefix_index a2 n).
  Axiom progress:
    forall e,
    exists v, AStep e v. 
End ACC.

Module Acc.
  Record access_exp := {
    access_exp_loc: loc;
    access_exp_index: list nexp;
    access_exp_mode : mode;
  }.

  Record access := {
    access_loc: loc;
    access_index: list nat;
    access_mode : mode; 
    access_tid : tid;
  }. 

  Inductive ModeConflict: mode -> mode -> Prop :=
  | mode_conflict_l:
    forall o,
    ModeConflict W o
  | mode_conflict_r:
    forall o,
    ModeConflict o W.

  Inductive Racy: access -> access -> Prop :=
  | racy_def:
    forall t1 t2 i m1 m2 l,
    t1 <> t2 ->
    ModeConflict m1 m2 ->
    Racy {| access_loc := l; access_index := i; access_mode := m1; access_tid := t1 |}
         {| access_loc := l; access_index := i; access_mode := m2; access_tid := t2 |}.

  Inductive SafeAcc: access -> access -> Prop :=
  | safe_acc_neq_loc:
    forall l1 l2 t1 t2 m1 m2 i1 i2,
    l1 <> l2 ->
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := m2; access_index := i2 |}
  | safe_acc_eq_task:
    forall t m1 m2 i1 i2 l1 l2,
    SafeAcc {| access_loc := l1; access_tid := t; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t; access_mode := m2; access_index := i2 |}
  | safe_acc_read:
    forall t1 t2 i1 i2 l1 l2,
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := R; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := R; access_index := i2 |}
  | safe_acc_neq_index:
    forall t1 t2 i1 i2 m1 m2 l1 l2,
    i1 <> i2 ->
    SafeAcc {| access_loc := l1; access_tid := t1; access_mode := m1; access_index := i1 |}
            {| access_loc := l2; access_tid := t2; access_mode := m2; access_index := i2 |}.

  Section Add.

    Fixpoint eval_acc l i m (tids:list tid) : list access :=
    match tids with
    | [] => []
    | t :: tids =>
      {| access_loc := l; access_tid := t; access_mode := m; access_index := i |}
      :: eval_acc l i m tids
    end.

    Variable tids: list tid.

    Inductive AStep: access_exp -> list access -> Prop :=
    | a_step_def:
      forall i l m n,
      IStep i n -> 
      AStep {| access_exp_loc := l; access_exp_index := i; access_exp_mode := m; |}
            (eval_acc l n m tids).

  End Add.
End Acc.