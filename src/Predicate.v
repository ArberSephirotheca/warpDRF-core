(**
  Implements a predicate semantics similar to what is seen in
  GPUVerify OOPSLA12.
  *)

Require Import Coq.Lists.List.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import AccExp.
Require Import Util.
Require Import Tasks.
Require Import RangeList.
Require Hist.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).

  Inductive inst :=
(*  | Skip: inst*)
  | MemAcc: access_exp -> inst
  | Seq: inst -> inst -> inst
  | If: bexp -> inst -> inst -> inst
  | For: var -> range -> inst -> inst
  | Loop: var -> list (list nat) -> inst -> inst.


  Definition shmem := list (Map_VAR.t nat).

  Definition multi_subst {A:Type} (f:var -> nexp -> A -> A) (m:Map_VAR.t nat) :=
    @Map_VAR.fold nat A (fun x v e => f x (NNum v) e) m.

  Inductive ShAdd x n : shmem -> shmem -> Prop :=
  | sh_add_nil:
    ShAdd x n [] []
  | sh_add_cons:
    forall l l' m n',
    ShAdd x n l l' ->
    NStep (multi_subst n_subst m n) n' ->
    ShAdd x n (m::l) (Map_VAR.add x n' m :: l').

  Inductive StepAccess (a:cond_access): shmem -> list (list access_val) -> Prop :=
  | gen_access_nil:
    StepAccess a [] []
  | gen_access_cons:
    forall l l' v m,
    StepAccess a l l' ->
    CStep (multi_subst cond_access_subst m a, NNum (length l)) v ->
    StepAccess a (m::l) (v::l').

  Inductive HasIter : range -> shmem -> Prop :=
  | has_iter_eq:
    forall e1 e2 n1 n2 m l,
    NStep (multi_subst n_subst m e1) n1 ->
    NStep (multi_subst n_subst m e2) n2 ->
    n1 < n2 ->
    HasIter (e1,e2) (m::l)
  | has_iter_cons:
    forall r m l,
    HasIter r l ->
    HasIter r (m::l).

  Inductive EmptyIter : range -> shmem -> Prop :=
  | can_iter_nil:
    forall r,
    EmptyIter r []
  | empty_iter_cons:
    forall e1 e2 n1 n2 m l,
    EmptyIter (e1, e2) l ->
    NStep (multi_subst n_subst m e1) n1 ->
    NStep (multi_subst n_subst m e2) n2 ->
    n1 >= n2 ->
    EmptyIter (e1,e2) (m::l)
  .
(*
  Inductive MapsToAll (x:var) : shmem -> list nat -> Prop :=
  | maps_to_all_nil:
    MapsToAll x [] []
  | maps_to_all_cons:
    forall l l' m n,
    MapsToAll x l l' ->
    Map_VAR.MapsTo x n m ->
    MapsToAll x (m::l) (n::l').

  Record valid_shmem (m:shmem) := {
    valid_shmem_1:
      List.length m = TID_COUNT
    ;
    valid_shmem_2:
      forall x,
      MapsTo x l m ->
      length l = M
  }.
*)
  Inductive Step: list (shmem * inst * bexp) * history -> list (shmem * inst * bexp) * history -> Prop :=

  | step_access:
    forall p a h v l m,
    StepAccess (a,p) m v ->
    Step ((m, MemAcc a, p)::l, h) (l, List.concat v ++ h)

  | step_seq:
    forall p h i j l m,
    Step ((m, Seq i j, p)::l, h) ((m, i, p)::(m, j, p)::l, h)

  | step_if:
    forall p b i j h l m,
    Step ((m, If b i j, p)::l, h)
         ((m, i, BRel BAnd p b)::(m, j, BRel BAnd p (BNot b))::l, h)

  | step_for_seq:
    forall n1 n2 l i x h p m m',
    HasIter (n1,n2) m ->
    ShAdd x n1 m m' ->
    Step ((m, For x (n1,n2) i,p)::l, h)
         ((m', i, (b_and p (b_and (n_le n1 (NVar x)) (n_lt (NVar x) n2))))::
          (m, For x (add (NNum 1) n1, n2) i,p)::l, h)
  | step_for_skip:
    forall n1 n2 l i x h p m,
    EmptyIter (n1,n2) m ->
    Step ((m, For x (n1,n2) i,p)::l, h)
         (l, h)
  .

End Defs.
