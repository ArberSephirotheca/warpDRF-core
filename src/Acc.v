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
  Parameter subst: var -> nat -> E -> E.
  (* Prefix the access expression with an index. *)
(*  Parameter e_prefix_index: nexp -> E -> E.
  Parameter a_prefix_index: nat -> A -> A.
  *)
  Parameter AStep: (E * nexp) -> list A -> Prop.
  Parameter Safe: A -> A -> Prop.
  Axiom a_step_fun:
    forall e l1 l2,
    AStep e l1 ->
    AStep e l2 ->
    l1 = l2.
    (*
  Axiom safe_annotate:
    forall a1 a2 n,
    Safe a1 a2 <-> Safe (a_prefix_index n a1) (a_prefix_index n a2).
  *)
  (*
  Axiom progress:
    forall e,
    exists v, AStep e v.
  *) 
End ACC.

Class Access := {
  access_exp: Type;
  access_val: Type;
  access_subst: var -> nat -> access_exp -> access_exp;
  access_step: (access_exp * nexp) -> list access_val -> Prop;
  access_eval1: (access_exp * nexp) -> option (list access_val);
  access_safe: access_val -> access_val -> Prop;
  access_step_fun:
    forall e l1 l2,
    access_step e l1 ->
    access_step e l2 ->
    l1 = l2;
  access_eval1_to_step:
    forall e l,
    access_eval1 e = Some l ->
    access_step e l;
  access_step_to_eval1:
    forall e l,
    access_step e l ->
    access_eval1 e = Some l;
}.

Module Hist.
Section Defs.
  Context {A:Access}.
  Definition history := list access_val.
  Definition Safe (h:history) := forall x y, List.In x h -> List.In y h -> access_safe x y.

  Lemma safe_nil:
    Safe (@nil access_val).
  Proof.
    unfold Safe.
    intros.
    contradiction.
  Qed.
End Defs.
End Hist.


Module OneDim.

  (** One dimension *)
  Record access := {
    tid : nat;
    index: nat;
  }.

  Definition A := access.

  (** [ n ] *)

  Definition E := (nexp * bexp) % type.

  Definition subst x v (e:E) :=
    let (idx, b) := e in
    (n_subst x v idx, b_subst x v b).

  Inductive Step:  (E * nexp) -> list A -> Prop :=
  | step_true:
    forall idx b ni nt t,
    BStep b true ->
    NStep idx ni ->
    NStep t nt ->
    Step ((idx, b), t) [{| index := ni; tid := nt |}]
  | step_false:
    forall idx b t,
    BStep b false ->
    Step ((idx, b), t) [].

  Definition AStep := Step.

  Definition a_step (e:E*nexp) :=
    let (e, t) := e in
    let (idx, b) := e in
    match b_step b, n_step idx, n_step t with
    | Some true, Some ni, Some nt => Some [{| index := ni; tid:=nt|}]
    | Some false, _, _ => Some []
    | _, _, _ => None
    end.

  Lemma a_step_to_prop:
    forall e l,
    a_step e = Some l ->
    AStep e l.
  Proof.
    intros.
    destruct e as ((idx, b), t).
    simpl in *.
    destruct (b_step b) eqn:Hb; try (inversion H; fail).
    destruct b0. {
      destruct (n_step idx) eqn:Hi; try (inversion H; fail). 
      destruct (n_step t) eqn:Ht; try (inversion H; fail).
      inversion H; subst; clear H.
      apply step_true; auto using n_step_to_prop, b_step_to_prop.
    }
    inversion H; subst; clear H.
    apply step_false.
    apply b_step_to_prop; auto.
  Qed.

  Lemma prop_to_a_step:
    forall e l,
    AStep e l ->
    a_step e = Some l.
  Proof.
    intros.
    inversion H; subst; clear H; simpl. {
      apply prop_to_b_step in H0.
      apply prop_to_n_step in H1.
      apply prop_to_n_step in H2.
      rewrite H0.
      rewrite H1.
      rewrite H2.
      reflexivity.
    }
    apply prop_to_b_step in H0.
    rewrite H0.
    reflexivity.
  Qed.

  Definition Safe (a1 a2:A) :=
    tid a1 <> tid a2 /\ index a1 = index a2.

  Lemma a_step_fun:
    forall e v1 v2,
    AStep e v1 ->
    AStep e v2 ->
    v1 = v2.
  Proof.
    unfold AStep; intros.
    inversion H; subst; clear H;
      inversion H0; subst; clear H0.
    - assert (ni0 = ni) by eauto using n_step_fun.
      assert (nt0 = nt) by eauto using n_step_fun.
      subst.
      reflexivity.
    - assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - reflexivity.
  Qed.

End OneDim.

Instance ONE_DIM : Access := {|
  access_subst := OneDim.subst;
  access_step := OneDim.Step;
  access_safe := OneDim.Safe;
  access_step_fun := OneDim.a_step_fun;
  access_eval1 := OneDim.a_step;
  access_eval1_to_step := OneDim.a_step_to_prop;
  access_step_to_eval1 := OneDim.prop_to_a_step;
|}.


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