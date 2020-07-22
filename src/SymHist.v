Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Arith.PeanoNat.
Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Conc.
Require Import RangeList.
Require Import SetTh.
Require Import MultiHist.
Require Import InUtil.
Require Import MExp.
Import ListNotations.
Import MHistNotations.
Require Import SymExec.
Section Defs.
  Context {A:Access}.

  Definition s_subst (x:var) (v:nexp) (p:cond_access * nexp) :=
    let (e, n) := p in 
    (cond_access_subst x v e, n_subst x v n)
  .

  Definition SIn x (p:cond_access * nexp) :=
    let (e, n) := p in
    CIn x e \/ NIn x n
  .

  Lemma s_subst_subst_eq:
    forall x n1 n2 a,
    s_subst x (NNum n1) (s_subst x (NNum n2) a) =
    s_subst x (NNum n2) a.
  Proof.
    intros x n1 n2 (e, n).
    simpl.
    rewrite cond_access_subst_subst_eq.
    rewrite n_subst_subst_eq.
    reflexivity.
  Qed.

  Lemma s_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    s_subst x (NNum n1) (s_subst y (NNum n2) a) =
    s_subst y (NNum n2) (s_subst x (NNum n1) a).
  Proof.
    intros x y n1 n2 (e, n) Hn.
    simpl.
    rewrite cond_access_subst_subst_neq; auto.
    rewrite n_subst_subst_neq; auto.
  Qed.

  Lemma s_subst_subst_neq_2:
    forall x y z n i,
    x <> z ->
    y <> z ->
    s_subst x (NVar y) (s_subst z (NNum n) i) =
    s_subst z (NNum n) (s_subst x (NVar y) i).
  Proof.
    intros x y z n (e, n2) Hn1 Hn2.
    simpl.
    rewrite cond_access_subst_subst_neq_2; auto.
    rewrite n_subst_subst_neq_2; auto.
  Qed.

  Lemma s_subst_not_in:
    forall x e v,
    ~ SIn x e ->
    s_subst x v e = e.
  Proof.
    intros x (e, n) v Hn.
    simpl in *.
    rewrite cond_access_subst_not_in; auto.
    rewrite n_subst_not_in; auto.
  Qed.

  Lemma s_subst_subst_trans:
    forall e x v y,
    ~ SIn x e ->
    s_subst x v (s_subst y (NVar x) e) =
    s_subst y v e.
  Proof.
    intros (e, n); simpl; intros.
    rewrite cond_access_subst_subst_trans; auto.
    rewrite n_subst_subst_trans; auto.
  Qed.

  Lemma s_in_subst_neq:
    forall e x y v,
    SIn x (s_subst y v e) ->
    ~ NIn x v ->
    SIn x e.
  Proof.
    intros (e, n); simpl; intros.
    destruct H as [H|H].
    - eauto using cond_access_in_subst_neq.
    - eauto using in_n_subst_neq.
  Qed.

  Instance SymAcc : AccessInst := {
    access_inst_type := (cond_access * nexp) % type ;
    access_inst_subst := s_subst;
    access_inst_step := CStep;
    access_inst_in := SIn;
    access_inst_step_fun := c_step_fun;
    access_inst_subst_subst_eq := s_subst_subst_eq;
    access_inst_subst_subst_neq := s_subst_subst_neq;
    access_inst_subst_subst_neq_2 := s_subst_subst_neq_2;
    access_inst_subst_not_in := s_subst_not_in;
    access_inst_subst_subst_trans := s_subst_subst_trans;
    access_inst_in_subst_neq := s_in_subst_neq;
  }.

End Defs.

