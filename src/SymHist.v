Require Import Coq.Lists.List.

Require Coq.omega.Omega.

Require Import Util.
Require Import InUtil.

Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AccExp.

Require Import SymExec.
Require Conc.

Import ListNotations.

Section Defs.
  Context {A:Access}.

  Definition s_subst (x:var) (v:nexp) (p:access_exp * nexp) :=
    let (e, n) := p in 
    (access_subst x v e, n_subst x v n)
  .

  Definition SFree (p:access_exp * nexp) x :=
    let (e, n) := p in
    AFree e x \/ NFree n x
  .

  Lemma s_subst_subst_eq:
    forall x n1 n2 a,
    s_subst x (NNum n1) (s_subst x (NNum n2) a) =
    s_subst x (NNum n2) a.
  Proof.
    intros x n1 n2 (e, n).
    simpl.
    rewrite access_subst_subst_eq.
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
    rewrite access_subst_subst_neq; auto.
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
    rewrite access_subst_subst_neq_2; auto.
    rewrite n_subst_subst_neq_2; auto.
  Qed.

  Lemma s_subst_not_in:
    forall x e v,
    ~ SFree e x ->
    s_subst x v e = e.
  Proof.
    intros x (e, n) v Hn.
    simpl in *.
    rewrite access_subst_not_free; auto.
    rewrite n_subst_not_free; auto.
  Qed.

  Lemma s_subst_subst_trans:
    forall e x v y,
    ~ SFree e x ->
    s_subst x v (s_subst y (NVar x) e) =
    s_subst y v e.
  Proof.
    intros (e, n); simpl; intros.
    rewrite access_subst_subst_trans; auto.
    rewrite n_subst_subst_trans; auto.
  Qed.

  Lemma s_free_subst_neq:
    forall e x y v,
    SFree (s_subst y v e) x ->
    ~ NFree v x ->
    SFree e x.
  Proof.
    intros (e, n); simpl; intros.
    destruct H as [H|H].
    - eauto using access_in_subst_neq.
    - eauto using n_free_subst_neq.
  Qed.

  Instance SymAcc: AccessInst := {
    access_inst_type := (access_exp * nexp) % type ;
    access_inst_subst := s_subst;
    access_inst_step := access_step;
    SFree := SFree;
    access_inst_step_fun := access_step_fun;
    access_inst_subst_subst_eq := s_subst_subst_eq;
    access_inst_subst_subst_neq := s_subst_subst_neq;
    access_inst_subst_subst_neq_2 := s_subst_subst_neq_2;
    access_inst_subst_not_free := s_subst_not_in;
    access_inst_subst_subst_trans := s_subst_subst_trans;
    access_inst_in_subst_neq := s_free_subst_neq;
  }.
  Variable CurTask : nat.
  Fixpoint translate (i:Conc.inst) : SymExec.inst (I:=SymAcc) :=
    match i with
    | Conc.Skip => SymExec.Skip
    | Conc.Seq i j => SymExec.Seq (translate i) (translate j)
    | Conc.If b i j => SymExec.If b (translate i) (translate j)
    | Conc.MemAcc e => SymExec.MemAcc (I:=SymAcc) (e, NNum CurTask)
    | Conc.For x r i => SymExec.Decl x r (translate i)
    end.

  Lemma i_subst_translate_rw:
    forall i x n,
    i_subst x n (translate i) =
    translate (Conc.i_subst x n i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - reflexivity.
    - rewrite IHi.
      destruct (Set_VAR.MF.eq_dec x v); auto.
(*    - rewrite IHi.
      destruct (Set_VAR.MF.eq_dec x v); auto.*)
  Qed.

  Lemma all_incl_eq:
    forall A v,
    @AllIncl A [v] v.
  Proof.
    intros.
    apply all_incl_cons.
    + apply incl_refl.
    + apply all_incl_nil.
  Qed.

End Defs.

