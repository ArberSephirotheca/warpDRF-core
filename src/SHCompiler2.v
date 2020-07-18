Require Import Coq.Lists.List.
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
Require Import SymExecMRun.
Require Import SymExecMap.
Require Import MExp.

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

  Lemma translate_def:
    forall i vs1 vs2,
    Map (Iter2d T1 T2 (i_subst TID (NVar T1) (proj i)))
        (range_list_2d 1 TID_COUNT) vs1 ->
    Map (Iter2d T1 T2 (i_subst TID (NVar T2) (proj i)))
        (range_list_2d 1 TID_COUNT) vs2 ->
    FRun (translate i) (summation (map2 Prod vs1 vs2)).
  Proof.
    intros.
    unfold translate.
    apply f_run_decl_map_2d; auto using t1_neq_t2.
    apply map_iter2d_map2_prod; auto.
  Qed.

  (* -------------------- ACCESS ---------------------------- *)
  
  Definition Access2d x y (e:access_exp * nexp) (p:nat*nat) m :=
    let (nx, ny) := p in
    let (a, e) := e in
      exists v,
      access_step
        (access_subst y (NNum ny)
          (access_subst x (NNum nx) a),
           n_subst y (NNum ny) (n_subst x (NNum nx) e)) v /\
      m = One v.


  Lemma access_2d_to_iter_2d:
    forall x y e a m,
    Access2d x y e a m ->
    Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e) a m.
  Proof.
    unfold Access2d, Iter2d.
    intros.
    destruct a as (nx, ny).
    destruct e as (a, e).
    destruct H as (v, (H,R)).
    subst.
    simpl.
    eapply f_run_access; eauto.
    reflexivity.
  Qed.

  Lemma iter_2d_inv_access:
    forall x y e p m,
    Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e) p m ->
    exists m', EEq m m' /\ Access2d x y e p m'.
  Proof.
    intros.
    unfold Iter2d in H.
    destruct p as (nx, ny).
    destruct e as (a, e).
    simpl in H.
    inversion H; subst; clear H.
    unfold Iter2d, Access2d.
    simpl in *.
    eauto.
  Qed.

  Lemma map_iter_2d_inv_acc:
    forall x y e ks vs,
    Map (Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e)) ks vs ->
    exists vs',
    EEqList vs vs' /\
    length vs = length vs' /\
    Map (Access2d x y e) ks vs'.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      exists [].
      split. { reflexivity. }
      split. { reflexivity. }
      apply map_nil.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    destruct H5 as (vs1, (R1, (Hl1, Hm2))).
    apply iter_2d_inv_access in H2.
    destruct H2 as (m1, (R2, Hacc)).
    exists (m1::vs1).
    split. {
      rewrite R2.
      rewrite R1.
      reflexivity.
    }
    simpl.
    rewrite Hl1.
    auto using map_cons.
  Qed.

  Lemma map_iter_2d_access_skip:
    forall x y e ks vs,
    Map (Access2d x y e) ks vs ->
    Map (Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e)) ks vs.
  Proof.
    eauto using map_impl, access_2d_to_iter_2d.
  Qed.

  Lemma translate_access:
    forall e vs1 vs2,
    Map (Access2d T1 T2 (access_subst TID (NVar T1) e, NVar T1))
          (range_list_2d 1 TID_COUNT) vs1 ->
    Map (Access2d T1 T2 (access_subst TID (NVar T2) e, NVar T2))
          (range_list_2d 1 TID_COUNT) vs2 ->
    FRun (translate (Conc2.MemAcc e)) (summation (map2 Prod vs1 vs2)).
  Proof.
    intros.
    unfold translate.
    unfold do_proj.
    apply f_run_decl_map_2d; auto using t1_neq_t2.
    apply map_iter2d_map2_prod.
    + simpl.
      remove_eq TID TID.
      apply map_iter_2d_access_skip; simpl in *.
      remove_eq TID TID.
      assumption.
    + apply map_iter_2d_access_skip.
      simpl in *.
      remove_eq TID TID.
      assumption.
  Qed.


  End Defs.

End Compiler.
