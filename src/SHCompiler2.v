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
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import SetTh.
Import ListNotations.
Require Import RangeList.
Require Import Tasks.
Require Import SymExec2.
Require SymHist2.
Require Import SymExecMRun.
Require Import SymExecMap.
Require Import SymExec2DMap.
Require Import SymExecEq.
Require Import MExp.
Require Import PairInUtil.

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
    end.

  Definition do_proj x i := i_subst TID (NVar x) (proj i).

  Definition translate c : inst :=
    Decl T1 (NNum 1, NNum TID_COUNT)
      (Decl T2 (NNum 0, NVar T1)
        (Seq (do_proj T1 c) (do_proj T2 c))).



  (* ----------------------- SUBSTITUTION --------------------------- *)

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
  Qed.

  (* ---------------------------- IN PROJECTION -------------------- *)

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

  Lemma var_proj_rw:
    forall x i,
    Var x (proj i) ->
    Conc2.Var x i.
  Proof.
    induction i; simpl; intros.
    - assumption.
    - destruct H; auto.
    - destruct H; auto.
    - assumption.
    - destruct H; auto.
  Qed.

  (* ------------------------- IN PROJECTION ----------------------- *)

  Inductive PIn a n: Conc2.inst -> Prop :=
  | p_in_access:
    forall e l,
    access_step (access_subst TID (NNum n) e, NNum n) l -> 
    List.In a l ->
    PIn a n (Conc2.MemAcc e)
  | p_in_seq_l:
    forall i j,
    PIn a n i ->
    PIn a n (Conc2.Seq i j)
  | p_in_seq_r:
    forall i j,
    PIn a n j ->
    PIn a n (Conc2.Seq i j)
  | p_in_if_true:
    forall b i j,
    BData n b true ->
    PIn a n i ->
    PIn a n (Conc2.If b i j)
  | p_in_if_false:
    forall b i j,
    BData n b false ->
    PIn a n j ->
    PIn a n (Conc2.If b i j)
  | p_in_for:
    forall e1 e2 n' n1 n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 <= n' < n2 ->
    PIn a n (Conc2.i_subst x (NNum n') i) ->
    PIn a n (Conc2.For x (e1, e2) i)
  .


  Lemma s_in_to_p_in:
    forall a n i,
    ~ Conc2.Var TID i ->
    SIn a n (proj i) ->
    PIn a n i.
  Proof.
    intros a n i Hv Hi.
    remember (proj i) as j.
    generalize dependent i.
    induction Hi; intros i' Hv Heq.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      remove_eq TID TID.
      eapply p_in_access; eauto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply p_in_seq_l; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply p_in_seq_r; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply p_in_if_true; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply p_in_if_false; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
    - destruct i'; inversion Heq; subst; clear Heq.
    - destruct i'; inversion Heq; subst; clear Heq.
      eapply p_in_for; eauto.
      simpl in *.
      assert (TID <> v) by auto.
      apply IHHi.
      + intros N.
        apply Conc2.var_subst_inv_1 in N.
        auto.
      + rewrite i_subst_proj_rw; auto.
  Qed.

  Lemma p_in_to_s_in:
    forall a n i,
    ~ Conc2.Var TID i ->
    PIn a n i ->
    SIn a n (proj i).
  Proof.
    intros a n i Hv Hi.
    generalize dependent Hv.
    induction Hi; intros Hv; simpl.
    - eapply s_in_access; eauto.
      simpl.
      remove_eq TID TID.
      assumption.
    - simpl in *.
      apply s_in_seq_l; auto.
    - simpl in *.
      apply s_in_seq_r; auto.
    - simpl in *.
      apply s_in_if_true; auto.
    - simpl in *.
      apply s_in_if_false; auto.
    - simpl in *.
      assert (TID <> x) by auto.
      eapply s_in_decl; eauto.
      rewrite <- i_subst_proj_rw; auto.
      apply IHHi.
      intros N.
      apply Conc2.var_subst_inv_1 in N.
      auto.
  Qed.

  Lemma p_in_inv_access_tid:
    forall a n i,
    PIn a n i ->
    access_tid a = n.
  Proof.
    intros.
    induction H; intros; auto.
    eauto using access_step_inv_in_eq.
  Qed.


  (* ----------------------------- IN TRANSLATION ------------------ *)


  Inductive TIn (a:access_val) : Conc2.inst -> Prop :=
  | t_in_access:
    forall e l,
    access_step (access_subst TID (NNum (access_tid a)) e, NNum (access_tid a)) l -> 
    List.In a l ->
    TIn a (Conc2.MemAcc e)
  | t_in_seq_l:
    forall i j,
    TIn a i ->
    TIn a (Conc2.Seq i j)
  | t_in_seq_r:
    forall i j,
    TIn a j ->
    TIn a (Conc2.Seq i j)
  | t_in_if_true:
    forall b i j,
    BData (access_tid a) b true ->
    TIn a i ->
    TIn a (Conc2.If b i j)
  | t_in_if_false:
    forall b i j,
    BData (access_tid a) b false ->
    TIn a j ->
    TIn a (Conc2.If b i j)
  | t_in_for:
    forall e1 e2 n n1 n2 x i,
    NData (access_tid a) e1 n1 ->
    NData (access_tid a) e2 n2 ->
    n1 <= n < n2 ->
    TIn a (Conc2.i_subst x (NNum n) i) ->
    TIn a (Conc2.For x (e1, e2) i)
  .


  Lemma t_in_to_p_in:
    forall a i,
    TIn a i ->
    PIn a (access_tid a) i.
  Proof.
    intros a i Hi.
    induction Hi; intros;
      eauto using p_in_access,
        p_in_seq_l, p_in_seq_r,
        p_in_if_true, p_in_if_false, p_in_for.
  Qed.

  Lemma p_in_to_t_in:
    forall a n i,
    PIn a n i ->
    TIn a i.
  Proof.
    intros.
    assert (Heq: access_tid a = n) by eauto using p_in_inv_access_tid.
    generalize dependent Heq.
    induction H; intros; auto using t_in_seq_l, t_in_seq_r.
    - rewrite <- Heq in *.
      eauto using t_in_access.
    - apply t_in_if_true; auto.
      rewrite Heq.
      assumption.
    - apply t_in_if_false; auto.
      rewrite Heq.
      assumption.
    - eapply t_in_for; eauto.
      + rewrite Heq.
        assumption.
      + rewrite Heq.
        assumption.
  Qed.

  (* ------------------------- TIN TO IIN ------------------------ *)

  Lemma t_in_to_i_in:
    forall i,
    ~ Conc2.Var TID i ->
    forall a,
    TIn a i ->
    IIn a (i_subst TID (NNum (access_tid a)) (proj i)).
  Proof.
    intros.
    apply s_in_to_i_in. {
      intros N.
      apply var_proj_rw in N.
      auto.
    }
    apply p_in_to_s_in; auto.
    apply t_in_to_p_in; auto.
  Qed.

  Lemma i_in_to_t_in:
    forall i,
    ~ Conc2.Var TID i ->
    forall a,
    IIn a (i_subst TID (NNum (access_tid a)) (proj i)) ->
    TIn a i.
  Proof.
    intros i Hv a Hi.
    eapply p_in_to_t_in; eauto.
    apply s_in_to_p_in; eauto.
    apply i_in_to_s_in; eauto.
    intros N.
    apply var_proj_rw in N.
    auto.
  Qed.

  Lemma i_in_inv_access_tid:
    forall a t i,
    ~ Conc2.Var TID i ->
    IIn a (i_subst TID (NNum t) (proj i)) ->
    t = access_tid a.
  Proof.
    intros a t i Hv Hi.
    apply i_in_to_s_in in Hi. {
      apply s_in_to_p_in in Hi; auto.
      apply p_in_inv_access_tid in Hi.
      auto.
    }
    intros N.
    apply var_proj_rw in N.
    auto.
  Qed.

  Lemma t_in_to_i_in_translate:
    forall i,
    ~ Conc2.Var TID i ->
    ~ Conc2.In T1 i ->
    ~ Conc2.In T2 i ->
    forall a,
    access_tid a < TID_COUNT -> (* needed for the second branch, can we prove this? *)
    TIn a i ->
    IIn a (translate i).
  Proof.
    intros i Hv t1_nin t2_nin a a_lt_tc Hi.
    unfold translate.
    assert (Hx: access_tid a = 0 \/ access_tid a > 0). {
      destruct (access_tid a); auto with *.
    }
    assert (t1_nin_p: ~ In T1 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ In T2 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t2_neq_tid.
    }
    destruct Hx as [Hx|Hx]. {
      (*
         We have that access_tid a = 0.
         We show that a is produced by T2, because
         only T2 can be assigned to 0 (as T1 starts at 1).

         We can pick any value of T1, because the rule of sequence says we
         can pick any branch and we pick the branch of the projection set
         to T2.

         Thus, we pick T1 = 1 and T2 = 0.
      *)
      apply i_in_decl with (n:=1) (n1:=1) (n2:=TID_COUNT); auto using n_step_num. {
        auto using tid_count_1_lt with *.
      }
      unfold do_proj.
      simpl.
      remove_eq T1 T1.
      remove_eq T1 T2.
      apply i_in_decl with (n:=0) (n1:=0) (n2:=1); auto using n_step_num.
      simpl.
      apply i_in_seq_r.
      rewrite i_subst_subst_neq; auto using t1_neq_t2.
      rewrite i_subst_subst_trans; auto.
      rewrite i_subst_not_in. {
        rewrite <- Hx.
        apply t_in_to_i_in; auto.
      }
      intros N.
      apply in_i_subst_neq in N; auto using t1_neq_tid. 
      intros M.
      inversion M.
    }
    (*
       We have that access_tid a > 0.
       We do not know what the value actually is, but we know that
       it cannot be *0*.

       Thus, `access_tid a` cannot be T2 (as it _may_ be assigned to 0).

       We, therefore, set T1 = access_tid a and must pick some value for
       T2. We can pick `T2 = 0`. 

       Thus, we pick `T1 = access_tid a` and `T2 = 0`.
    *)
    apply i_in_decl with (n:=access_tid a) (n1:=1) (n2:=TID_COUNT); auto using n_step_num.
    unfold do_proj.
    simpl.
    remove_eq T1 T1.
    remove_eq T1 T2.
    apply i_in_decl with (n:=0) (n1:=0) (n2:=access_tid a); auto using n_step_num.
    simpl.
    apply i_in_seq_l.
    rewrite i_subst_not_in. {
      rewrite i_subst_subst_trans; auto.
      apply t_in_to_i_in; auto.
    }
    intros N.
    apply in_i_subst_neq in N; auto using t1_neq_t2. {
      apply in_i_subst_neq in N; auto using t2_neq_tid.
      intros X.
      inversion X.
      contradict H0.
      auto using t1_neq_t2.
    }
    intros X.
    inversion X.
  Qed.

  Lemma i_in_translate_to_t_in:
    forall i,
    ~ Conc2.Var TID i ->
    ~ Conc2.In T1 i ->
    ~ Conc2.In T2 i ->
    forall a,
    IIn a (translate i) ->
    TIn a i /\ access_tid a < TID_COUNT.
  Proof.
    intros i Hv t1_nin t2_nin a Hi.
    unfold translate in Hi.

    inversion Hi; subst; clear Hi.

    (* Useful results *)
    assert (t1_nin_p: ~ In T1 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ In T2 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t2_neq_tid.
    }


    (* Remove temporary variables introduced in NStep *)
    assert (n1 = 1) by eauto using n_step_fun, n_step_num.
    assert (n2 = TID_COUNT) by eauto using n_step_fun, n_step_num.
    subst.
    repeat match goal with (* remove unneeded assumptions *)
      H: NStep (NNum _) _ |- _ => clear H
    end.
    match goal with
      H: _ <= ?n < _ |- _ => rename n into t1
    end.

    (* Rename assumption (IIn a ...) *)
    match goal with
      H: IIn _ _ |- _ => rename H into Hi
    end.

    (* Do inversion and then clean up *)
    simpl in Hi.
    remove_eq T1 T2.
    remove_eq T1 T1.
    inversion Hi; subst; clear Hi.
    assert (n1 = 0) by eauto using n_step_fun, n_step_num.
    assert (n2 = t1) by eauto using n_step_fun, n_step_num.
    subst.
    repeat match goal with (* remove unneeded assumptions *)
      H: NStep (NNum _) _ |- _ => clear H
    end.
    match goal with
      H: 0 <= ?n < _ |- _ => rename n into t2
    end.

    match goal with
      H: IIn _ _ |- _ => rename H into Hi
    end.
    simpl in Hi.
    (* Is a in T1 or in T2? *)
    unfold do_proj in *.
    inversion Hi; subst; clear Hi;
    match goal with
      H: IIn _ _ |- _ => rename H into Hi
    end.
    - (* a is in T1 *)
      rewrite i_subst_not_in in Hi. {
        rewrite i_subst_subst_trans in Hi; auto.
        assert (R:  t1 = access_tid a) by eauto using i_in_inv_access_tid.
        rewrite R in Hi.
        auto using i_in_to_t_in with *.
      }
      intros N.
      apply in_inv_subst_1 in N; auto.
      apply in_inv_subst_in in N; auto using t1_neq_t2, t2_neq_tid.
    - (* a is in T2 *)
      rewrite i_subst_subst_neq in Hi; auto using t1_neq_t2.
      rewrite i_subst_not_in in Hi. {
        rewrite i_subst_subst_trans in Hi; auto.
        assert (R: t2 = access_tid a) by eauto using i_in_inv_access_tid.
        rewrite R in Hi.
        auto using i_in_to_t_in with *.
      }
      intros N.
      apply in_inv_subst_1 in N; auto.
      apply in_inv_subst_in in N; auto using t1_neq_t2, t1_neq_tid.
  Qed.


  (* ---------------------- PAIR IN TRANSLATION ------------------- *)

  Lemma c_i_in_to_t_in:
    forall a i,
    Conc2.IIn a i ->
    TIn a i.
  Proof.
    intros a i Hi.
    induction Hi;
    auto using t_in_if_true, t_in_if_false, t_in_seq_l, t_in_seq_r.
    - destruct H as (l, (Hi, Hj)).
      eapply t_in_access; eauto.
    - destruct r as (e1, e2).
      destruct H as (Ha, Hb).
      eapply t_in_for; eauto.
  Qed.

  Lemma t_in_to_c_i_in:
    forall a i,
    TIn a i ->
    Conc2.IIn a i.
  Proof.
    intros a i Hi.
    induction Hi; auto using Conc2.i_in_seq_l, Conc2.i_in_seq_r, Conc2.i_in_if_true, Conc2.i_in_if_false.
    - apply Conc2.i_in_access.
      unfold AIn.
      eauto.
    - eapply Conc2.i_in_for; eauto.
      split; auto.
  Qed.

End Defs.
