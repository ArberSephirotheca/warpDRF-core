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

(*
  Lemma i_subst_proj_rw_eq:
    forall i n,
    proj (Conc2.i_subst TID (NNum n) i) = i_subst TID (NNum n) (proj i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi1; auto);
      try (rewrite IHi2; auto);
      try (rewrite IHi; auto);
      auto
    .
    - destruct (Set_VAR.MF.eq_dec TID TID). {
        
      }
    - .
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
*)
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

  Lemma p_in_inv_access_tid:
    forall a n i,
    PIn a n i ->
    access_tid a = n.
  Proof.
    intros.
    induction H; intros; auto.
    eauto using access_step_inv_in_eq.
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
    access_tid a < TID_COUNT -> (* needed for the second branch, can we prove this? *)
    IIn a (translate i) ->
    TIn a i.
  Proof.
    intros i Hv t1_nin t2_nin a a_lt_tc Hi.
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
        auto using i_in_to_t_in.
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
        auto using i_in_to_t_in.
      }
      intros N.
      apply in_inv_subst_1 in N; auto.
      apply in_inv_subst_in in N; auto using t1_neq_t2, t1_neq_tid.
  Qed.

  (* ---------------------- PAIR IN TRANSLATION ------------------- *)

  Definition TOneOf (p:access_val*access_val) i j :=
    let (v1, v2) := p in
    (TIn v1 i /\ TIn v2 j)
    \/
    (TIn v2 i /\ TIn v1 j).

  Inductive TPairIn : (access_val * access_val) -> Conc2.inst -> Prop :=
  | t_pair_in_mem_acc:
    forall v1 v2 e l1 l2,
    access_step (access_subst TID (NNum (access_tid v1)) e, NNum (access_tid v1)) l1 -> 
    access_step (access_subst TID (NNum (access_tid v2)) e, NNum (access_tid v2)) l2 ->
    List.In v1 l1 ->
    List.In v2 l2 ->
    TPairIn (v1,v2) (Conc2.MemAcc e)
  | t_pair_in_seq_l:
    forall p i j,
    TPairIn p i ->
    TPairIn p (Conc2.Seq i j)
  | t_pair_in_seq_r:
    forall p i j,
    TPairIn p j ->
    TPairIn p (Conc2.Seq i j)
  | t_pair_in_seq_one_of:
    forall p i j,
    TOneOf p i j ->
    TPairIn p (Conc2.Seq i j)
  | t_pair_in_true_true:
    forall v1 v2 b i j,
    BData (access_tid v1) b true ->
    BData (access_tid v2) b true ->
    TPairIn (v1,v2) i -> 
    TPairIn (v1,v2) (Conc2.If b i j)
  | t_pair_in_false_false:
    forall v1 v2 b i j,
    BData (access_tid v1) b false ->
    BData (access_tid v2) b false ->
    TPairIn (v1,v2) i -> 
    TPairIn (v1,v2) (Conc2.If b i j)
  | t_pair_in_true_false:
    forall v1 v2 b i j,
    BData (access_tid v1) b true ->
    BData (access_tid v2) b false ->
    TIn v1 i -> 
    TIn v2 j -> 
    TPairIn (v1,v2) (Conc2.If b i j)
  | t_pair_in_false_true:
    forall v1 v2 b i j,
    BData (access_tid v1) b false ->
    BData (access_tid v2) b true ->
    TIn v1 j -> 
    TIn v2 i -> 
    TPairIn (v1,v2) (Conc2.If b i j)
  .
(*
  Lemma i_in_pair_in_translate_if_true:
    forall v1 v2 b c1 c2,
    BData (access_tid v1) b true ->
    BData (access_tid v2) b true ->
    IPairIn (v1, v2) (translate c1) ->
    IPairIn (v1, v2) (translate (Conc2.If b c1 c2)).
  Proof.
    unfold translate, do_proj.
    intros.
    inversion H1; subst; clear H1;
      simpl in *;
      remove_eq T1 T1;
      remove_eq T1 T2.
    - inversion H6; subst; clear H6.
      inversion H7; subst; clear H7.
      eapply i_pair_decl_l; eauto using n_step_num.
      inversion H9; subst; clear H9; simpl in *.
      + remove_eq T1 T1.
        remove_eq T1 T2.
        inversion H5; subst; clear H5.
        inversion H6; subst; clear H6.
        eapply i_pair_decl_l; eauto using n_step_num.
        simpl.
        inversion H10; subst; clear H10.
        * apply i_pair_in_seq_1; auto.
  Qed.

  Lemma i_pair_in_to_pair_in:
    forall c p, 
(*    Run (translate c) hs ->*)
    TPairIn p c ->
    IPairIn p (translate c).
(*    MPairIn p hs. *)
  Proof.
    induction c; intros.
    - inversion H.
    - inversion H; subst; clear H.
      + apply IHc1 in H6.
  Qed.*)

  (* ---------------------- TRANSLATE + RUN -------------------- *)

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

  Lemma translate_inv:
    forall i m,
    FRun (translate i) m ->
    exists vs1 vs2,
    EEq m (summation (map2 Prod vs1 vs2)) /\
    length vs1 = length vs2 /\
    Map (Iter2d T1 T2 (i_subst TID (NVar T1) (proj i)))
        (range_list_2d 1 TID_COUNT) vs1 /\
    Map (Iter2d T1 T2 (i_subst TID (NVar T2) (proj i)))
        (range_list_2d 1 TID_COUNT) vs2
    .
  Proof.
    unfold translate.
    intros.
    apply f_run_inv_decl_map_2d in H; auto using t1_neq_t2.
    destruct H as (l, (R, Hm)).
    unfold do_proj in Hm.
    apply map_iter_2d_inv_seq in Hm.
    destruct Hm as (vs1, (vs2, (R2, (Hl1, (Hm1, Hm2))))).
    exists vs1, vs2.
    rewrite R.
    rewrite R2.
    split. { reflexivity. }
    auto.
  Qed.

  (* --------------------------- SKIP ---------------------------- *)

  Lemma translate_skip:
    FRun (translate Conc2.Skip) (One []).
  Proof.
    unfold translate.
    rewrite p_eq_decl_impl with (j:=Skip); auto using f_run_decl_skip.
    intros.
    simpl.
    remove_eq T1 T1.
    remove_eq T1 T2.
    rewrite p_eq_decl_impl with (j:=Skip); auto.
    - rewrite p_eq_decl_skip.
      reflexivity.
    - intros.
      simpl.
      rewrite p_eq_seq_skip_r.
      reflexivity.
  Qed.

  Let map_iter_2d_inv_skip I:
    forall x y ks vs,
    Map (Iter2d (I:=I) x y Skip) ks vs ->
    EEq (summation vs) (One []).
  Proof.
    induction ks; intros; inversion H; subst; clear H. {
      reflexivity.
    }
    simpl.
    rewrite IHks; auto.
    destruct a as (na, nb).
    simpl in *.
    inversion H2; subst; clear H2.
    rewrite H.
    rewrite e_plus_nil_l.
    reflexivity.
  Qed.

  Lemma translate_inv_skip:
     forall m,
     FRun (translate Conc2.Skip) m ->
     EEq m (One []).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (vs1, (vs2, (R1, (Hl, (Hm1, Hm2))))).
    rewrite R1; clear R1 m.
    simpl in *.
    apply map_iter_2d_inv_skip in Hm1.
    apply map_iter_2d_inv_skip in Hm2.
    rewrite e_summation_nil_l; auto.
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

  (* ---------------- ACCESS CONSTRUCTOR -------------------- *)

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

  (* ---------------- ACCESS DESTRUCTOR -------------------- *)

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

  Lemma translate_inv_access:
    forall e m,
    FRun (translate (Conc2.MemAcc e)) m ->
    exists vs1 vs2,
    EEq m (summation (map2 Prod vs1 vs2)) /\
    length vs1 = length vs2 /\
    Map (Access2d T1 T2 (access_subst TID (NVar T1) e, NVar T1))
          (range_list_2d 1 TID_COUNT) vs1 /\
    Map (Access2d T1 T2 (access_subst TID (NVar T2) e, NVar T2))
          (range_list_2d 1 TID_COUNT) vs2.
  Proof.
    intros e m Hr.
    apply translate_inv in Hr.
    destruct Hr as (vs1, (vs2, (R1, (Hl, (Hm1, Hm2))))).
    apply map_iter_2d_inv_acc in Hm1.
    destruct Hm1 as (vs1', (R2, (Hl1, Hm1))).
    apply map_iter_2d_inv_acc in Hm2.
    destruct Hm2 as (vs2', (R3, (Hl2, Hm2))).
    exists vs1'.
    exists vs2'.
    rewrite R1; clear R1 m.
    rewrite R2; clear R2.
    rewrite R3; clear R3.
    split. { reflexivity. }
    split. { auto with *. }
    simpl in *.
    remove_eq TID TID.
    auto.
  Qed.

  (* --------------------------- SEQ ------------------------ *)

  Lemma iter_2d_inv_seq I:
    forall x y i j m p,
    Iter2d (I:=I) x y (Seq i j) p m ->
    exists m1 m2,
    EEq m (Prod m1 m2) /\
    Iter2d x y i p m1 /\
    Iter2d x y j p m2.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in H.
    inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma map_iter_2d_inv_fork I:
    forall x y ks vs i j,
    Map (Iter2d (I:=I) x y (Seq i j)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Prod vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d x y i) ks vs1 /\
    Map (Iter2d x y j) ks vs2.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      exists [], [].
      auto using map_nil, e_eq_list_nil.
    }
    inversion H; subst; clear H.
    edestruct IHks as (vs1, (vs2, (Rl, (Hl, (Hm1, Hm2))))); eauto.
    edestruct iter_2d_inv_seq as (ma, (mb, (R2, (Hr1, Hr2)))); eauto.
    exists (ma :: vs1), (mb :: vs2).
    rewrite Rl.
    rewrite R2.
    simpl.
    rewrite Hl.
    rewrite map2_cons_rw.
    split. { reflexivity. }
    split. { reflexivity. }
    split; auto using map_cons.
  Qed.

  Lemma translate_inv_seq i j m:
    FRun (translate (Conc2.Seq i j)) m ->
    exists vs1_1 vs2_1 vs1_2 vs2_2,
    EEq m (summation (map2 Prod (map2 Prod vs1_1 vs2_1) (map2 Prod vs1_2 vs2_2))) /\
    length vs1_1 = length vs2_1 /\
    length vs2_1 = length vs1_2 /\
    length vs1_2 = length vs2_2 /\
    FRun (translate i) (summation (map2 Prod vs1_1 vs1_2)) /\
    FRun (translate j) (summation (map2 Prod vs2_1 vs2_2)).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (vs1, (vs2, (R1, (Hl, (Hm1, Hm2))))).
    simpl in *.
    apply map_iter_2d_inv_seq in Hm1.
    destruct Hm1 as (vs1_1, (vs2_1, (R_1, (Hl1, (Hm1_1, Hm2_1))))).
    apply map_iter_2d_inv_seq in Hm2.
    destruct Hm2 as (vs1_2, (vs2_2, (R_2, (Hl2, (Hm1_2, Hm2_2))))).
    eexists.
    eexists.
    eexists.
    eexists.
    split.
    2: {
      split. 2: {
        split. 2: {
          split. 2: {
            split.
            - eapply translate_def; eauto.
            - eapply translate_def; eauto.
          }
          auto.
        }
        apply e_eq_list_inv_length_r in R_1; auto.
        apply e_eq_list_inv_length_r in R_2; auto.
        auto with *.
      }
      auto.
    }
    rewrite R1.
    rewrite R_1.
    rewrite R_2.
    reflexivity.
  Qed.

  (* ------------------------------ IF ----------------------------- *)

End Defs.
