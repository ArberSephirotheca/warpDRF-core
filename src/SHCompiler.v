Require Import Coq.Lists.List.
Require Coq.omega.Omega.

Require Import Util.

Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import AExp.
Require Import Tasks.
Require Import Tictac.

Require TLang.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Fixpoint proj (c:ULang.inst) : TLang.inst :=
    match c with
    | ULang.Skip => TLang.Skip
    | ULang.Seq i j => TLang.Seq (proj i) (proj j)
    | ULang.If b i j => TLang.If b (proj i) (proj j)
    | ULang.MemAcc a => TLang.MemAcc a (NVar TID)
    | ULang.For x r i => TLang.Decl x r (proj i)
    end.

  Definition do_proj x i := TLang.i_subst TID (NVar x) (proj i).

  Definition translate c : TLang.inst :=
    TLang.Decl T1 (NNum 1, NNum TID_COUNT)
      (TLang.Decl T2 (NNum 0, NVar T1)
        (TLang.Seq (do_proj T1 c) (do_proj T2 c))).



  (* ----------------------- SUBSTITUTION --------------------------- *)

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (ULang.i_subst x (NNum n) i) = TLang.i_subst x (NNum n) (proj i).
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
    TLang.SEFree (proj i) x ->
    ULang.CFree i x.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0; auto.
    + destruct H1; auto.
    + contradiction.
    + destruct H1; auto.
  Qed.

  Lemma var_proj_rw:
    forall x i,
    TLang.Var x (proj i) ->
    ULang.Var x i.
  Proof.
    induction i; simpl; intros.
    - assumption.
    - destruct H; auto.
    - destruct H; auto.
    - assumption.
    - destruct H; auto.
  Qed.

  (* ------------------------- IN PROJECTION ----------------------- *)

  Inductive PIn a n: ULang.inst -> Prop :=
  | p_in_access:
    forall e l,
    access_step (access_subst TID (NNum n) e, NNum n) l -> 
    List.In a l ->
    PIn a n (ULang.MemAcc e)
  | p_in_seq_l:
    forall i j,
    PIn a n i ->
    PIn a n (ULang.Seq i j)
  | p_in_seq_r:
    forall i j,
    PIn a n j ->
    PIn a n (ULang.Seq i j)
  | p_in_if_true:
    forall b i j,
    BData n b true ->
    PIn a n i ->
    PIn a n (ULang.If b i j)
  | p_in_if_false:
    forall b i j,
    BData n b false ->
    PIn a n j ->
    PIn a n (ULang.If b i j)
  | p_in_for:
    forall e1 e2 n' n1 n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 <= n' < n2 ->
    PIn a n (ULang.i_subst x (NNum n') i) ->
    PIn a n (ULang.For x (e1, e2) i)
  .


  Lemma s_in_to_p_in:
    forall a n i,
    ~ ULang.Var TID i ->
    TLang.SIn a n (proj i) ->
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
        apply ULang.var_inv_subst in N.
        auto.
      + rewrite i_subst_proj_rw; auto.
  Qed.

  Lemma p_in_to_s_in:
    forall a n i,
    ~ ULang.Var TID i ->
    PIn a n i ->
    TLang.SIn a n (proj i).
  Proof.
    intros a n i Hv Hi.
    generalize dependent Hv.
    induction Hi; intros Hv; simpl.
    - eapply TLang.s_in_access; eauto.
      simpl.
      remove_eq TID TID.
      assumption.
    - simpl in *.
      apply TLang.s_in_seq_l; auto.
    - simpl in *.
      apply TLang.s_in_seq_r; auto.
    - simpl in *.
      apply TLang.s_in_if_true; auto.
    - simpl in *.
      apply TLang.s_in_if_false; auto.
    - simpl in *.
      assert (TID <> x) by auto.
      eapply TLang.s_in_decl; eauto.
      rewrite <- i_subst_proj_rw; auto.
      apply IHHi.
      intros N.
      apply ULang.var_inv_subst in N.
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


  Inductive TIn (a:access_val) : ULang.inst -> Prop :=
  | t_in_access:
    forall e l,
    access_step (access_subst TID (NNum (access_tid a)) e, NNum (access_tid a)) l -> 
    List.In a l ->
    TIn a (ULang.MemAcc e)
  | t_in_seq_l:
    forall i j,
    TIn a i ->
    TIn a (ULang.Seq i j)
  | t_in_seq_r:
    forall i j,
    TIn a j ->
    TIn a (ULang.Seq i j)
  | t_in_if_true:
    forall b i j,
    BData (access_tid a) b true ->
    TIn a i ->
    TIn a (ULang.If b i j)
  | t_in_if_false:
    forall b i j,
    BData (access_tid a) b false ->
    TIn a j ->
    TIn a (ULang.If b i j)
  | t_in_for:
    forall e1 e2 n n1 n2 x i,
    NData (access_tid a) e1 n1 ->
    NData (access_tid a) e2 n2 ->
    n1 <= n < n2 ->
    TIn a (ULang.i_subst x (NNum n) i) ->
    TIn a (ULang.For x (e1, e2) i)
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
    ~ ULang.Var TID i ->
    forall a,
    TIn a i ->
    TLang.IIn a (TLang.i_subst TID (NNum (access_tid a)) (proj i)).
  Proof.
    intros.
    apply TLang.s_in_to_i_in. {
      intros N.
      apply var_proj_rw in N.
      auto.
    }
    apply p_in_to_s_in; auto.
    apply t_in_to_p_in; auto.
  Qed.

  Lemma i_in_to_t_in:
    forall i,
    ~ ULang.Var TID i ->
    forall a,
    TLang.IIn a (TLang.i_subst TID (NNum (access_tid a)) (proj i)) ->
    TIn a i.
  Proof.
    intros i Hv a Hi.
    eapply p_in_to_t_in; eauto.
    apply s_in_to_p_in; eauto.
    apply TLang.i_in_to_s_in; eauto.
    intros N.
    apply var_proj_rw in N.
    auto.
  Qed.

  Lemma i_in_inv_access_tid:
    forall a t i,
    ~ ULang.Var TID i ->
    TLang.IIn a (TLang.i_subst TID (NNum t) (proj i)) ->
    t = access_tid a.
  Proof.
    intros a t i Hv Hi.
    apply TLang.i_in_to_s_in in Hi. {
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
    ~ ULang.Var TID i ->
    ~ ULang.CFree i T1 ->
    ~ ULang.CFree i T2 ->
    forall a,
    access_tid a < TID_COUNT -> (* needed for the second branch, can we prove this? *)
    TIn a i ->
    TLang.IIn a (translate i).
  Proof.
    intros i Hv t1_nin t2_nin a a_lt_tc Hi.
    unfold translate.
    assert (Hx: access_tid a = 0 \/ access_tid a > 0). {
      destruct (access_tid a); auto with *.
    }
    assert (t1_nin_p: ~ TLang.SEFree (proj i) T1). {
      intros N.
      apply in_proj_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ TLang.SEFree (proj i) T2). {
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
      apply TLang.i_in_decl with (n:=1) (n1:=1) (n2:=TID_COUNT); auto using n_step_num. {
        auto using tid_count_1_lt with *.
      }
      unfold do_proj.
      simpl.
      remove_eq T1 T1.
      remove_eq T1 T2.
      apply TLang.i_in_decl with (n:=0) (n1:=0) (n2:=1); auto using n_step_num.
      simpl.
      apply TLang.i_in_seq_r.
      rewrite TLang.i_subst_subst_neq; auto using t1_neq_t2.
      rewrite TLang.i_subst_subst_trans; auto.
      rewrite TLang.i_subst_not_free. {
        rewrite <- Hx.
        apply t_in_to_i_in; auto.
      }
      intros N.
      apply TLang.i_free_subst_neq in N; auto using t1_neq_tid. 
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
    apply TLang.i_in_decl with (n:=access_tid a) (n1:=1) (n2:=TID_COUNT); auto using n_step_num.
    unfold do_proj.
    simpl.
    remove_eq T1 T1.
    remove_eq T1 T2.
    apply TLang.i_in_decl with (n:=0) (n1:=0) (n2:=access_tid a); auto using n_step_num.
    simpl.
    apply TLang.i_in_seq_l.
    rewrite TLang.i_subst_not_free. {
      rewrite TLang.i_subst_subst_trans; auto.
      apply t_in_to_i_in; auto.
    }
    intros N.
    apply TLang.i_free_subst_neq in N; auto using t1_neq_t2.
    apply TLang.i_free_subst_neq in N; auto using t2_neq_tid.
    intros X.
    inversion X.
    contradict H0.
    auto using t1_neq_t2.
  Qed.

  Lemma i_in_translate_to_t_in:
    forall i,
    ~ ULang.Var TID i ->
    ~ ULang.CFree i T1 ->
    ~ ULang.CFree i T2 ->
    forall a,
    TLang.IIn a (translate i) ->
    TIn a i /\ access_tid a < TID_COUNT.
  Proof.
    intros i Hv t1_nin t2_nin a Hi.
    unfold translate in Hi.

    inversion Hi; subst; clear Hi.

    (* Useful results *)
    assert (t1_nin_p: ~ TLang.SEFree (proj i) T1). {
      intros N.
      apply in_proj_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ TLang.SEFree (proj i) T2). {
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
      H: TLang.IIn _ _ |- _ => rename H into Hi
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

    rename_hyp (TLang.IIn _ _) as Hi.
    simpl in Hi.
    (* Is a in T1 or in T2? *)
    unfold do_proj in *.
    inversion Hi; subst; clear Hi;
    rename_hyp (TLang.IIn _ _) as Hi.
    - (* a is in T1 *)
      rewrite TLang.i_subst_not_free in Hi. {
        rewrite TLang.i_subst_subst_trans in Hi; auto.
        assert (R:  t1 = access_tid a) by eauto using i_in_inv_access_tid.
        rewrite R in Hi.
        auto using i_in_to_t_in with *.
      }
      intros N.
      apply TLang.se_free_inv_subst_neq_num in N; auto.
      apply TLang.i_free_inv_subst in N; auto using t1_neq_t2, t2_neq_tid.
    - (* a is in T2 *)
      rewrite TLang.i_subst_subst_neq in Hi; auto using t1_neq_t2.
      rewrite TLang.i_subst_not_free in Hi. {
        rewrite TLang.i_subst_subst_trans in Hi; auto.
        assert (R: t2 = access_tid a) by eauto using i_in_inv_access_tid.
        rewrite R in Hi.
        auto using i_in_to_t_in with *.
      }
      intros N.
      apply TLang.i_free_subst_neq in N; auto using t1_neq_t2.
      apply TLang.i_free_inv_subst in N; auto using t1_neq_t2, t1_neq_tid.
  Qed.


  (* ---------------------- PAIR IN TRANSLATION ------------------- *)

  Lemma c_i_in_to_t_in:
    forall a i,
    ULang.IIn a i ->
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
    ULang.IIn a i.
  Proof.
    intros a i Hi.
    induction Hi; auto using ULang.i_in_seq_l, ULang.i_in_seq_r, ULang.i_in_if_true, ULang.i_in_if_false.
    - apply ULang.i_in_access.
      unfold AIn.
      eauto.
    - eapply ULang.i_in_for; eauto.
      split; auto.
  Qed.

End Defs.
