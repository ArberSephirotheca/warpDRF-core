Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

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

  Fixpoint trace (c:ULang.inst) : TLang.inst :=
    match c with
    | ULang.Skip => TLang.Skip
    | ULang.Seq i j => TLang.Seq (trace i) (trace j)
    | ULang.If b i j => TLang.If b (trace i) (trace j)
    | ULang.MemAcc a => TLang.MemAcc a (NVar TID)
    | ULang.For x r i => TLang.Decl x r (trace i)
    end.

  Definition do_trace x i := TLang.i_subst TID (NVar x) (trace i).

  Definition sequentialize c : TLang.inst :=
    TLang.Decl T1 (NNum 1, NNum TID_COUNT)
      (TLang.Decl T2 (NNum 0, NVar T1)
        (TLang.Seq (do_trace T1 c) (do_trace T2 c))).



  (* ----------------------- SUBSTITUTION --------------------------- *)

  Lemma i_subst_trace_rw:
    forall x i n,
    x <> TID ->
    trace (ULang.i_subst x (NNum n) i) = TLang.i_subst x (NNum n) (trace i).
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

   Lemma in_trace_to_in:
    forall x i,
    x <> TID ->
    TLang.Occurs x (trace i) ->
    ULang.Occurs x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0; auto.
    + destruct H1; auto.
    + contradiction.
    + destruct H1; auto.
  Qed.

  Lemma var_inv_trace:
    forall x i,
    TLang.Var x (trace i) ->
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
    forall e,
    access_step (access_subst TID (NNum n) e, NNum n) a -> 
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
    TLang.SIn a n (trace i) ->
    PIn a n i.
  Proof.
    intros a n i Hv Hi.
    remember (trace i) as j.
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
      + rewrite i_subst_trace_rw; auto.
  Qed.

  Lemma p_in_to_s_in:
    forall a n i,
    ~ ULang.Var TID i ->
    PIn a n i ->
    TLang.SIn a n (trace i).
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
      rewrite <- i_subst_trace_rw; auto.
      apply IHHi.
      intros N.
      apply ULang.var_inv_subst in N.
      auto.
  Qed.

  Lemma s_in_p_in_iff:
    forall a n i,
    ~ ULang.Var TID i ->
    PIn a n i <-> TLang.SIn a n (trace i).
  Proof.
    split; auto using s_in_to_p_in, p_in_to_s_in.
  Qed.

  Lemma p_in_inv_access_tid:
    forall a n i,
    PIn a n i ->
    access_tid a = n.
  Proof.
    intros.
    induction H; intros; auto.
    eapply access_step_inv_tid; eauto using n_step_num.
  Qed.


  (* ----------------------------- IN TRANSLATION ------------------ *)

  Lemma u_in_to_p_in:
    forall a i,
    ULang.IIn a i ->
    PIn a (access_tid a) i.
  Proof.
    intros a i Hi.
    induction Hi; intros;
      eauto using p_in_access,
        p_in_seq_l, p_in_seq_r,
        p_in_if_true, p_in_if_false.
    destruct r as (e1, e2).
    inversion_clear H.
   eapply p_in_for; eauto.
  Qed.

  Lemma p_in_to_u_in:
    forall a n i,
    PIn a n i ->
    ULang.IIn a i.
  Proof.
    intros.
    assert (Heq: access_tid a = n) by eauto using p_in_inv_access_tid.
    generalize dependent Heq.
    induction H; intros; auto using ULang.i_in_seq_l, ULang.i_in_seq_r.
    - rewrite <- Heq in *.
      eauto using ULang.i_in_access.
    - apply ULang.i_in_if_true; auto.
      rewrite Heq.
      assumption.
    - apply ULang.i_in_if_false; auto.
      rewrite Heq.
      assumption.
    - eapply ULang.i_in_for; eauto.
      split.
      + rewrite Heq.
        assumption.
      + rewrite Heq.
        assumption.
  Qed.

  (* ------------------------- TIN TO IIN ------------------------ *)

  Lemma not_var_trace:
    forall x i,
    ~ ULang.Var x i ->
    ~ TLang.Var x (trace i).
  Proof.
    intros.
    intros N.
    apply var_inv_trace in N.
    contradiction.
  Qed.

  Lemma u_in_to_t_in:
    forall i,
    ~ ULang.Var TID i ->
    forall a,
    ULang.IIn a i ->
    TLang.IIn a (TLang.i_subst TID (NNum (access_tid a)) (trace i)).
  Proof.
    intros.
    apply TLang.s_in_to_i_in; auto using not_var_trace.
    apply p_in_to_s_in; auto.
    apply u_in_to_p_in; auto.
  Qed.

  Lemma t_in_to_u_in:
    forall i,
    ~ ULang.Var TID i ->
    forall a,
    TLang.IIn a (TLang.i_subst TID (NNum (access_tid a)) (trace i)) ->
    ULang.IIn a i.
  Proof.
    intros i Hv a Hi.
    eapply p_in_to_u_in; eauto.
    apply s_in_to_p_in; eauto.
    apply TLang.i_in_to_s_in; eauto using not_var_trace.
  Qed.

  Lemma i_in_inv_access_tid:
    forall a t i,
    ~ ULang.Var TID i ->
    TLang.IIn a (TLang.i_subst TID (NNum t) (trace i)) ->
    t = access_tid a.
  Proof.
    intros a t i Hv Hi.
    apply TLang.i_in_to_s_in in Hi; auto using not_var_trace.
    apply s_in_to_p_in in Hi; auto.
    apply p_in_inv_access_tid in Hi.
    auto.
  Qed.

  Lemma i_in_sequentialize_to_t_in:
    forall i,
    ~ ULang.Var TID i ->
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    forall a,
    TLang.IIn a (sequentialize i) ->
    ULang.IIn a i /\ access_tid a < TID_COUNT.
  Proof.
    intros i Hv t1_nin t2_nin a Hi.
    unfold sequentialize in Hi.

    inversion Hi; subst; clear Hi.

    (* Useful results *)
    assert (t1_nin_p: ~ TLang.Occurs T1 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ TLang.Occurs T2 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t2_neq_tid.
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
    unfold do_trace in *.
    (* Remove subst T1 (subst TID ... ) *)
    rewrite TLang.i_subst_not_occurs in Hi.
    2: {
      intros N.
      apply TLang.i_occurs_inv_subst_neq_num in N; auto.
      apply TLang.i_occurs_inv_subst in N; auto using t1_neq_t2, t2_neq_tid.
    }
    (* Remove subs T1 (subs TID T1 ...) *)
    rewrite TLang.i_subst_subst_trans in Hi; auto.
    rewrite TLang.i_subst_subst_neq in Hi; auto using t1_neq_t2.
    (* Remove subs T2 (subs TID T2 ...) *)
    rewrite TLang.i_subst_subst_trans in Hi; auto.

    rewrite TLang.i_subst_not_occurs with (x:=T1) in Hi.
    2: {
      intros N.
      apply TLang.i_occurs_subst_neq in N; auto using t1_neq_t2, t1_neq_tid.
    }

    inversion Hi; subst; clear Hi;
    rename_hyp (TLang.IIn _ _) as Hi.
    - (* a is in T1 *)
      assert (R:  t1 = access_tid a) by eauto using i_in_inv_access_tid.
      rewrite R in Hi.
      auto using t_in_to_u_in with *.
    - (* a is in T2 *)
      assert (R:  t2 = access_tid a) by eauto using i_in_inv_access_tid.
      rewrite R in Hi.
      auto using t_in_to_u_in with *.
  Qed.

  (* ===================== Main results ========================= *)

  Lemma t_pair_in_lt:
    forall i x y,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    ~ TLang.Occurs T1 (trace i) ->
    ~ TLang.Occurs T2 (trace i) ->
    access_tid x < TID_COUNT ->
    ULang.IIn x i ->
    access_tid y < TID_COUNT ->
    ULang.IIn y i ->
    access_tid x < access_tid y ->
    TLang.IPairIn (x, y)
      (TLang.Decl T1 (NNum 1, NNum TID_COUNT)
         (TLang.Decl T2 (NNum 0, NVar T1)
            (TLang.Seq (TLang.i_subst TID (NVar T1) (trace i))
               (TLang.i_subst TID (NVar T2) (trace i))))).
  Proof.
    intros.
    apply TLang.i_pair_in_decl with (n:=access_tid y) (n1:=1) (n2:=TID_COUNT);
      auto using n_step_num with *.
    simpl.
    (* clean up goal *)
    remove_eq T1 T1.
    remove_eq T1 T2.
    rewrite TLang.i_subst_subst_trans; auto.
    assert (~ TLang.Occurs T1 (TLang.i_subst TID (NVar T2) (trace i))). {
      intros N.
      apply TLang.i_occurs_inv_subst in N; auto using t1_neq_t2, t1_neq_tid.
    }
    rewrite TLang.i_subst_not_occurs with (x:=T1); auto.
    (* fix the second biding *)
    apply TLang.i_pair_in_decl with (n:=access_tid x) (n1:=0) (n2:=access_tid y);
      auto using n_step_num with *.
    simpl.
    rewrite TLang.i_subst_subst_trans; auto.
    apply TLang.i_pair_in_seq_both.
    simpl.
    right.
    split. {
      rewrite TLang.i_subst_not_occurs. {
        apply u_in_to_t_in; auto.
      }
      intros N.
      apply TLang.i_occurs_inv_subst_neq_num in N; auto.
    }
    apply u_in_to_t_in; auto.
  Qed.

  Corollary soundness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    Hist.MSafeStrong m_h ->
    ULang.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.Safe m_c.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hv Hs1 Hrc Hrh.
    unfold Hist.MSafeStrong in *.
    unfold Hist.Safe.
    intros x y Hix' Hiy'.

    (* Simplify the goal *)
    destruct (PeanoNat.Nat.eq_dec (access_tid x) (access_tid y)). {
      auto using access_safe_eq_tid.
    }
    apply Hs1; auto; clear Hs1.
    eapply TLang.run_i_pair_in_to_m_pair_in; eauto.

    (* Simplify the assumption of run for t1 *)
    assert (Hrx := Hrc).
    eapply ULang.run_all_inv_in with (x:=x) in Hrx; eauto.
    destruct Hrx as (nx, (h_x, (?, (Hrx, (_, Hix))))).
    assert (nx = access_tid x). {
      symmetry.
      eapply ULang.run_access_tid; eauto.
    }
    subst.
    eapply ULang.in_to_i_in in Hix; eauto.
    clear Hrx Hix'.

    (* Simplify the assumption of run for t2 *)
    assert (Hry := Hrc).
    eapply ULang.run_all_inv_in with (x:=y) in Hry; eauto.
    destruct Hry as (ny, (h_y, (?, (Hry, (_, Hiy))))).
    assert (ny = access_tid y). {
      symmetry.
      eapply ULang.run_access_tid; eauto.
    }
    subst.
    eapply ULang.in_to_i_in in Hiy; eauto.
    clear Hry Hiy'.

    (* We no longer need run all *)
    clear Hrc.

    (* Now we will find the right pair *)
    unfold sequentialize, do_trace.

    (* Useful results *)
    assert (t1_nin_p: ~ TLang.Occurs T1 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ TLang.Occurs T2 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t2_neq_tid.
    }

    assert (X: access_tid x < access_tid y \/ access_tid y < access_tid x). {
      lia.
    }
    destruct X as [Hlt|Hlt]. {
      (* We know that x < y, thus T1 = y and T2 = x *)
      auto using t_pair_in_lt.
    }
    apply TLang.i_pair_in_sym.
    auto using t_pair_in_lt.
  Qed.

  Lemma i_pair_in_1:
    forall p i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    (* --- *)
    TLang.IPairIn p (sequentialize i) ->
    ULang.CPairIn p i.
  Proof.
    intros.
    destruct p as (a1, a2).
    rename_hyp (TLang.IPairIn _ _) as hp.
    apply TLang.i_pair_in_to_i_in in hp.
    destruct hp as (Hxi, Hyi).
    apply i_in_sequentialize_to_t_in in Hxi; auto.
    destruct Hxi as (Hxi, Hlt_x).
    apply i_in_sequentialize_to_t_in in Hyi; auto.
    destruct Hyi as (Hyi, Hlt_y).
    eauto using ULang.c_pair_in_def, ULang.c_in_def.
  Qed.

  Lemma i_pair_in_2:
    forall i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    (* --- *)
    forall x y,
    (* Note that in this direction, the tids being different is a
     pre-conditions. *)
    access_tid x <> access_tid y -> 
    ULang.CPairIn (x,y) i ->
    TLang.IPairIn (x,y) (sequentialize i).
  Proof.
    intros.
    rename_hyp (ULang.CPairIn _ _) as hp.
    invc hp.
    rename_hyp (ULang.CIn x i) as hi1.
    rename_hyp (ULang.CIn y i) as hi2.

    (* Now we will find the right pair *)
    unfold sequentialize, do_trace.

    (* Useful results *)
    assert (t1_nin_p: ~ TLang.Occurs T1 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ TLang.Occurs T2 (trace i)). {
      intros N.
      apply in_trace_to_in in N; auto using t2_neq_tid.
    }
    invc hi1.
    rename_hyp (ULang.IIn x i) as hi1.
    invc hi2.
    rename_hyp (ULang.IIn y i) as hi2.

    assert (X: access_tid x < access_tid y \/ access_tid y < access_tid x). {
      lia.
    }
    destruct X as [Hlt|Hlt].
    - (* We know that x < y, thus T1 = y and T2 = x *)
      apply t_pair_in_lt; auto.
    - (* We know that y < x, thus T1 = x and T2 = y *)
      apply TLang.i_pair_in_sym.
      apply t_pair_in_lt; auto.
  Qed.

  Lemma trace_subst_rw:
    forall x v u,
    ~ ULang.Var x u ->
    NClosed v ->
    x <> TID ->
    trace (ULang.i_subst x v u) =
    TLang.i_subst x v (trace u).
  Proof.
    induction u;
      intros;
      simpl;
      rename_hyp (~ ULang.Var x _) as hv;
      simpl in hv.
    - reflexivity.
    - rewrite IHu1; auto.
      rewrite IHu2; auto.
    - rewrite IHu1; auto.
      rewrite IHu2; auto.
    - destruct (Set_VAR.MF.eq_dec x TID) as [?|_]; try contradiction.
      reflexivity.
    - rename v0 into y.
      destruct (Set_VAR.MF.eq_dec x y). {
        intuition.
      }
      rewrite IHu; auto.
  Qed.

  Lemma do_trace_subst_rw:
    forall x v y i,
    x <> TID ->
    ~ ULang.Var x i ->
    NClosed v ->
    x <> y ->
    TLang.i_subst x v (do_trace y i) =
    do_trace y (ULang.i_subst x v i).
  Proof.
    unfold do_trace.
    intros.
    rewrite trace_subst_rw; auto.
    rewrite TLang.i_subst_subst_neq_3; auto.
  Qed.

  Lemma sequentialize_subst_rw:
    forall x v i,
    ~ ULang.Var x i ->
    NClosed v ->
    x <> T1 ->
    x <> T2 ->
    x <> TID ->
    TLang.i_subst x v (sequentialize i) = sequentialize (ULang.i_subst x v i).
  Proof.
    intros.
    unfold sequentialize.
    simpl.
    destruct (Set_VAR.MF.eq_dec x T1) as [?|_]; try contradiction.
    destruct (Set_VAR.MF.eq_dec x T2) as [?|_]; try contradiction.
    rewrite do_trace_subst_rw; auto.
    rewrite do_trace_subst_rw; auto.
  Qed.


  Corollary completeness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    Hist.Safe m_c ->
    ULang.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.MSafeStrong m_h.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hv Hs1 Hrc Hrh.
    unfold Hist.MSafeStrong in *.
    unfold Hist.Safe in *.
    intros x y Hneq Hp.
    eapply TLang.run_m_pair_in_to_i_pair_in in Hp; eauto.
    apply TLang.i_pair_in_to_i_in in Hp.
    destruct Hp as (Hxi, Hyi).
    apply i_in_sequentialize_to_t_in in Hxi; auto.
    destruct Hxi as (Hxi, Hlt_x).
    apply i_in_sequentialize_to_t_in in Hyi; auto.
    destruct Hyi as (Hyi, Hlt_y).
    apply Hs1; auto; clear Hs1.
    - eapply ULang.run_all_i_in_to_in in Hxi; eauto.
    - eapply ULang.run_all_i_in_to_in in Hyi; eauto.
  Qed.

  Corollary correctness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    ~ ULang.Var TID i ->
    ULang.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.Safe m_c <-> Hist.MSafeStrong m_h.
  Proof.
    split; intros. {
      eapply completeness; eauto.
    }
    eapply soundness; eauto.
  Qed.
End Defs.
