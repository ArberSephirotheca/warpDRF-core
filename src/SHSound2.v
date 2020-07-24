Require Import Coq.Lists.List.

Require Coq.omega.Omega.

Require Conc2.

Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import SymExec2.
Require Import SymExecMRun.
Require Import RangeList.
Require Import SHCompiler2.
Require Import Tasks.
Require Import SetTh.
Require Import InUtil.
Require Import PairInUtil.
Require Import MExp.
Import ListNotations.
Require SymHist.


Section Compiler.
  Import SHCompiler2.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Lemma in_to_in_proj:
    forall x i,
    Conc2.In x i ->
    In x (proj i).
  Proof.
    induction i; simpl; intros;
      auto;
      destruct H; auto;
      destruct H; auto.
  Qed.

  Lemma var_eq_dec_rw_eq:
    forall x,
    exists e, Set_VAR.MF.eq_dec x x = @left _ _ e.
  Proof.
    intros.
    destruct (Set_VAR.MF.eq_dec x x).
    - exists e.
      reflexivity.
    - contradiction.
  Qed.
(*
  Theorem run_m_proj:
    forall n i hs2,
    Conc2.Run n i hs2 ->
    forall n hs1,
    Run (i_subst TID (NNum n) (proj i)) hs1 ->
    ~ Var TID i ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    intros i hs2 H.
    induction H; intros.
    - inversion H0; subst; clear H0.
      reflexivity.
    - inversion H2; subst; clear H2.
      apply SymExec.var_not_in_acc in H3.
      assert (IHRun := IHRun _ _ H1 H8 H3).
      subst.
      destruct (var_eq_dec_rw_eq TID) as (?, R).
      rewrite R in *; clear R.
      destruct H as (vs, (Ha,Hb)).
      simpl in *.
      subst.
      unfold LoopFree.LStep in *.
      erewrite Hist.m_proj_prepend; eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (l0 = l). {
        assert (R: r_subst TID (NNum n) r = r). {
          apply r_subst_not_in.
          eapply r_step_to_not_in; eauto.
        }
        rewrite R in *.
        eauto using r_step_fun.
      }
      subst.
      assert (~ SymExec.Var TID (SymExec.Branch x l i1 i2)). {
        intros N.
        contradict H3.
        eauto using SymExec.var_branch_to_decl.
      }
      eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (~ SymExec.Var TID (SymExec.Branch x l i1 i2)). {
        intros N.
        contradict H3.
        auto using SymExec.var_branch_cons.
      }
      apply IHRun2 in H11; auto; clear IHRun2.
      subst.
      rewrite Hist.m_proj_app.
      assert (Hist.m_proj n0 hs1 = hs3). {
        destruct (Set_VAR.MF.eq_dec TID x). {
          apply SymExec.var_not_in_branch in H3.
          destruct H3 as (?, _).
          contradiction.
        }
        apply IHRun1; auto; clear IHRun1.
        + rewrite SymExec.i_subst_subst_neq in H10; auto.
          rewrite <- SymExec.i_subst_seq in H10.
          rewrite <- i_subst_proj_rw in H10; auto.
          rewrite proj_seq in *.
          auto.
        + intros N.
          contradict H2.
          eauto using SymExec.var_iter_branch.
      }
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (~ SymExec.Var TID i2). {
        intros N.
        contradict H2.
        auto using SymExec.var_branch_r.
      }
      auto.
    - simpl in *.
      inversion H2; subst; clear H2.
      rewrite Hist.m_proj_app.
      erewrite IHRun1; eauto.
      2: { intros N. contradict H3. auto using var_fork_l. }
      erewrite IHRun2; eauto.
      intros N. contradict H3. auto using var_fork_r.
  Qed.

  Lemma run_do_proj (t:var):
    forall i m_l,
    SymExec.Run i m_l ->
    forall n m_h,
    n < TID_COUNT -> 
    Run (SymExec.i_subst t (NNum n) (do_proj t i)) m_h ->
    ~ Var TID i ->
    ~ In t i ->
    t <> TID ->
    Hist.m_proj n m_l = m_h.
  Proof.
    unfold do_proj.
    intros.
    rewrite i_subst_subst_trans in H1; auto.
    + eapply run_m_proj; eauto.
    + intros N.
      contradict H3.
      apply in_proj_to_in; auto.
  Qed.

  Lemma run_do_proj_do_proj:
    forall i hs2,
    Run i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT ->
    n2 < TID_COUNT ->
    Run
        (i_subst T2 (NNum n1)
           (i_subst T1 (NNum n2) (seq (do_proj T1 i) (do_proj T2 i)))) hs1 ->
    ~ Var TID i ->
    ~ In T1 i ->
    ~ In T2 i ->
    prod (Hist.m_proj n2 hs2) (Hist.m_proj n1 hs2) = hs1.
  Proof.
    intros.
    rewrite i_subst_seq in H2.
    rewrite i_subst_seq in H2.
    apply run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in, t1_neq_tid.
    }
    assert (t2_nin_proj_i: ~ In T2 (proj i)). {
      intros N.
      contradict H5.
      eauto using in_proj_to_in, t2_neq_tid.
    }
    (* Simplify Hra: *)
    assert (~ In T2 (i_subst T1 (NNum n2) (do_proj T1 i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply in_i_subst_neq in N; auto using t1_neq_t2. {
        unfold do_proj in N.
        apply in_i_subst_neq in N; auto using t2_neq_tid.
        intros M.
        inversion M.
        assert (T2 <> T1) by auto using t1_neq_t2.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite i_subst_not_in in Hra; auto.
    eapply run_do_proj in Hra; eauto using t1_neq_tid.
    subst.
    (* Simplify Hrb *)
    rewrite i_subst_subst_neq in Hrb; auto using t1_neq_t2.
    assert (~ In T1 (i_subst T2 (NNum n1) (do_proj T2 i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply in_i_subst_neq in N; auto using t1_neq_t2. {
        unfold do_proj in N.
        apply in_i_subst_neq in N; auto using t1_neq_tid.
        intros M.
        inversion M.
        tasks_absurd.
      }
      intros M.
      inversion M.
    }
    rewrite i_subst_not_in in Hrb; auto.
    eapply run_do_proj in Hrb; eauto using t2_neq_tid.
    subst.
    reflexivity.
  Qed.

  Lemma in_branch_inv:
    forall l hs x i1 i2,
    Run (I:=SymHist.SymAcc) (Branch x l i1 i2) hs ->
    forall n,
    List.In n l ->
    exists hs2,
    incl hs2 hs /\ Run (seq (i_subst x (NNum n) i1) i2) hs2.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H0; subst; clear H0;
        inversion H; subst; clear H. {
      exists hs1.
      repeat split; auto using incl_app_refl_l.
    }
    assert (IHl := IHl hs2 x i1 i2 H8 _ H1).
    destruct IHl as (hs3, (Hinc, Hr)).
    exists hs3.
    split; auto.
    apply incl_appr.
    auto.
  Qed.

  Lemma in_decl_inv:
    forall e1 e2 hs x i1 i2,
    Run (I:=SymHist.SymAcc) (Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    ((n1 >= n2 /\ Run i2 hs)
    \/
    forall n,
    n1 <= n < n2 ->
    exists hs2,
    incl hs2 hs /\ Run (seq (i_subst x (NNum n) i1) i2) hs2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst.
    exists n1.
    exists n2.
    split; auto.
    split; auto.
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    intros.
    apply (Ha n) in H.
    eapply in_branch_inv in H6; eauto.
  Qed.
*)
(*
  Lemma translate_proper:
    forall e e' m,
    Conc2.REq e e' ->
    FRun (translate e) m ->
    FRun (translate e') m.
  Proof.
    induction e; intros.
    - 
  Qed.
*)
  Lemma soundness_2:
    forall i nx a1,
    Conc2.AccIn nx a1 i ->
    forall ny a2,
    Conc2.AccIn ny a2 i ->
    nx < TID_COUNT ->
    ny < TID_COUNT ->
    TPairIn (a1,a2) i.
  Proof.
    induction i; intros.
    - inversion H.
    - inversion H; subst; clear H.
      + inversion H0; subst; clear H0.
        * eapply t_pair_in_true_true; eauto.
          -- admit.
          -- admit.
        * 
      (*
      apply translate_inv_access in H3.
      destruct H3 as (vs1, (vs2, (R, (Hl, (Hm1, Hm2))))).
      apply R.
      admit.*)
    - inversion H1; subst; clear H1.
      + apply IHAccIn in H8; auto.
        admit.
      + 
    - admit.
    - 
  Qed.

  Theorem soundness_1
      (i:Conc2.inst)
      (*
      (T1_nin_i: ~ In T1 i)
      (T2_nin_i: ~ In T2 i)
      (TID_nvar_i: ~ Var TID i)
      *)
    :
    forall m_c,
    Conc2.RunAll TID_COUNT i m_c ->
    forall m_h,
    (* (forall x, MIn x m_l -> access_tid x < TID_COUNT) -> *)
    Run (translate i) m_h ->
    Hist.PairInclMPair m_c m_h.
  Proof.
    intros.
    unfold Hist.PairInclMPair.
    intros x y Hx Hy.
    assert (Hi := Hx).
    eapply Conc2.run_all_inv_in in Hi; eauto.
    destruct Hi as (nx, (h_x, (?, (Hrx, (Hjx, Hix))))).
    assert (Hi := Hy).
    eapply Conc2.run_all_inv_in in Hi; eauto.
    destruct Hi as (ny, (h_y, (?, (Hry, (Hjy, Hiy))))).
    clear Hjy H Hjx.
    apply run_inv_decl in H1.
    destruct H1 as (n1, (n2, (Hn1, (Hn2, Hx)))).
    inversion Hn1; subst; clear Hn1.
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    subst.
    clear Hn2.
    destruct Hx as [(N,Hx)|(hss, (?, Hx))]. {
      assert (1 < TID_COUNT) by auto using tid_count_1_lt.
      Import Omega.
      omega.
    }
    subst.
    (* We simplified our assumption [SymHist.Run (translate i) m_h]
       as [Hx]. *)  
    assert (x_lt_tc: access_tid x < TID_COUNT) by eauto.
    assert (y_lt_tc: access_tid y < TID_COUNT) by eauto.
    (* Check the tids of both accesses. *)
    assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
      by omega.
    destruct Ht as [Ht | [Ht|Ht]].
    - (* x = y *)
      omega.
    - (* x < y *)
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= access_tid y < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid y) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply SymExec.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply SymExec.run_inv_decl in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid x < access_tid y) by omega.
      assert (Hx := Hx (access_tid x) Hb).
      destruct Hx as (hs, (Hx,Hz)).
      remove_eq T1 T2.
      (* Now we want to handle the seq in Hx *)
      apply SymExec.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto.
      subst.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
      apply m_pair_in_prod_2.
      + auto using Hist.in_m_proj.
      + auto using Hist.in_m_proj.
    - (* y < x *)
      Import Omega.
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= access_tid x < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid x) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply SymExec.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      remove_eq T1 T1.
      apply SymExec.run_inv_decl in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid y < access_tid x) by omega.
      assert (Hx := Hx (access_tid y) Hb).
      destruct Hx as (hs, (Hx,Hz)).
      remove_eq T1 T2.
      (* Now we want to handle the seq in Hx *)
      apply SymExec.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto.
      subst.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
      apply m_pair_in_prod_1.
      + auto using Hist.in_m_proj.
      + auto using Hist.in_m_proj.
  Qed.
*)
  (**
    Top-level soundness theorem.
    *)

  Corollary soundness:
    forall m_c m_h i,
    (*(forall x, MIn x m_l -> access_tid x < TID_COUNT) ->*)
    ~ Conc2.In T1 i ->
    ~ Conc2.In T2 i ->
    ~ Conc2.Var TID i ->
    Hist.MSafeStrong m_h ->
    Conc2.RunAll TID_COUNT i m_c ->
    Run (translate i) m_h ->
    Hist.Safe m_c.
  Proof.
    intros.
    eapply Hist.m_safe_strong_to_safe in H2; eauto.
    + eapply Hist.msafe_to_safe in H2; eauto.
    eapply soundness_1; eauto.
  Qed.
End Defs.
End Compiler.