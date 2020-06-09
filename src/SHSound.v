Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.funind.Recdef.

Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
(*
Require Aniceto.Graphs.Graph.
*)

Require Conc.
Require LoopFree.

Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Acc.
Require Import Util.
Require Import SymHist.
Require Import RangeList.
Require Import SHCompiler.
Require Import Tasks.
Require Import SetTh.

Import ListNotations.


Section Compiler.
  Import Conc.
  Import SHCompiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Lemma in_to_in_proj:
    forall x i,
    Conc.In x i ->
    SymHist.In x (proj i).
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H;
        auto using SymHist.in_acc_1, SymHist.in_acc_3, SymHist.in_decl_1, SymHist.in_decl_2, SymHist.in_decl_3,
          SymHist.in_decl_4, SymHist.in_branch_1, SymHist.in_branch_2, SymHist.in_branch_3.
  Qed.

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (Conc.i_subst x (NNum n) i) = SymHist.i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
  Qed.


  Lemma proj_seq:
    forall i1 i2,
    proj (Conc.seq i1 i2) = SymHist.seq (proj i1) (proj i2).
  Proof.
    induction i1; intros; simpl.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
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

  Theorem run_m_proj:
    forall i hs2,
    LoopFree.Run i hs2 ->
    forall n hs1,
    n < TID_COUNT ->
    SymHist.Run (SymHist.i_subst TID (NNum n) (proj i)) hs1 ->
    ~ Conc.Var TID i ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    intros i hs2 H.
    induction H; intros.
    - inversion H0; subst; clear H0.
      reflexivity.
    - inversion H2; subst; clear H2.
      apply Conc.var_not_in_acc in H3.
      assert (IHRun := IHRun _ _ H1 H8 H3).
      subst.
      destruct (var_eq_dec_rw_eq TID) as (?, R).
      rewrite R in *; clear R.
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
      assert (~ Conc.Var TID (Conc.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        eauto using Conc.var_loop_to_for.
      }
      eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (~ Conc.Var TID (Conc.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        auto using Conc.var_loop_cons.
      }
      apply IHRun2 in H11; auto; clear IHRun2.
      subst.
      rewrite Hist.m_proj_app.
      assert (Hist.m_proj n0 hs1 = hs3). {
        destruct (Set_VAR.MF.eq_dec TID x). {
          apply Conc.var_not_in_loop in H3.
          destruct H3 as (?, _).
          contradiction.
        }
        apply IHRun1; auto; clear IHRun1.
        + rewrite SymHist.i_subst_subst_neq in H10; auto.
          rewrite <- SymHist.i_subst_seq in H10.
          rewrite <- i_subst_proj_rw in H10; auto.
          rewrite proj_seq in *.
          auto.
        + intros N.
          contradict H2.
          eauto using Conc.var_iter_loop.
      }
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (~ Conc.Var TID i2). {
        intros N.
        contradict H2.
        auto using Conc.var_loop_3.
      }
      auto.
  Qed.

  Lemma run_do_proj (t:var):
    forall i hs2,
    LoopFree.Run i hs2 ->
    forall n hs1,
    n < TID_COUNT -> 
    SymHist.Run (SymHist.i_subst t (NNum n) (do_proj t i)) hs1 ->
    ~ Conc.Var TID i ->
    ~ Conc.In t i ->
    t <> TID ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    unfold do_proj.
    intros.
    rewrite SymHist.i_subst_subst_trans in H1; auto.
    + eapply run_m_proj; eauto.
    + intros N.
      contradict H3.
      apply in_proj_to_in; auto.
  Qed.

  Lemma run_do_proj_do_proj:
    forall i hs2,
    LoopFree.Run i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT ->
    n2 < TID_COUNT ->
    SymHist.Run
        (SymHist.i_subst T2 (NNum n1)
           (SymHist.i_subst T1 (NNum n2) (SymHist.seq (do_proj T1 i) (do_proj T2 i)))) hs1 ->
    ~ Conc.Var TID i ->
    ~ Conc.In T1 i ->
    ~ Conc.In T2 i ->
    prod (Hist.m_proj n2 hs2) (Hist.m_proj n1 hs2) = hs1.
  Proof.
    intros.
    rewrite SymHist.i_subst_seq in H2.
    rewrite SymHist.i_subst_seq in H2.
    apply SymHist.run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ SymHist.In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in, t1_neq_tid.
    }
    assert (t2_nin_proj_i: ~ SymHist.In T2 (proj i)). {
      intros N.
      contradict H5.
      eauto using in_proj_to_in, t2_neq_tid.
    }
    (* Simplify Hra: *)
    assert (~ SymHist.In T2 (SymHist.i_subst T1 (NNum n2) (do_proj T1 i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply SymHist.in_i_subst_neq in N; auto using t1_neq_t2. {
        unfold do_proj in N.
        apply SymHist.in_i_subst_neq in N; auto using t2_neq_tid.
        intros M.
        inversion M.
        assert (T2 <> T1) by auto using t1_neq_t2.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite SymHist.i_subst_not_in in Hra; auto.
    eapply run_do_proj in Hra; eauto using t1_neq_tid.
    subst.
    (* Simplify Hrb *)
    rewrite SymHist.i_subst_subst_neq in Hrb; auto using t1_neq_t2.
    assert (~ SymHist.In T1 (SymHist.i_subst T2 (NNum n1) (do_proj T2 i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply SymHist.in_i_subst_neq in N; auto using t1_neq_t2. {
        unfold do_proj in N.
        apply SymHist.in_i_subst_neq in N; auto using t1_neq_tid.
        intros M.
        inversion M.
        tasks_absurd.
      }
      intros M.
      inversion M.
    }
    rewrite SymHist.i_subst_not_in in Hrb; auto.
    eapply run_do_proj in Hrb; eauto using t2_neq_tid.
    subst.
    reflexivity.
  Qed.

  Lemma in_branch_inv:
    forall l hs x i1 i2,
    SymHist.Run (SymHist.Branch x l i1 i2) hs ->
    forall n,
    List.In n l ->
    exists hs2,
    incl hs2 hs /\ SymHist.Run (SymHist.seq (SymHist.i_subst x (NNum n) i1) i2) hs2.
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
    SymHist.Run (SymHist.Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    ((n1 >= n2 /\ SymHist.Run i2 hs)
    \/
    forall n,
    n1 <= n < n2 ->
    exists hs2,
    incl hs2 hs /\ SymHist.Run (SymHist.seq (SymHist.i_subst x (NNum n) i1) i2) hs2).
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

  Theorem soundness_1
      (i:Conc.inst)
      (T1_nin_i: ~ Conc.In T1 i)
      (T2_nin_i: ~ Conc.In T2 i)
      (TID_nvar_i: ~ Conc.Var TID i)
    :
    forall hs1,
    LoopFree.Run i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    SymHist.Run (translate i) hs2 ->
    Hist.APairIncl hs1 hs2.
  Proof.
    unfold translate.
    intros.
    unfold Hist.APairIncl.
    intros.
    apply SymHist.run_decl_inv in H1.
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
      apply SymHist.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply SymHist.run_decl_inv in Hr1.
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
      apply SymHist.run_inv_seq in Hx.
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
      apply SymHist.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      remove_eq T1 T1.
      apply SymHist.run_decl_inv in Hr1.
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
      apply SymHist.run_inv_seq in Hx.
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

  (**
    Top-level soundness theorem.
    *)

  Corollary soundness:
    forall hs1 hs2 i,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    ~ Conc.In T1 i ->
    ~ Conc.In T2 i ->
    ~ Conc.Var TID i ->
    Hist.MSafeStrong hs2 ->
    LoopFree.Run i hs1 ->
    SymHist.Run (translate i) hs2 ->
    Hist.MSafe hs1.
  Proof.
    intros.
    eapply Hist.m_safe_strong_to_m_safe; eauto.
    eapply soundness_1; eauto.
  Qed.
End Defs.
End Compiler.