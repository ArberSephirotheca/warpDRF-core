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
  Lemma i_in_to_t_in:
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

  Lemma t_in_to_i_in:
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

  Lemma soundness_2:
    forall i a1,
    Conc2.IIn a1 i ->
    forall a2,
    Conc2.IIn a2 i ->
    TPairIn (a1,a2) i.
  Proof.
    intros.
    apply i_in_to_t_in in H.
    apply i_in_to_t_in in H0.
    unfold TPairIn.
    auto.
  Qed.

  Corollary soundness:
    forall m_c m_h i,
    ~ Conc2.In T1 i ->
    ~ Conc2.In T2 i ->
    ~ Conc2.Var TID i ->
    Hist.MSafeStrong m_h ->
    Conc2.RunAll TID_COUNT i m_c ->
    Run (translate i) m_h ->
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
    eapply run_i_pair_in_to_m_pair_in; eauto.

    (* Simplify the assumption of run for t1 *)
    assert (Hrx := Hrc).
    eapply Conc2.run_all_inv_in with (x0:=x) in Hrx; eauto.
    destruct Hrx as (nx, (h_x, (?, (Hrx, (_, Hix))))).
    assert (nx = access_tid x). {
      symmetry.
      eapply Conc2.run_access_tid; eauto.
    }
    subst.
    eapply Conc2.in_to_i_in in Hix; eauto.
    clear Hrx Hix'.

    (* Simplify the assumption of run for t2 *)
    assert (Hry := Hrc).
    eapply Conc2.run_all_inv_in with (x0:=y) in Hry; eauto.
    destruct Hry as (ny, (h_y, (?, (Hry, (_, Hiy))))).
    assert (ny = access_tid y). {
      symmetry.
      eapply Conc2.run_access_tid; eauto.
    }
    subst.
    eapply Conc2.in_to_i_in in Hiy; eauto.
    clear Hry Hiy'.

    (* We no longer need run all *)
    clear Hrc.

    (* Now we will find the right pair *)
    unfold translate, do_proj.

    (* Useful results *)
    assert (t1_nin_p: ~ In T1 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t1_neq_tid.
    }
    assert (t2_nin_p: ~ In T2 (proj i)). {
      intros N.
      apply in_proj_to_in in N; auto using t2_neq_tid.
    }

    apply i_in_to_t_in in Hix.
    apply i_in_to_t_in in Hiy.

    assert (X: access_tid x < access_tid y \/ access_tid y < access_tid x). {
      Import Omega.
      omega.
    }
    destruct X as [Hlt|Hlt]. {
      (* We know that x < y, thus T1 = y and T2 = x *)
      apply i_pair_in_decl with (n0:=access_tid y) (n1:=1) (n2:=TID_COUNT);
        auto using n_step_num with *.
      simpl.
      (* clean up goal *)
      remove_eq T1 T1.
      remove_eq T1 T2.
      rewrite i_subst_subst_trans; auto.
      assert (~ In T1 (i_subst TID (NVar T2) (proj i))). {
        intros N.
        apply in_inv_subst_in in N; auto using t1_neq_t2, t1_neq_tid.
      }
      rewrite i_subst_not_in with (x0:=T1); auto.
      (* fix the second biding *)
      apply i_pair_in_decl with (n0:=access_tid x) (n1:=0) (n2:=access_tid y);
        auto using n_step_num with *.
      simpl.
      rewrite i_subst_subst_trans; auto.
      apply i_pair_in_seq_both.
      simpl.
      right.
      split. {
        rewrite i_subst_not_in. {
          apply SHCompiler2.t_in_to_i_in; auto.
        }
        intros N.
        apply in_inv_subst_1 in N; auto.
      }
      apply SHCompiler2.t_in_to_i_in; auto.
    }
      (* We know that y < x, thus T1 = x and T2 = y *)
      apply i_pair_in_decl with (n0:=access_tid x) (n1:=1) (n2:=TID_COUNT);
        auto using n_step_num with *.
      simpl.
      (* clean up goal *)
      remove_eq T1 T1.
      remove_eq T1 T2.
      rewrite i_subst_subst_trans; auto.
      assert (~ In T1 (i_subst TID (NVar T2) (proj i))). {
        intros N.
        apply in_inv_subst_in in N; auto using t1_neq_t2, t1_neq_tid.
      }
      rewrite i_subst_not_in with (x0:=T1); auto.
      (* fix the second biding *)
      apply i_pair_in_decl with (n0:=access_tid y) (n1:=0) (n2:=access_tid x);
        auto using n_step_num with *.
      simpl.
      rewrite i_subst_subst_trans; auto.
      apply i_pair_in_seq_both.
      simpl.
      left.
      split. {
        rewrite i_subst_not_in. {
          apply SHCompiler2.t_in_to_i_in; auto.
        }
        intros N.
        apply in_inv_subst_1 in N; auto.
      }
      apply SHCompiler2.t_in_to_i_in; auto.
  Qed.

End Defs.
End Compiler.