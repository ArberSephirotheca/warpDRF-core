Require Import Coq.Lists.List.

Require Coq.omega.Omega.

Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import AccExp.

Require Import Tasks.

Require Import SymExec2.
Require Import SHCompiler2.

Require Conc2.

Import ListNotations.

Section Compiler.
  Import SHCompiler2.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

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

    apply c_i_in_to_t_in in Hix.
    apply c_i_in_to_t_in in Hiy.

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

  Corollary completeness:
    forall m_c m_h i,
    ~ Conc2.In T1 i ->
    ~ Conc2.In T2 i ->
    ~ Conc2.Var TID i ->
    Hist.Safe m_c ->
    Conc2.RunAll TID_COUNT i m_c ->
    Run (translate i) m_h ->
    Hist.MSafeStrong m_h.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hv Hs1 Hrc Hrh.
    unfold Hist.MSafeStrong in *.
    unfold Hist.Safe in *.
    intros x y Hneq Hp.
    eapply SymExec2.run_m_pair_in_to_i_pair_in in Hp; eauto.
    apply i_pair_in_to_i_in in Hp.
    destruct Hp as (Hxi, Hyi).
    apply i_in_translate_to_t_in in Hxi; auto.
    destruct Hxi as (Hxi, Hlt_x).
    apply i_in_translate_to_t_in in Hyi; auto.
    destruct Hyi as (Hyi, Hlt_y).
    apply t_in_to_c_i_in in Hxi.
    apply t_in_to_c_i_in in Hyi.
    apply Hs1; auto; clear Hs1.
    - eapply Conc2.run_all_i_in_to_in in Hxi; eauto.
    - eapply Conc2.run_all_i_in_to_in in Hyi; eauto.
  Qed.
End Defs.
End Compiler.