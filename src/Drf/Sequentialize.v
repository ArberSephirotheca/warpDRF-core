From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

From Faial.Core Require Import Util.

From Faial.Core Require Import Var.
From Faial.Expr Require Import Pure.N.Exp.
From Faial.Expr Require Import Pure.B.Exp.
From Faial.Expr Require Import Pure.A.Exp.
From Faial.Expr Require Import Pure.R.Exp.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import AVal.
Require TLang.

Import ListNotations.

Section Defs.
  Context {T:Tasks}.
  Section TRACE.
  Variable tid:Pure.N.Exp.nexp.

  Fixpoint trace (c:Lang.t) : TLang.inst :=
    match c with
    | Lang.Skip => TLang.Skip
    | Lang.Seq i j => TLang.Seq (trace i) (trace j)
    | Lang.If b i j => TLang.If (B.Exp.to_pure tid b) (trace i) (trace j)
    | Lang.MemAcc a => TLang.MemAcc (A.Exp.to_pure tid a)
    | Lang.For x r i => TLang.BoundedDecl x (R.Exp.to_pure tid r) (trace i)
    | Lang.Decl x i => TLang.Decl x (trace i)
    end.
  End TRACE.

  Definition sequentialize c : TLang.inst :=
    TLang.BoundedDecl T1 (NNum 1, NNum TID_COUNT)
      (TLang.BoundedDecl T2 (NNum 0, NVar T1)
        (TLang.Seq (trace (NVar T1) c) (trace (NVar T2) c))).

  (* ----------------------- SUBSTITUTION --------------------------- *)

  Lemma i_subst_trace_rw:
    forall tid x i v,
    ~ NFree x tid ->
    trace tid (Subst.f x (N.Exp.from_pure v) i) =
    TLang.i_subst x v (trace tid i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite B.Exp.b_subst_to_pure; auto.
      rewrite IHi2; auto.
      rewrite N.Exp.to_pure_from_pure.
      auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite N.Exp.n_subst_to_pure; auto.
      simpl in *.
      destruct a.
      unfold a_subst.
      simpl.
      rewrite N.Exp.to_pure_from_pure.
      rewrite n_subst_not_free with (n:=tid); auto.
    - rewrite R.Exp.r_subst_to_pure; auto.
      rewrite N.Exp.to_pure_from_pure.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_trace_num_rw:
    forall tid x i n,
    ~ NFree x tid ->
    trace tid (Subst.f x (N.Exp.NNum n) i) =
    TLang.i_subst x (NNum n) (trace tid i).
  Proof.
    intros.
    assert (Hx := i_subst_trace_rw tid x i (NNum n) H).
    simpl in *.
    auto.
  Qed.

  (* ---------------------------- IN PROJECTION -------------------- *)

  Lemma in_trace_to_in:
    forall x tid i,
    ~ NFree x tid ->
    TLang.Occurs x (trace tid i) ->
    Occurs.t x i.
  Proof.
    induction i; simpl; intros; auto.
    all: intuition.
    - eauto using B.Exp.b_free_to_pure.
    - destruct a.
      unfold AFree in *.
      simpl in *.
      intuition.
      eauto using N.Exp.n_free_to_pure. 
    - eauto using R.Exp.r_free_to_pure.
  Qed.

  Lemma var_inv_trace:
    forall x i tid,
    TLang.Var x (trace tid i) ->
    Var.t x i.
  Proof.
    induction i.
    all: simpl.
    all: intros.
    all: intuition.
    all: eauto.
  Qed.

  (* ------------------------- IN PROJECTION ----------------------- *)

  Inductive PIn a: Lang.t -> Prop :=
  | p_in_access:
    forall e,
    SIMT.A.Exp.AStep (AVal.av_owner a) e a ->
    PIn a (Lang.MemAcc e)
  | p_in_seq_l:
    forall i j,
    PIn a i ->
    PIn a (Lang.Seq i j)
  | p_in_seq_r:
    forall i j,
    PIn a j ->
    PIn a (Lang.Seq i j)
  | p_in_if_true:
    forall b i j,
    SIMT.B.Exp.BStep (AVal.av_owner a) b true ->
    PIn a i ->
    PIn a (Lang.If b i j)
  | p_in_if_false:
    forall b i j,
    SIMT.B.Exp.BStep (AVal.av_owner a) b false ->
    PIn a j ->
    PIn a (Lang.If b i j)
  | p_in_for:
    forall r n x i,
    SIMT.R.Exp.RPick (AVal.av_owner a) r n ->
    PIn a (Subst.f x (SIMT.N.Exp.NNum n) i) ->
    PIn a (Lang.For x r i)
  | p_in_decl:
    forall x i,
    PIn a i ->
    PIn a (Lang.Decl x i)
  .

  Lemma n_step_to_pure:
    forall tid e n,
    NStep (N.Exp.to_pure (NNum tid) e) n ->
    N.Exp.NStep tid e n.
  Proof.
    induction e; simpl; intros.
    all: invc H.
    - constructor.
    - constructor.
    - constructor.
      all: auto.
  Qed.

  Lemma b_step_to_pure:
    forall tid e n,
    BStep (B.Exp.to_pure (NNum tid) e) n ->
    B.Exp.BStep tid e n.
  Proof.
    induction e; simpl; intros.
    all: invc H.
    all: constructor.
    all: auto using n_step_to_pure.
  Qed.

  Lemma i_in_to_p_in:
    forall a i,
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i) ->
    PIn a i.
  Proof.
    intros a i Hi.
    remember (trace _ i) as j.
    generalize dependent i.
    induction Hi; intros i' Heq.
    all: destruct i'.
    all: invc Heq.
    all: simpl in *.
    - destruct a0.
      simpl in *.
      invc H.
      simpl in *.
      constructor.
      constructor.
      eauto using n_step_to_pure.
    - constructor; auto.
    - constructor 3; auto.
    - eauto using p_in_if_true, b_step_to_pure.
    - eauto using p_in_if_false, b_step_to_pure.
    - apply R.Exp.r_pick_to_pure in H.
      apply p_in_for with (n:=n); auto.
      apply IHHi.
      rewrite i_subst_trace_num_rw; auto.
    - apply p_in_decl.
      apply IHHi.
      reflexivity.
  Qed.

  Lemma p_in_to_i_in:
    forall a i,
    PIn a i ->
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    intros a i Hi.
    induction Hi; simpl.
    - eapply TLang.i_in_access; eauto.
      rewrite A.Exp.a_step_to_pure.
      assumption.
    - apply TLang.i_in_seq_l; auto.
    - apply TLang.i_in_seq_r; auto.
    - apply TLang.i_in_if_true; auto.
      rewrite B.Exp.b_step_to_pure.
      assumption.
    - apply TLang.i_in_if_false; auto.
      rewrite B.Exp.b_step_to_pure.
      assumption.
    - rewrite <- R.Exp.r_pick_to_pure in H.
      apply TLang.i_in_bounded_decl with (n:=n); auto.
      rewrite <- i_subst_trace_rw; auto.
    - apply TLang.i_in_decl. auto.
  Qed.

  Lemma i_in_p_in_iff:
    forall a i,
    PIn a i <-> TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    split; auto using i_in_to_p_in, p_in_to_i_in.
  Qed.

  (* ----------------------------- IN TRANSLATION ------------------ *)

  Lemma u_in_to_p_in:
    forall a i,
    IIn.IIn a i ->
    PIn a i.
  Proof.
    intros a i Hi.
    induction Hi; intros;
      eauto using p_in_access,
        p_in_seq_l, p_in_seq_r,
        p_in_if_true, p_in_if_false.
    - eapply p_in_for; eauto.
    - eapply p_in_decl; eauto.
  Qed.

  Lemma p_in_to_u_in:
    forall a i,
    PIn a i ->
    IIn.IIn a i.
  Proof.
    intros.
    induction H; intros; auto using IIn.i_in_seq_l, IIn.i_in_seq_r.
    - eauto using IIn.i_in_access.
    - apply IIn.i_in_if_true; auto.
    - apply IIn.i_in_if_false; auto.
    - eapply IIn.i_in_for; eauto.
    - eapply IIn.i_in_decl; eauto.
  Qed.

  (* ------------------------- TIN TO IIN ------------------------ *)

  Lemma not_var_trace:
    forall x i,
    ~ Var.t x i ->
    forall tid,
    ~ TLang.Var x (trace tid i).
  Proof.
    intros.
    intros N.
    apply var_inv_trace in N.
    contradiction.
  Qed.

  Lemma u_in_to_t_in:
    forall a i,
    IIn.IIn a i ->
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    intros.
    apply p_in_to_i_in; auto.
    apply u_in_to_p_in; auto.
  Qed.

  Lemma t_in_to_u_in:
    forall a i,
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i) ->
    IIn.IIn a i.
  Proof.
    intros.
    eapply p_in_to_u_in; eauto.
    apply i_in_to_p_in; eauto.
  Qed.

  Lemma i_in_inv_access_tid:
    forall a tid i,
    TLang.IIn a (trace (NNum tid) i) ->
    tid = AVal.av_owner a.
  Proof.
    intros a t i Hi.
    remember (trace _ _) as j.
    generalize dependent i.
    induction Hi.
    all: intros i' heq.
    all: destruct i'; invc heq.
    all: eauto.
    - destruct a0.
      simpl in *.
      simpl in *.
      invc H.
      rename_hyp (NStep (NNum t) _) as hn.
      invc hn.
      reflexivity.
    - assert (IHHi := IHHi ((Subst.f v (N.Exp.NNum n) i')) ).
      rewrite i_subst_trace_num_rw in IHHi; auto.
  Qed.

  Lemma i_subst_trace_eq:
    forall v tid i,
    ~ NFree tid v ->
    ~ Occurs.t tid i ->
    TLang.i_subst tid v (trace (NVar tid) i) =
    trace v i.
  Proof.
    induction i; simpl; intros.
    all: auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite B.Exp.b_subst_to_pure_eq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite A.Exp.a_subst_to_pure_eq; auto.
    - rewrite IHi; auto.
      destruct (Set_VAR.MF.eq_dec tid v0). {
        subst.
        intuition.
      }
      rewrite R.Exp.r_subst_to_pure_eq; auto.
    - rewrite IHi; auto.
      destruct (Set_VAR.MF.eq_dec tid v0). {
        subst.
        intuition.
      }
      auto.
  Qed.

  Lemma i_in_sequentialize_to_t_in:
    forall i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    forall a,
    TLang.IIn a (sequentialize i) ->
    IIn.IIn a i /\ AVal.av_owner a < TID_COUNT.
  Proof.
    intros i t1_nin t2_nin a Hi.
    unfold sequentialize in Hi.

    invc Hi.

    (* Rename assumption (IIn a ...) *)
    match goal with
      H: TLang.IIn _ _ |- _ => rename H into Hi
    end.

    (* Do inversion and then clean up *)
    simpl in Hi.
    remove_eq T1 T2.
    remove_eq T1 T1.
    invc Hi.
 
    rename_hyp (TLang.IIn _ _) as Hi.
    simpl in Hi.
    (* Is a in T1 or in T2? *)
    (* Remove subst T1 (subst TID ... ) *)
    rewrite TLang.i_subst_not_occurs in Hi.
    2: {
      intros N.
      apply TLang.i_occurs_inv_subst_neq_num in N; auto.
      apply in_trace_to_in in N; auto.
      simpl.
      auto using t1_neq_t2.
    }

    assert (n < TID_COUNT). {
      eapply r_pick_to_lt; eauto using n_step_num.
    }
    assert (n0 < TID_COUNT). {
      assert (n0 < n) by (eapply r_pick_to_lt; eauto using n_step_num).
      auto with *.
    }

    invc Hi.
    all: rename_hyp (TLang.IIn _ _) as Hi.

    - (* a is in T1 *)
      rewrite i_subst_trace_eq in Hi; auto.
      assert (n = AVal.av_owner a) by eauto using i_in_inv_access_tid.
      subst.
      auto using t_in_to_u_in.

    - (* a is in T2 *)
      rewrite TLang.i_subst_not_occurs with (x:=T1) in Hi.
      2: {
        intros N.
        apply in_trace_to_in in N; auto.
        simpl.
        auto using t1_neq_t2.
      }
      rewrite i_subst_trace_eq in Hi; auto.
      assert (n0 = AVal.av_owner a) by eauto using i_in_inv_access_tid.
      subst.
      auto using t_in_to_u_in.
  Qed.

  (* ===================== Main results ========================= *)

  Lemma t_pair_in_lt:
    forall i x y,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    AVal.av_owner x < TID_COUNT ->
    IIn.IIn x i ->
    AVal.av_owner y < TID_COUNT ->
    IIn.IIn y i ->
    AVal.av_owner x < AVal.av_owner y ->
    TLang.IPairIn (x, y)
      (TLang.BoundedDecl T1 (NNum 1, NNum TID_COUNT)
         (TLang.BoundedDecl T2 (NNum 0, NVar T1)
            (TLang.Seq (trace (NVar T1) i)
               (trace (NVar T2) i)))).
  Proof.
    intros.
    apply TLang.i_pair_in_bounded_decl with (n:=AVal.av_owner y) (r:=(NNum 1, NNum TID_COUNT)).
    1: { eapply r_pick_def; eauto using n_step_num with *. }
    simpl.
    (* clean up goal *)
    remove_eq T1 T1.
    remove_eq T1 T2.
    apply TLang.i_pair_in_bounded_decl with (n:=AVal.av_owner x) (r:=(NNum 0, NNum (AVal.av_owner y))).
    1: { eapply r_pick_def; eauto using n_step_num with *. }

    simpl.
    apply TLang.i_pair_in_seq_both.
    simpl.
    right.
    split. {
      rewrite TLang.i_subst_not_occurs. {
        rewrite i_subst_trace_eq; auto.
        apply u_in_to_t_in; auto.
      }
      intros N.
      apply TLang.i_occurs_inv_subst_neq_num in N; auto.
      apply in_trace_to_in in N; auto.
      simpl.
      auto using t1_neq_t2.
    }
    rewrite TLang.i_subst_not_occurs with (x:=T1).
    2: {
      intros N.
      apply in_trace_to_in in N; auto.
      simpl.
      auto using t1_neq_t2.
    }
    rewrite i_subst_trace_eq; auto.
    apply u_in_to_t_in; auto.
  Qed.
(*
  Corollary soundness:
    forall m_c m_h i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    Hist.Safe m_h ->
    Run.RunAll TID_COUNT i m_c ->
    TLang.NRun (sequentialize i) m_h ->
    Hist.Safe m_c.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hs1 Hrc Hrh.
    unfold Hist.Safe.
    intros x y Hix' Hiy'.

    assert (av_owner x < TID_COUNT) by eauto using Run.run_all_inv_in_eq.
    assert (av_owner y < TID_COUNT) by eauto using Run.run_all_inv_in_eq.

    (* Simplify the goal *)
    destruct (PeanoNat.Nat.eq_dec (AVal.av_owner x) (AVal.av_owner y)). {
      auto using A.Exp.a_safe_eq_tid.
    }
    assert (hp: PairInUtil.PairIn (x, y) m_c) by eauto using PairInUtil.pair_in_def.

(*     apply Hs1; auto; clear Hs1. *)

    (* Simplify the assumption of run for t1 *)
    assert (Hix: IIn.IIn x i). {
      assert (Hrx := Hrc).
      eapply Run.run_all_inv_in with (x:=x) in Hrx; eauto.
      destruct Hrx as (nx, (h_x, (?, (Hrx, (_, Hix))))).
      assert (nx = AVal.av_owner x). {
        symmetry.
        eapply Run.run_inv_in_eq; eauto.
      }
      subst.
      eapply IIn.run_in_to_i_in in Hix; eauto.
    }

    (* Simplify the assumption of run for t2 *)
    assert (Hiy : IIn.IIn y i). {
      assert (Hry := Hrc).
      eapply Run.run_all_inv_in with (x:=y) in Hry; eauto.
      destruct Hry as (ny, (h_y, (?, (Hry, (_, Hiy))))).
      assert (ny = AVal.av_owner y). {
        symmetry.
        eapply Run.run_inv_in_eq; eauto.
      }
      subst.
      eapply IIn.run_in_to_i_in in Hiy; eauto.
    }

    (* We no longer need run all *)
    clear Hrc.

    (* Now we will find the right pair *)
    unfold sequentialize in *.

    assert (X: AVal.av_owner x < AVal.av_owner y \/ AVal.av_owner y < AVal.av_owner x). {
      lia.
    }
    Search (av_owner _ < TID_COUNT).
    destruct X as [Hlt|Hlt]. {
      assert (TLang.IPairIn (x, y)
         (TLang.BoundedDecl T1 (NNum 1, NNum TID_COUNT)
            (TLang.BoundedDecl T2 (NNum 0, NVar T1)
               (TLang.Seq (trace (NVar T1) i) (trace (NVar T2) i)))))
      by (
      (* We know that x < y, thus T1 = y and T2 = x *)
      apply t_pair_in_lt; auto
      ).
      apply Hs1.
    }
    apply TLang.i_pair_in_sym.
    auto using t_pair_in_lt.
  Qed.
*)
  Lemma i_pair_in_1:
    forall p i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    (* --- *)
    TLang.IPairIn p (sequentialize i) ->
    CIn.CPairIn p i.
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
    eauto using CIn.c_pair_in_def, CIn.c_in_def.
  Qed.

  Lemma i_pair_in_2:
    forall i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    (* --- *)
    forall x y,
    (* Note that in this direction, the tids being different is a
     pre-conditions. *)
    AVal.av_owner x <> AVal.av_owner y -> 
    CIn.CPairIn (x,y) i ->
    TLang.IPairIn (x,y) (sequentialize i).
  Proof.
    intros.
    rename_hyp (CIn.CPairIn _ _) as hp.
    invc hp.
    rename_hyp (CIn.CIn x i) as hi1.
    rename_hyp (CIn.CIn y i) as hi2.

    (* Now we will find the right pair *)
    unfold sequentialize.

    invc hi1.
    rename_hyp (IIn.IIn x i) as hi1.
    invc hi2.
    rename_hyp (IIn.IIn y i) as hi2.

    assert (X: AVal.av_owner x < AVal.av_owner y \/ AVal.av_owner y < AVal.av_owner x). {
      lia.
    }
    destruct X as [Hlt|Hlt].
    - (* We know that x < y, thus T1 = y and T2 = x *)
      apply t_pair_in_lt; auto.
    - (* We know that y < x, thus T1 = x and T2 = y *)
      apply TLang.i_pair_in_sym.
      apply t_pair_in_lt; auto.
  Qed.

  Lemma sequentialize_subst_rw:
    forall x v i,
    ~ Var.t x i ->
    NClosed v ->
    x <> T1 ->
    x <> T2 ->
    TLang.i_subst x v (sequentialize i) = sequentialize (Subst.f x (N.Exp.from_pure v) i).
  Proof.
    intros.
    unfold sequentialize.
    simpl.
    remove_eq x T1.
    remove_eq x T2.
    rewrite i_subst_trace_rw.
    2: { simpl. auto. }
    rewrite i_subst_trace_rw.
    2: { simpl. auto. }
    f_equal.
  Qed.

  Corollary completeness2:
    forall m_c i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    Hist.Safe m_c ->
    Run.RunAll TID_COUNT i m_c ->
    forall h,
    TLang.NRun (sequentialize i) h ->
    Hist.Safe h.
  Proof.
    intros ? ? nin_t1 nin_t2 Hs1 Hr1 h Hr2.
    unfold Hist.Safe in *.
    intros x y hnx hny.
    assert (hx: av_owner x = av_owner y \/ av_owner x <> av_owner y) by lia.
    destruct hx. {
      auto using safe_owner.
    }
    assert (Hp: TLang.IPairIn (x, y) (sequentialize i)). {
      eapply TLang.n_run_pair_in_to_i_pair_in; eauto using PairInUtil.pair_in_def.
    }
    apply TLang.i_pair_in_to_i_in in Hp.
    destruct Hp as (Hxi, Hyi).
    apply i_in_sequentialize_to_t_in in Hxi; auto.
    destruct Hxi as (Hxi, Hlt_x).
    apply i_in_sequentialize_to_t_in in Hyi; auto.
    destruct Hyi as (Hyi, Hlt_y).
    apply Hs1; auto; clear Hs1.
    - eapply IIn.run_all_i_in_to_in in Hxi; eauto.
    - eapply IIn.run_all_i_in_to_in in Hyi; eauto.
  Qed.
(*
  Corollary completeness:
    forall m_c m_h i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    Hist.Safe m_c ->
    Run.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.MSafeStrong m_h.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hs1 Hrc Hrh.
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
    - eapply IIn.run_all_i_in_to_in in Hxi; eauto.
    - eapply IIn.run_all_i_in_to_in in Hyi; eauto.
  Qed.

  Corollary correctness:
    forall m_c m_h i,
    ~ Occurs.t T1 i ->
    ~ Occurs.t T2 i ->
    Run.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.Safe m_c <-> Hist.MSafeStrong m_h.
  Proof.
    split; intros. {
      eapply completeness; eauto.
    }
    eapply soundness; eauto.
  Qed.
  *)
End Defs.
