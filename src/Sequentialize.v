Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Util.

Require Import Var.
Require Import Pure.NExp.
Require Import Pure.BExp.
Require Import Pure.AExp.
Require Import Pure.RExp.
Require Import Tasks.
Require Import Tictac.

Require TLang.

Import ListNotations.

Section Defs.
  Context {T:Tasks}.
  Section TRACE.
  Variable tid:Pure.NExp.nexp.

  Fixpoint trace (c:ULang.inst) : TLang.inst :=
    match c with
    | ULang.Skip => TLang.Skip
    | ULang.Seq i j => TLang.Seq (trace i) (trace j)
    | ULang.If b i j => TLang.If (BExp.to_pure tid b) (trace i) (trace j)
    | ULang.MemAcc a => TLang.MemAcc (AExp.to_pure tid a)
    | ULang.For x r i => TLang.Decl x (RExp.to_pure tid r) (trace i)
    end.
  End TRACE.

  Definition sequentialize c : TLang.inst :=
    TLang.Decl T1 (NNum 1, NNum TID_COUNT)
      (TLang.Decl T2 (NNum 0, NVar T1)
        (TLang.Seq (trace (NVar T1) c) (trace (NVar T2) c))).

  (* ----------------------- SUBSTITUTION --------------------------- *)

  Lemma i_subst_trace_rw:
    forall tid x i v,
    ~ NFree x tid ->
    trace tid (ULang.i_subst x (NExp.from_pure v) i) =
    TLang.i_subst x v (trace tid i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite BExp.b_subst_to_pure; auto.
      rewrite IHi2; auto.
      rewrite NExp.to_pure_from_pure.
      auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite NExp.n_subst_to_pure; auto.
      simpl in *.
      destruct a.
      unfold a_subst.
      simpl.
      rewrite NExp.to_pure_from_pure.
      rewrite n_subst_not_free with (n:=tid); auto.
    - rewrite RExp.r_subst_to_pure; auto.
      rewrite NExp.to_pure_from_pure.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_trace_num_rw:
    forall tid x i n,
    ~ NFree x tid ->
    trace tid (ULang.i_subst x (NExp.NNum n) i) =
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
    ULang.Occurs x i.
  Proof.
    induction i; simpl; intros; auto.
    all: intuition.
    - eauto using BExp.b_free_to_pure.
    - destruct a.
      unfold AFree in *.
      simpl in *.
      intuition.
      eauto using NExp.n_free_to_pure. 
    - eauto using RExp.r_free_to_pure.
  Qed.

  Lemma var_inv_trace:
    forall x i tid,
    TLang.Var x (trace tid i) ->
    ULang.Var x i.
  Proof.
    induction i.
    all: simpl.
    all: intros.
    all: intuition.
    all: eauto.
  Qed.

  (* ------------------------- IN PROJECTION ----------------------- *)

  Inductive PIn a: ULang.inst -> Prop :=
  | p_in_access:
    forall e,
    SIMT.AExp.AStep (AVal.av_owner a) e a ->
    PIn a (ULang.MemAcc e)
  | p_in_seq_l:
    forall i j,
    PIn a i ->
    PIn a (ULang.Seq i j)
  | p_in_seq_r:
    forall i j,
    PIn a j ->
    PIn a (ULang.Seq i j)
  | p_in_if_true:
    forall b i j,
    SIMT.BExp.BStep (AVal.av_owner a) b true ->
    PIn a i ->
    PIn a (ULang.If b i j)
  | p_in_if_false:
    forall b i j,
    SIMT.BExp.BStep (AVal.av_owner a) b false ->
    PIn a j ->
    PIn a (ULang.If b i j)
  | p_in_for:
    forall r n x i,
    SIMT.RExp.RPick (AVal.av_owner a) r n ->
    PIn a (ULang.i_subst x (SIMT.NExp.NNum n) i) ->
    PIn a (ULang.For x r i)
  .

  Lemma n_step_to_pure:
    forall tid e n,
    NStep (NExp.to_pure (NNum tid) e) n ->
    NExp.NStep tid e n.
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
    BStep (BExp.to_pure (NNum tid) e) n ->
    BExp.BStep tid e n.
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
    - (*destruct i'; inversion Heq; subst; clear Heq.*)
      apply RExp.r_pick_to_pure in H.
      apply p_in_for with (n:=n); auto.
      apply IHHi.
      rewrite i_subst_trace_num_rw; auto.
  Qed.

  Lemma p_in_to_i_in:
    forall a i,
    PIn a i ->
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    intros a i Hi.
    induction Hi; simpl.
    - eapply TLang.i_in_access; eauto.
      rewrite AExp.a_step_to_pure.
      assumption.
    - apply TLang.i_in_seq_l; auto.
    - apply TLang.i_in_seq_r; auto.
    - apply TLang.i_in_if_true; auto.
      rewrite BExp.b_step_to_pure.
      assumption.
    - apply TLang.i_in_if_false; auto.
      rewrite BExp.b_step_to_pure.
      assumption.
    - rewrite <- RExp.r_pick_to_pure in H.
      apply TLang.i_in_decl with (n:=n); auto.
      rewrite <- i_subst_trace_rw; auto.
  Qed.

  Lemma i_in_p_in_iff:
    forall a i,
    PIn a i <-> TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    split; auto using i_in_to_p_in, p_in_to_i_in.
  Qed.
(*
  Lemma p_in_inv_access_tid:
    forall a n i,
    PIn a i ->
    AVal.av_owner a = n.
  Proof.
    intros.
    induction H; intros; auto.
    eapply access_step_inv_tid; eauto using n_step_num.
  Qed.
*)

  (* ----------------------------- IN TRANSLATION ------------------ *)

  Lemma u_in_to_p_in:
    forall a i,
    ULang.IIn a i ->
    PIn a i.
  Proof.
    intros a i Hi.
    induction Hi; intros;
      eauto using p_in_access,
        p_in_seq_l, p_in_seq_r,
        p_in_if_true, p_in_if_false.
    eapply p_in_for; eauto.
  Qed.

  Lemma p_in_to_u_in:
    forall a i,
    PIn a i ->
    ULang.IIn a i.
  Proof.
    intros.
    induction H; intros; auto using ULang.i_in_seq_l, ULang.i_in_seq_r.
    - eauto using ULang.i_in_access.
    - apply ULang.i_in_if_true; auto.
    - apply ULang.i_in_if_false; auto.
    - eapply ULang.i_in_for; eauto.
  Qed.

  (* ------------------------- TIN TO IIN ------------------------ *)

  Lemma not_var_trace:
    forall x i,
    ~ ULang.Var x i ->
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
    ULang.IIn a i ->
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i).
  Proof.
    intros.
    apply p_in_to_i_in; auto.
    apply u_in_to_p_in; auto.
  Qed.

  Lemma t_in_to_u_in:
    forall a i,
    TLang.IIn a (trace (NNum (AVal.av_owner a)) i) ->
    ULang.IIn a i.
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
    - assert (IHHi := IHHi ((ULang.i_subst v (NExp.NNum n) i')) ).
      rewrite i_subst_trace_num_rw in IHHi; auto.
  Qed.

  Lemma i_subst_trace_eq:
    forall v tid i,
    ~ NFree tid v ->
    ~ ULang.Occurs tid i ->
    TLang.i_subst tid v (trace (NVar tid) i) =
    trace v i.
  Proof.
    induction i; simpl; intros.
    all: auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite BExp.b_subst_to_pure_eq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite AExp.a_subst_to_pure_eq; auto.
    - rewrite IHi; auto.
      destruct (Set_VAR.MF.eq_dec tid v0). {
        subst.
        intuition.
      }
      rewrite RExp.r_subst_to_pure_eq; auto.
  Qed.

  Lemma i_in_sequentialize_to_t_in:
    forall i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    forall a,
    TLang.IIn a (sequentialize i) ->
    ULang.IIn a i /\ AVal.av_owner a < TID_COUNT.
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
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    AVal.av_owner x < TID_COUNT ->
    ULang.IIn x i ->
    AVal.av_owner y < TID_COUNT ->
    ULang.IIn y i ->
    AVal.av_owner x < AVal.av_owner y ->
    TLang.IPairIn (x, y)
      (TLang.Decl T1 (NNum 1, NNum TID_COUNT)
         (TLang.Decl T2 (NNum 0, NVar T1)
            (TLang.Seq (trace (NVar T1) i)
               (trace (NVar T2) i)))).
  Proof.
    intros.
    apply TLang.i_pair_in_decl with (n:=AVal.av_owner y) (r:=(NNum 1, NNum TID_COUNT)).
    1: { eapply r_pick_def; eauto using n_step_num with *. }
    simpl.
    (* clean up goal *)
    remove_eq T1 T1.
    remove_eq T1 T2.
    apply TLang.i_pair_in_decl with (n:=AVal.av_owner x) (r:=(NNum 0, NNum (AVal.av_owner y))).
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

  Corollary soundness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    Hist.MSafeStrong m_h ->
    ULang.RunAll TID_COUNT i m_c ->
    TLang.Run (sequentialize i) m_h ->
    Hist.Safe m_c.
  Proof.
    intros m_c m_h i nin_t1 nin_t2 Hs1 Hrc Hrh.
    unfold Hist.MSafeStrong in *.
    unfold Hist.Safe.
    intros x y Hix' Hiy'.

    (* Simplify the goal *)
    destruct (PeanoNat.Nat.eq_dec (AVal.av_owner x) (AVal.av_owner y)). {
      auto using AExp.a_safe_eq_tid.
    }
    apply Hs1; auto; clear Hs1.
    eapply TLang.run_i_pair_in_to_m_pair_in; eauto.

    (* Simplify the assumption of run for t1 *)
    assert (Hrx := Hrc).
    eapply ULang.run_all_inv_in with (x:=x) in Hrx; eauto.
    destruct Hrx as (nx, (h_x, (?, (Hrx, (_, Hix))))).
    assert (nx = AVal.av_owner x). {
      symmetry.
      eapply ULang.run_inv_in_eq; eauto.
    }
    subst.
    eapply ULang.run_in_to_i_in in Hix; eauto.
    clear Hrx Hix'.

    (* Simplify the assumption of run for t2 *)
    assert (Hry := Hrc).
    eapply ULang.run_all_inv_in with (x:=y) in Hry; eauto.
    destruct Hry as (ny, (h_y, (?, (Hry, (_, Hiy))))).
    assert (ny = AVal.av_owner y). {
      symmetry.
      eapply ULang.run_inv_in_eq; eauto.
    }
    subst.
    eapply ULang.run_in_to_i_in in Hiy; eauto.
    clear Hry Hiy'.

    (* We no longer need run all *)
    clear Hrc.

    (* Now we will find the right pair *)
    unfold sequentialize.

    assert (X: AVal.av_owner x < AVal.av_owner y \/ AVal.av_owner y < AVal.av_owner x). {
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
    (* --- *)
    forall x y,
    (* Note that in this direction, the tids being different is a
     pre-conditions. *)
    AVal.av_owner x <> AVal.av_owner y -> 
    ULang.CPairIn (x,y) i ->
    TLang.IPairIn (x,y) (sequentialize i).
  Proof.
    intros.
    rename_hyp (ULang.CPairIn _ _) as hp.
    invc hp.
    rename_hyp (ULang.CIn x i) as hi1.
    rename_hyp (ULang.CIn y i) as hi2.

    (* Now we will find the right pair *)
    unfold sequentialize.

    invc hi1.
    rename_hyp (ULang.IIn x i) as hi1.
    invc hi2.
    rename_hyp (ULang.IIn y i) as hi2.

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
(*
  Lemma trace_subst_rw:
    forall x v u,
    ~ ULang.Var x u ->
    NClosed v ->
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
*)
  Lemma sequentialize_subst_rw:
    forall x v i,
    ~ ULang.Var x i ->
    NClosed v ->
    x <> T1 ->
    x <> T2 ->
    TLang.i_subst x v (sequentialize i) = sequentialize (ULang.i_subst x (NExp.from_pure v) i).
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

  Corollary completeness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
    Hist.Safe m_c ->
    ULang.RunAll TID_COUNT i m_c ->
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
    - eapply ULang.run_all_i_in_to_in in Hxi; eauto.
    - eapply ULang.run_all_i_in_to_in in Hyi; eauto.
  Qed.

  Corollary correctness:
    forall m_c m_h i,
    ~ ULang.Occurs T1 i ->
    ~ ULang.Occurs T2 i ->
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
