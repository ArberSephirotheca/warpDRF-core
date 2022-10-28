Require Import Coq.Lists.List.

Require Import Coq.micromega.Lia.

Require Import Util.
Require Import InUtil.
Require Import PairInUtil.
Require Import MultiHist.
Require Import Tictac.

Require Import Var.
Require Import Tid.
Require Import Pure.NExp.
Require Import Pure.BExp.
Require Import Pure.RExp.
Require Import Pure.AExp.
Require Import AVal.

Require ULang.

Import ListNotations.

Section Defs.

  Inductive inst :=
  | Skip
  | Seq: inst -> inst -> inst
  | If: bexp -> inst -> inst -> inst
  | MemAcc: access_exp -> inst
  | Decl : var -> range -> inst -> inst
  | Fork : inst -> inst -> inst
  .

  Fixpoint i_subst x v i :=
    match i with
    | Skip => Skip
    | MemAcc e => MemAcc (a_subst x v e)
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | If b i j => If (b_subst x v b) (i_subst x v i) (i_subst x v j)
    | Decl y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      Decl y (r_subst x v r) i'
    | Fork i j => Fork (i_subst x v i) (i_subst x v j)
    end
  .


  Notation history := (list access_val).

  Inductive Run: inst -> list history -> Prop :=
  | run_skip:
    Run Skip [[]]
  | run_seq:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Seq i j) (prod hs1 hs2)
  | run_if:
    forall e b i j hsi hsj,
    BStep e b ->
    Run i hsi ->
    Run j hsj ->
    Run (If e i j) (if b then hsi else hsj)
  | run_access:
    forall e v,
    AStep e v ->
    Run (MemAcc e) [[v]]
  | run_fork:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Fork i j) (hs1 ++ hs2)
  | run_decl_cons:
    forall r n r' i x hs1 hs2,
    RStep r n r' ->
    Run (i_subst x (NNum n) i) hs1 ->
    Run (Decl x r' i) hs2 ->
    Run (Decl x r i) (hs1 ++ hs2)
  | run_decl_nil:
    forall x i r,
    REmpty r ->
    Run (Decl x r i) [[]]
  .


  (* Non-deterministic run *)
  Inductive NRun: inst -> history -> Prop :=
  | n_run_skip:
    NRun Skip []
  | n_run_seq:
    forall i j h1 h2,
    NRun i h1 ->
    NRun j h2 ->
    NRun (Seq i j) (h1 ++ h2)
  | n_run_if:
    forall e b i j hi hj,
    BStep e b ->
    NRun i hi ->
    NRun j hj ->
    NRun (If e i j) (if b then hi else hj)
  | n_run_access:
    forall e v,
    AStep e v ->
    NRun (MemAcc e) [v]
  | n_run_fork_l:
    forall i j h1 h2,
    NRun i h1 ->
    NRun j h2 ->
    NRun (Fork i j) h1
  | n_run_fork_r:
    forall i j h1 h2,
    NRun i h1 ->
    NRun j h2 ->
    NRun (Fork i j) h2
  | n_run_decl_cons:
    forall r n i x h,
    RPick r n ->
    NRun (i_subst x (NNum n) i) h ->
    NRun (Decl x r i) h
  | n_run_decl_nil:
    forall r i x,
    REmpty r ->
    NRun (Decl x r i) []
  .

  Lemma n_run_if_true:
    forall e i j hi hj,
    BStep e true ->
    NRun i hi ->
    NRun j hj ->
    NRun (If e i j) hi.
  Proof.
    intros.
    eapply n_run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma n_run_if_false:
    forall e i j hi hj,
    BStep e false ->
    NRun i hi ->
    NRun j hj ->
    NRun (If e i j) hj.
  Proof.
    intros.
    eapply n_run_if with (i:=i) (j:=j) in H0; eauto.
    assumption.
  Qed.

  Lemma run_if_true:
    forall e i j hi hj,
    BStep e true ->
    Run i hi ->
    Run j hj ->
    Run (If e i j) hi.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma run_if_false:
    forall e i j hi hj,
    BStep e false ->
    Run i hi ->
    Run j hj ->
    Run (If e i j) hj.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma run_inv_nil:
    forall i,
    ~ Run i [].
  Proof.
    intros i H.
    remember ([]).
    generalize dependent Heql.
    induction H; intros.
    - inversion Heql.
    - apply prod_inv_nil in Heql.
      destruct Heql; auto.
    - destruct b; auto.
    - inversion Heql.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
    - inversion Heql.
  Qed.

  Lemma run_not_nil:
    forall i m,
    Run i m ->
    m <> [].
  Proof.
    intros.
    intros N.
    subst.
    apply run_inv_nil in H.
    assumption.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_eq; auto.
    - rewrite a_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi; auto.
      rewrite r_subst_subst_eq.
      reflexivity.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_neq; auto.
    - rewrite a_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite r_subst_subst_neq; auto.
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_subst_neq_2:
    forall x y z n i,
    y <> z ->
    x <> z ->
    i_subst x (NVar y) (i_subst z (NNum n) i)
    =
    i_subst z (NNum n) (i_subst x (NVar y) i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_neq_2; auto.
    - rewrite a_subst_subst_neq_2; auto.
    - destruct (Set_VAR.MF.eq_dec z v). {
        subst.
        rewrite r_subst_subst_neq_2; auto.
      }
      rewrite r_subst_subst_neq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_subst_neq_3:
    forall c x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    i_subst x v1 (i_subst y v2 c)
    =
    i_subst y v2 (i_subst x v1 c).
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite b_subst_subst_neq_3; auto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite a_subst_subst_neq_3; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq_3; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq_3; auto.
      }
      rewrite r_subst_subst_neq_3; auto.
      rewrite IHc;auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
  Qed.

  (* ------------------------------- In ----------------------------- *)

  Fixpoint Occurs x (i:inst) : Prop :=
    match i with
    | MemAcc e => AFree x e
    | Skip => False
    | Seq i j => Occurs x i \/ Occurs x j
    | If b i j => BFree x b \/ Occurs x i \/ Occurs x j
    | Decl y r i => x = y \/ RFree x r \/ Occurs x i 
    | Fork i j => Occurs x i \/ Occurs x j
    end.

  Lemma i_subst_not_occurs:
    forall i x v,
    ~ Occurs x i ->
    i_subst x v i = i.
  Proof.
    induction i; intros; simpl in *.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_not_free; auto.
    - rewrite a_subst_not_free; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        intuition.
      }
      rewrite r_subst_not_free; auto.
      rewrite IHi; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma i_subst_subst_trans:
    forall i x y v,
    ~ Occurs x i ->
    i_subst x v (i_subst y (NVar x) i) =
    i_subst y v i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_trans; auto.
    - rewrite a_subst_subst_trans; auto.
    - rewrite r_subst_subst_trans; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        intuition.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite i_subst_not_occurs; auto.
      }
      rewrite IHi; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma i_occurs_subst_neq:
    forall i x y v,
    Occurs x (i_subst y v i) ->
    x <> y ->
    ~ NFree x v ->
    Occurs x i.
  Proof.
    induction i;
      simpl;
      intros.
    - assumption.
    - destruct H; eauto.
    - destruct H as [H|[H|H]]; eauto using b_free_subst_neq.
    - eauto using a_free_subst_neq.
    - destruct H as [H|[H|H]]; auto.
      + eauto using r_free_subst_neq.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto.
        }
        eauto.
    - destruct H; eauto.
  Qed.

  Lemma i_occurs_inv_subst:
    forall e x y z,
    x <> y ->
    x <> z ->
    Occurs x (i_subst z (NVar y) e) ->
    Occurs x e.
  Proof.
    intros.
    apply i_occurs_subst_neq in H1; auto.
  Qed.

  Lemma i_occurs_inv_subst_neq_num:
    forall y x n i,
    Occurs y (i_subst x (NNum n) i) ->
    Occurs y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - destruct H; auto.
    - destruct H as [H|[H|H]]; auto.
      left.
      eapply b_free_subst_neq; eauto.
    - eauto using a_free_subst_neq.
    - destruct H as [H|[H|H]]; auto.
      + eauto using r_free_subst_neq.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
    - destruct H; auto.
  Qed.

  (* --------------------------------- VAR ------------------------- *)

  Fixpoint Var x i :=
    match i with
    | Skip | MemAcc _=> False
    | If _ i j | Seq i j | Fork i j => Var x i \/ Var x j
    | Decl y _ i => x = y \/ Var x i
    end.

  Lemma var_not_in_fork:
    forall x i j,
    ~ Var x (Fork i j) ->
    ~ Var x i /\ ~ Var x j.
  Proof.
    intros.
    split;
    intros N;
    contradict H;
    simpl; auto.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros;
    destruct H; auto;
    destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (* -------------------------------- InRange -------------------------- *)

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j | Fork i j => InRange x i \/ InRange x j
  | Decl _ r i => RFree x r \/ InRange x i
  end.

  Lemma in_range_inv_subst_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; simpl; try destruct H; auto.
    - apply r_free_subst_neq in H; auto.
    - destruct (Set_VAR.MF.eq_dec x v);
      auto.
  Qed.

  (* --------------------- PAIR-IN INSTRUCTION ---------------------- *)

  Inductive IIn (a:access_val) : inst -> Prop :=
  | i_in_access:
    forall e,
    AStep e a ->
    IIn a (MemAcc e)
  | i_in_seq_l:
    forall i j,
    IIn a i ->
    IIn a (Seq i j)
  | i_in_seq_r:
    forall i j,
    IIn a j ->
    IIn a (Seq i j)
  | i_in_if_true:
    forall b i j,
    BStep b true ->
    IIn a i ->
    IIn a (If b i j)
  | i_in_if_false:
    forall b i j,
    BStep b false ->
    IIn a j ->
    IIn a (If b i j)
  | i_in_fork_l:
    forall i j,
    IIn a i ->
    IIn a (Fork i j)
  | i_in_fork_r:
    forall i j,
    IIn a j ->
    IIn a (Fork i j)
  | i_in_decl:
    forall r n x i,
    RPick r n ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (Decl x r i)
  .

  Lemma i_in_decl_r_step:
    forall r n r',
    RStep r n r' ->
    forall a x i,
    IIn a (Decl x r' i) ->
    IIn a (Decl x r i).
  Proof.
    intros.
    invc H0.
    apply i_in_decl with (n:=n0); eauto using r_step_pick_rev.
  Qed.

  Lemma run_m_in_to_i_in:
    forall i h,
    Run i h ->
    forall a,
    MIn a h ->
    IIn a i.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi.
    - apply m_in_nil_nil in Hi.
      contradiction.
    - apply m_in_prod_inv in Hi.
      destruct Hi; auto using i_in_seq_l, i_in_seq_r.
    - destruct b. {
        eauto using i_in_if_true.
      }
      eauto using i_in_if_false.
    - apply m_in_inv_cons_nil in Hi.
      simpl in *.
      intuition.
      subst.
      eapply i_in_access; eauto.
    - apply m_in_inv_app in Hi.
      destruct Hi; auto using i_in_fork_l, i_in_fork_r.
    - apply m_in_inv_app in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_in_decl; eauto using r_step_to_pick.
      }
      eauto using i_in_decl_r_step.
    - apply m_in_nil_nil in Hi.
      contradiction.
  Qed.

  Lemma n_run_in_to_i_in:
    forall i h,
    NRun i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - rewrite in_app_iff in Hi.
      destruct Hi as [Hi|Hi]; eauto using i_in_seq_l, i_in_seq_r.
    - destruct b; eauto using i_in_if_true, i_in_if_false.
    - constructor.
      simpl in *.
      intuition; subst.
      assumption.
    - auto using i_in_fork_l.
    - auto using i_in_fork_r.
    - apply i_in_decl with (n:=n); eauto.
    - contradiction.
  Qed.

  Lemma run_i_in_to_m_in:
    forall i h,
    Run i h ->
    forall a,
    IIn a i ->
    MIn a h.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi; invc Hi.
    - apply m_in_prod_l; eauto using run_not_nil.
    - apply m_in_prod_r; eauto using run_not_nil.
    - assert (b = true) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (a = v) by eauto using a_step_fun.
      subst.
      auto using in_eq, m_in_eq.
    - auto using m_in_app_l.
    - auto using m_in_app_r.
    - rename_hyp (RPick _ _) as hr.
      apply r_step_pick_advance with (n:=n) (r':=r') in hr; auto.
      destruct hr. {
        subst.
        eauto using m_in_app_l.
      }
      eauto using i_in_decl, m_in_app_r.
    - contradict H.
      eauto using r_pick_to_empty.
  Qed.

  Inductive CanRun : inst -> Prop :=
  | can_run_skip:
    CanRun Skip
  | can_run_seq:
    forall i j,
    CanRun i ->
    CanRun j ->
    CanRun (Seq i j)
  | can_run_if:
    forall e b i j,
    BStep e b ->
    CanRun i ->
    CanRun j ->
    CanRun (If e i j)
  | can_run_acc:
    forall e v,
    AStep e v ->
    CanRun (MemAcc e)
  | can_run_fork:
    forall i j,
    CanRun i ->
    CanRun j ->
    CanRun (Fork i j)
  | can_run_decl:
    forall x r i,
    RDefined r ->
    (forall n, RPick r n -> CanRun (i_subst x (NNum n) i)) ->
    CanRun (Decl x r i).

  Lemma can_run_to_n_run {i}:
    CanRun i ->
    exists h, NRun i h.
  Proof.
    intros.
    induction H.
    - exists [].
      constructor.
    - destruct IHCanRun1 as (h1, hr1).
      destruct IHCanRun2 as (h2, hr2).
      eexists.
      constructor; eauto.
    - destruct IHCanRun1 as (h1, hr1).
      destruct IHCanRun2 as (h2, hr2).
      eexists.
      constructor; eauto.
    - eexists.
      constructor; eauto.
    - destruct IHCanRun1 as (h1, hr1).
      destruct IHCanRun2 as (h2, hr2).
      eexists.
      eapply n_run_fork_r; eauto.
    - apply r_defined_inv in H.
      destruct H. {
        exists [].
        constructor.
        assumption.
      }
      destruct H as (n, Hf).
      apply r_first_to_pick in Hf.
      destruct H1 with (n:=n) as (h, Hr); auto.
      eexists.
      econstructor; eauto.
  Qed.

  Lemma n_run_i_in_to_in:
    forall i,
    CanRun i ->
    forall a,
    IIn a i ->
    exists h, NRun i h /\ In a h.
  Proof.
    intros i H.
    induction H.
    all: intros a Hi.
    all: invc Hi.
    - destruct (IHCanRun1 a) as (h1, (hr, hi)); auto.
      destruct (can_run_to_n_run H0) as (h2, hr2).
      exists (h1++h2).
      split. {
        constructor; auto.
      }
      rewrite in_app_iff.
      intuition.
    - destruct (IHCanRun2 a) as (h2, (hr, hj)); auto.
      destruct (can_run_to_n_run H) as (h1, hr2).
      exists (h1++h2).
      split. {
        constructor; auto.
      }
      rewrite in_app_iff.
      intuition.
    - destruct (IHCanRun1 a) as (h1, (hr, hi)); auto.
      destruct (can_run_to_n_run H1) as (h2, hr2).
      exists h1.
      split; auto.
      eapply n_run_if_true; eauto.
    - destruct (IHCanRun2 a) as (h2, (hr, hj)); auto.
      destruct (can_run_to_n_run H0) as (h1, hri).
      exists h2.
      split; auto.
      eapply n_run_if_false; eauto.
    - exists [a].
      split; auto using n_run_access, in_eq.
    - destruct (IHCanRun1 a) as (h1, (hr, hi)); auto.
      destruct (can_run_to_n_run H0) as (h2, hr2).
      exists h1.
      split; auto.
      eapply n_run_fork_l; eauto.
    - destruct (IHCanRun2 a) as (h2, (hr, hj)); auto.
      destruct (can_run_to_n_run H) as (h1, hri).
      exists h2.
      split; auto.
      eapply n_run_fork_r; eauto.
    - assert (Hx: exists h, NRun (i_subst x (NNum n) i) h /\ In a h) by eauto.
      destruct Hx as (h, (Hn, Hi)).
      exists h.
      split; auto.
      apply n_run_decl_cons with (n:=n); auto.
  Qed.

  Lemma i_in_iff:
    forall i h,
    Run i h ->
    forall a,
    IIn a i <-> MIn a h.
  Proof.
    intros.
    split; eauto using run_m_in_to_i_in, run_i_in_to_m_in.
  Qed.

  (* ------------------------ PAIR IN ------------------------------------- *)

  Definition IOneOf (p:access_val*access_val) i j :=
    let (v1, v2) := p in
    (IIn v1 i /\ IIn v2 j)
    \/
    (IIn v2 i /\ IIn v1 j).

  Inductive IPairIn p : inst -> Prop :=
  | i_pair_in_seq_l i j:
    IPairIn p i ->
    IPairIn p (Seq i j)
  | i_pair_in_seq_r i j:
    IPairIn p j ->
    IPairIn p (Seq i j)
  | i_pair_in_seq_both i j:
    IOneOf p i j ->
    IPairIn p (Seq i j)
  | i_pair_in_if_true b i j:
    BStep b true ->
    IPairIn p i ->
    IPairIn p (If b i j)
  | i_pair_in_if_false b i j:
    BStep b false ->
    IPairIn p j ->
    IPairIn p (If b i j)
  | i_pair_in_fork_l i j:
    IPairIn p i ->
    IPairIn p (Fork i j)
  | i_pair_in_fork_r i j:
    IPairIn p j ->
    IPairIn p (Fork i j)
  | i_pair_in_decl:
    forall n r i x,
    RPick r n ->
    IPairIn p (i_subst x (NNum n) i) ->
    IPairIn p (Decl x r i).

  Lemma i_one_of_sym:
    forall x y i j,
    IOneOf (x, y) i j ->
    IOneOf (y, x) i j.
  Proof.
    intros.
    unfold IOneOf in *.
    intuition.
  Qed.

  Lemma i_pair_in_sym:
    forall x y i,
    IPairIn (x, y) i ->
    IPairIn (y, x) i.
  Proof.
    intros.
    remember (x, y) as p.
    generalize dependent x.
    generalize dependent y.
    induction H; intros a1 a2 heq; subst.
    - eauto using i_pair_in_seq_l.
    - eauto using i_pair_in_seq_r.
    - eauto using i_pair_in_seq_both, i_one_of_sym.
    - eauto using i_pair_in_if_true.
    - eauto using i_pair_in_if_false.
    - eauto using i_pair_in_fork_l.
    - eauto using i_pair_in_fork_r.
    - eapply i_pair_in_decl; eauto.
  Qed.

  Lemma run_i_pair_in_to_m_pair_in:
    forall i h,
    Run i h ->
    forall p,
    IPairIn p i ->
    MPairIn p h.
  Proof.
    intros i h Hr.
    induction Hr; intros p Hi;
      inversion Hi; subst; clear Hi.
    - eauto using m_pair_in_prod_l, run_not_nil.
    - eauto using m_pair_in_prod_r, run_not_nil.
    - destruct p as (v1, v2).
      destruct H0 as [(Ha,Hb)|(Ha,Hb)];
        eapply run_i_in_to_m_in in Ha; eauto;
        eapply run_i_in_to_m_in in Hb;
        eauto using m_pair_in_prod_2, m_pair_in_prod_1.
    - assert (b = true) by eauto using b_step_fun; subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun; subst; eauto.
    - auto using m_pair_in_app_l.
    - auto using m_pair_in_app_r.
    - rename_hyp (RPick _ _) as hr.
      apply r_step_pick_advance with (n:=n) (r':=r') in hr; auto.
      destruct hr. {
        subst.
        apply m_pair_in_app_l.
        eauto.
      }
      eapply m_pair_in_app_r.
      eauto using i_pair_in_decl.
    - contradict H.
      eauto using r_pick_to_empty.
  Qed.


  Lemma run_m_pair_in_to_i_pair_in:
    forall i h,
    Run i h ->
    forall v1 v2,
    av_owner v1 <> av_owner v2 ->
    MPairIn (v1, v2) h ->
    IPairIn (v1, v2) i.
  Proof.
    intros i h Hr.
    induction Hr; intros v1 v2 hneq Hi.
    - apply m_pair_in_nil_nil in Hi.
      contradiction.
    - apply m_pair_in_inv_prod in Hi.
      destruct Hi as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]];
        auto using i_pair_in_seq_l, i_pair_in_seq_r;
        apply i_pair_in_seq_both;
        simpl in *;
        eapply run_m_in_to_i_in in Ha; eauto;
        eapply run_m_in_to_i_in in Hb; eauto.
    - destruct b. {
        apply i_pair_in_if_true; auto.
      }
      apply i_pair_in_if_false; auto.
    - (* Impossible case since only one access exists *)
      apply m_pair_in_inv in Hi.
      destruct Hi. {
        assert (v1 = v2). {
          inversion_clear H0.
          simpl in *.
          intuition.
          subst.
          reflexivity.
        }
        subst.
        contradiction.
      }
      apply m_pair_in_nil in H0.
      contradiction.
    - apply m_pair_in_app_or in Hi.
      destruct Hi; auto using i_pair_in_fork_l, i_pair_in_fork_r.
    - apply m_pair_in_app_or in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_pair_in_decl; eauto using r_step_to_pick.
      }
      apply IHHr2 in Hi; auto.
      invc Hi.
      rename_hyp (RPick _ _) as hr.
      eauto using r_step_pick_rev, i_pair_in_decl.
    - apply m_pair_in_nil_nil in Hi.
      contradiction.
  Qed.

  Lemma i_pair_in_to_i_in:
    forall v1 v2 i,
    IPairIn (v1, v2) i ->
    IIn v1 i /\ IIn v2 i.
  Proof.
    intros v1 v2 i Hi.
    remember (v1, v2) as p.
    generalize dependent v1.
    generalize dependent v2.
    induction Hi; intros; subst.
    - edestruct IHHi; eauto.
      auto using i_in_seq_l.
    - edestruct IHHi; eauto.
      auto using i_in_seq_r.
    - destruct H as [(?,?)|(?,?)]; auto using i_in_seq_l, i_in_seq_r.
    - edestruct IHHi; eauto.
      auto using i_in_if_true.
    - edestruct IHHi; eauto.
      auto using i_in_if_false.
    - edestruct IHHi; eauto.
      auto using i_in_fork_l.
    - edestruct IHHi; eauto.
      auto using i_in_fork_r.
    - edestruct IHHi; eauto.
      eauto using i_in_decl.
  Qed.

  Lemma n_run_pair_in_to_i_pair_in:
    forall i h,
    NRun i h ->
    forall v1 v2,
    av_owner v1 <> av_owner v2 ->
    PairIn (v1, v2) h ->
    IPairIn (v1, v2) i.
  Proof.
    intros i h Hr.
    induction Hr; intros v1 v2 hneq Hi.
    - apply pair_not_in_nil in Hi.
      contradiction.
    - apply pair_in_inv_app in Hi.
      intuition.
      + apply i_pair_in_seq_l.
        auto.
      + apply i_pair_in_seq_r.
        auto.
      + apply i_pair_in_seq_both.
        simpl in *.
        eauto using n_run_in_to_i_in.
      + apply i_pair_in_seq_both.
        simpl in *.
        eauto using n_run_in_to_i_in.
    - destruct b. {
        apply i_pair_in_if_true; auto.
      }
      apply i_pair_in_if_false; auto.
    - invc Hi.
      simpl in *.
      intuition.
      subst.
      contradiction.
    - apply i_pair_in_fork_l.
      auto.
    - apply i_pair_in_fork_r.
      auto.
    - eapply i_pair_in_decl; eauto.
    - apply pair_not_in_nil in Hi.
      contradiction.
  Qed.

  Lemma n_run_i_pair_in_to_m_pair_in:
    forall i,
    CanRun i ->
    forall p,
    IPairIn p i ->
    exists h, NRun i h /\ PairIn p h.
  Proof.
    intros i H.
    induction H.
    all: intros p hi.
    all: invc hi.
    all: try rename_hyp (IPairIn _ _) as hi.
    - apply IHCanRun1 in hi.
      destruct hi as (h1, (hr1, hi)); auto.
      destruct (can_run_to_n_run H0) as (h2, hr2).
      exists (h1 ++ h2).
      split; auto using pair_in_app_l.
      constructor; auto.
    - apply IHCanRun2 in hi.
      destruct hi as (h2, (hr1, hi)); auto.
      destruct (can_run_to_n_run H) as (h1, hr2).
      exists (h1 ++ h2).
      split; auto using pair_in_app_r.
      constructor; auto.
    - destruct p as (v1, v2).
      simpl in *.
      intuition.
      all: rename_hyp (IIn _ i) as hi.
      all: rename_hyp (IIn _ j) as hj.
      all: apply n_run_i_in_to_in in hi; auto.
      all: apply n_run_i_in_to_in in hj; auto.
      all: destruct hi as (h1, (hr1, hi)).
      all: destruct hj as (h2, (hr2, hj)).
      all: exists (h1 ++ h2).
      all: split.
      all: auto using n_run_seq.
      all: constructor.
      all: rewrite in_app_iff.
      all: intuition.
    - apply IHCanRun1 in hi.
      destruct hi as (h, (Hr1, hp)).
      exists h.
      split; auto.
      destruct (can_run_to_n_run H1) as (h2, hr2).
      eapply n_run_if_true; eauto.
    - apply IHCanRun2 in hi.
      destruct hi as (h, (Hr1, hp)).
      exists h.
      split; auto.
      destruct (can_run_to_n_run H0) as (h2, hr2).
      eapply n_run_if_false; eauto.
    - apply IHCanRun1 in hi.
      destruct hi as (h, (Hr1, hp)).
      exists h.
      split; auto.
      destruct (can_run_to_n_run H0) as (h2, hr2).
      eapply n_run_fork_l; eauto.
    - apply IHCanRun2 in hi.
      destruct hi as (h, (Hr1, hp)).
      exists h.
      split; auto.
      destruct (can_run_to_n_run H) as (h2, hr2).
      eapply n_run_fork_r; eauto.
    - apply H1 in hi; eauto.
      destruct hi as (h, (Hr1, hp)).
      exists h.
      split; auto.
      eapply n_run_decl_cons; eauto.
  Qed.
End Defs.
