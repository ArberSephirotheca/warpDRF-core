Require Import Coq.Lists.List.

Require Import Coq.micromega.Lia.

Require Import Util.
Require Import InUtil.
Require Import PairInUtil.
Require Import MultiHist.
Require Import Tictac.

Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AExp.
Require Import RExp.

Require ULang.

Import ListNotations.

Section Defs.
  Context {A:Access}.

  Inductive inst :=
  | Skip
  | Seq: inst -> inst -> inst
  | If: bexp -> inst -> inst -> inst
  | MemAcc: access_exp -> nexp -> inst
  | Decl : var -> range -> inst -> inst
  | Fork : inst -> inst -> inst
  .

  Fixpoint i_subst x v i :=
    match i with
    | Skip => Skip
    | MemAcc e n => MemAcc (access_subst x v e) (n_subst x v n)
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
    forall e v n,
    access_step (e, n) v ->
    Run (MemAcc e n) [v]
  | run_fork:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Fork i j) (hs1 ++ hs2)
  | run_decl_cons:
    forall e1 e2 n1 n2 i x hs1 hs2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) hs1 ->
    Run (Decl x (NNum (S n1), NNum n2) i) hs2 ->
    Run (Decl x (e1, e2) i) (hs1 ++ hs2)
  | run_decl_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run (Decl x (e1, e2) i) [[]]
  .

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
    - rewrite access_subst_subst_eq; auto.
      rewrite n_subst_subst_eq; auto.
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
    - rewrite access_subst_subst_neq; auto.
      rewrite n_subst_subst_neq; auto.
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
    - rewrite access_subst_subst_neq_2; auto.
      rewrite n_subst_subst_neq_2; auto.
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
    - rewrite access_subst_subst_neq_3; auto.
      rewrite n_subst_subst_neq_3; auto.
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
    | MemAcc e n => AFree x e \/ NFree x n
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
    - rewrite access_subst_not_free; auto.
      rewrite n_subst_not_free; auto.
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
    - rewrite access_subst_subst_trans; auto.
      rewrite n_subst_subst_trans; auto.
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
    - destruct H as [H|H]; eauto using access_in_subst_neq, n_free_subst_neq.
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
    - destruct H; eauto using access_in_subst_neq, n_free_subst_neq.
    - destruct H as [H|[H|H]]; auto.
      + eauto using r_free_subst_neq.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
    - destruct H; auto.
  Qed.

  (* --------------------------------- VAR ------------------------- *)

  Fixpoint Var x i :=
    match i with
    | Skip | MemAcc _ _=> False
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
  | Skip | MemAcc _ _ => False
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
    forall e n v,
    access_step (e, n) v ->
    List.In a v ->
    IIn a (MemAcc e n)
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
    forall e1 e2 n1 n n2 x i,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (Decl x (e1, e2) i)
  .

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
      eapply i_in_access; eauto.
    - apply m_in_inv_app in Hi.
      destruct Hi; auto using i_in_fork_l, i_in_fork_r.
    - apply m_in_inv_app in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_in_decl; eauto.
      }
      apply IHHr2 in Hi.
      inversion Hi; subst; clear Hi.
      assert (S n1 = n0) by eauto using n_step_fun, n_step_num.
      assert (n3 = n2) by eauto using n_step_fun, n_step_num.
      subst.
      eapply i_in_decl with (n:=n); eauto.
      auto with *.
    - apply m_in_nil_nil in Hi.
      contradiction.
  Qed.

  Lemma run_i_in_to_m_in:
    forall i h,
    Run i h ->
    forall a,
    IIn a i ->
    MIn a h.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi; inversion Hi; subst; clear Hi.
    - apply m_in_prod_l; eauto using run_not_nil.
    - apply m_in_prod_r; eauto using run_not_nil.
    - assert (b = true) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (v0 = v) by eauto using access_step_fun.
      subst.
      auto using m_in_eq.
    - auto using m_in_app_l.
    - auto using m_in_app_r.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. apply m_in_app_l. eauto. }
      apply m_in_app_r.
      apply IHHr2.
      eapply i_in_decl with (n1:=S n1) (n2:=n2); eauto using n_step_num.
      auto with *.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n2 = n3) by eauto using n_step_fun.
      subst.
      lia.
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

  (* --------------------------- SUBST IN --------------------------------- *)
  Section Props.
  Import Tasks.
  Context `{T:Tasks}.
  Inductive SIn (a:access_val) (n:nat) : inst -> Prop :=
  | s_in_access:
    forall e1 e2 v,
    access_step (access_subst TID (NNum n) e1, n_subst TID (NNum n) e2) v ->
    List.In a v ->
    SIn a n (MemAcc e1 e2)
  | s_in_seq_l:
    forall i j,
    SIn a n i ->
    SIn a n (Seq i j)
  | s_in_seq_r:
    forall i j,
    SIn a n j ->
    SIn a n (Seq i j)
  | s_in_if_true:
    forall b i j,
    BData n b true ->
    SIn a n i ->
    SIn a n (If b i j)
  | s_in_if_false:
    forall b i j,
    BData n b false ->
    SIn a n j ->
    SIn a n (If b i j)
  | s_in_fork_l:
    forall i j,
    SIn a n i ->
    SIn a n (Fork i j)
  | s_in_fork_r:
    forall i j,
    SIn a n j ->
    SIn a n (Fork i j)
  | s_in_decl:
    forall e1 e2 n1 n' n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 <= n' < n2 ->
    SIn a n (i_subst x (NNum n') i) ->
    SIn a n (Decl x (e1, e2) i)
  .

  Lemma i_in_to_s_in:
    forall i,
    ~ Var TID i ->
    forall a n,
    IIn a (i_subst TID (NNum n) i) ->
    SIn a n i.
  Proof.
    intros i Hv a n Hi.
    remember (i_subst _ _ _) as j.
    generalize dependent i.
    generalize dependent n.
    induction Hi; intros n' i' Hv Heq.
    - destruct i'; inversion Heq; subst; clear Heq.
      eapply s_in_access; eauto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_seq_l; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_seq_r; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_if_true; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_if_false; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_fork_l; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_fork_r; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      assert (TID <> v) by auto.
      remove_eq TID v.
      destruct r as (r1, r2).
      inversion H4; subst; clear H4.
      eapply s_in_decl; eauto.
      apply IHHi.
      + intros N.
        apply var_subst_inv_1 in N.
        auto.
      + rewrite i_subst_subst_neq; auto.
  Qed.

  Lemma s_in_to_i_in:
    forall i,
    ~ Var TID i ->
    forall a n,
    SIn a n i ->
    IIn a (i_subst TID (NNum n) i).
  Proof.
    intros i Hv a n Hi.
    generalize dependent Hv.
    induction Hi; intros Hv; simpl in Hv.
    - eapply i_in_access; eauto.
    - apply i_in_seq_l; auto.
    - apply i_in_seq_r; auto.
    - apply i_in_if_true; auto.
    - apply i_in_if_false; auto.
    - apply i_in_fork_l; auto.
    - apply i_in_fork_r; auto.
    - simpl.
      assert (TID <> x) by auto.
      remove_eq TID x.
      eapply i_in_decl; eauto.
      rewrite i_subst_subst_neq; auto.
      apply IHHi.
      intros N.
      apply var_subst_inv_1 in N.
      auto.
  Qed.
  End Props.

  (* ------------------------ PAIR IN ------------------------------------- *)

  Definition IOneOf (p:access_val*access_val) i j :=
    let (v1, v2) := p in
    (IIn v1 i /\ IIn v2 j)
    \/
    (IIn v2 i /\ IIn v1 j).

  Inductive IPairIn p : inst -> Prop :=
  | i_pair_in_access e n v:
    access_step (e, n) v ->
    PairIn p v ->
    IPairIn p (MemAcc e n)
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
    forall n e1 e2 n1 n2 i x,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IPairIn p (i_subst x (NNum n) i) ->
    IPairIn p (Decl x (e1, e2) i).

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
    - eapply i_pair_in_access; eauto using pair_in_sym.
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
    - assert (v0 = v) by eauto using access_step_fun; subst.
      auto using m_pair_in_eq.
    - auto using m_pair_in_app_l.
    - auto using m_pair_in_app_r.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. apply m_pair_in_app_l. eauto. }
      apply m_pair_in_app_r.
      apply IHHr2.
      eapply i_pair_in_decl with (n1:=S n1) (n2:=n2); eauto using n_step_num.
      auto with *.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n2 = n3) by eauto using n_step_fun.
      subst.
      lia.
  Qed.

  Lemma run_m_pair_in_to_i_pair_in:
    forall i h,
    Run i h ->
    forall p,
    MPairIn p h ->
    IPairIn p i.
  Proof.
    intros i h Hr.
    induction Hr; intros p Hi.
    - apply m_pair_in_nil_nil in Hi.
      contradiction.
    - apply m_pair_in_inv_prod in Hi.
      destruct Hi as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]];
        auto using i_pair_in_seq_l, i_pair_in_seq_r;
        apply i_pair_in_seq_both;
        destruct p as (v1, v2);
        simpl in *;
        eapply run_m_in_to_i_in in Ha; eauto;
        eapply run_m_in_to_i_in in Hb; eauto.
    - destruct b. {
        apply i_pair_in_if_true; auto.
      }
      apply i_pair_in_if_false; auto.
    - apply m_pair_in_inv in Hi.
      destruct Hi. {
        eauto using i_pair_in_access.
      }
      apply m_pair_in_nil in H0.
      contradiction.
    - apply m_pair_in_app_or in Hi.
      destruct Hi; auto using i_pair_in_fork_l, i_pair_in_fork_r.
    - apply m_pair_in_app_or in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_pair_in_decl; eauto.
      }
      apply IHHr2 in Hi.
      inversion Hi; subst; clear Hi.
      assert (S n1 = n0) by eauto using n_step_fun, n_step_num.
      assert (n3 = n2) by eauto using n_step_fun, n_step_num.
      subst.
      eapply i_pair_in_decl with (n:=n); eauto.
      auto with *.
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
    - inversion H0; subst; clear H0.
      eauto using i_in_access.
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

  Variable CurTask : nat.
  Fixpoint translate (i:ULang.inst) : inst :=
    match i with
    | ULang.Skip => Skip
    | ULang.Seq i j => Seq (translate i) (translate j)
    | ULang.If b i j => If b (translate i) (translate j)
    | ULang.MemAcc e => MemAcc e (NNum CurTask)
    | ULang.For x r i => Decl x r (translate i)
    end.

  Lemma i_subst_translate_rw:
    forall i x n,
    i_subst x n (translate i) =
    translate (ULang.i_subst x n i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
    - reflexivity.
    - rewrite IHi.
      destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma all_incl_eq:
    forall A v,
    @AllIncl A [v] v.
  Proof.
    intros.
    apply all_incl_cons.
    + apply incl_refl.
    + apply all_incl_nil.
  Qed.

End Defs.
