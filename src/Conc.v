Require Import Coq.Lists.List.

Require Import Coq.micromega.Lia.
Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import Tasks.
Require Import PairInUtil.
Require Hist.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip: inst
  | If: bexp -> inst -> inst -> inst
  | Seq: inst -> inst -> inst
  | MemAcc: access_exp -> inst
  | For : var -> range -> inst -> inst
  .

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | If b i j => If (b_subst x v b) (i_subst x v i) (i_subst x v j)
  | Seq i j => Seq (i_subst x v i) (i_subst x v j)
  | MemAcc a => MemAcc (access_subst x v a)  
  | For y r i =>
    let i' := if VAR.eq_dec x y then i else i_subst x v i in
    For y (r_subst x v r) i'
  end.

  Import Hist.

  Notation history := (list access_val).

  Fixpoint In (x:var) i :=
  match i with
  | Skip => False
  | MemAcc e => access_in x e
  | If b i j => BIn x b \/ In x i \/ In x j
  | Seq i j => In x i \/ In x j
  | For y r i => x = y \/ RIn x r \/ In x i
  end.

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => Var x i \/ Var x j
  | For y _ i (*| Loop y _ i*) => x = y \/ Var x i
  end.

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => InRange x i \/ InRange x j
  | For _ r i => RIn x r \/ InRange x i
  end.

  Infix ";;" := Seq (at level 50).

  Lemma i_subst_seq:
    forall x n i1 i2,
    i_subst x n (i1 ;; i2) = i_subst x n i1 ;; i_subst x n i2.
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma i_subst_inv_seq:
    forall x v k i j,
    i_subst x v k = Seq i j ->
    exists i' j',
    k = Seq i' j' /\
    i = i_subst x v i' /\
    j = i_subst x v j'.
  Proof.
    destruct k; simpl; intros i j H; inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_eq.
      reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi.
      rewrite r_subst_subst_eq.
      reflexivity.
  Qed.

  Lemma i_subst_subst_eq_2
     : forall (x : var) i (v e : nexp),
       ~ NIn x v -> i_subst x e (i_subst x v i) = i_subst x v i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite b_subst_subst_eq_2; auto.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto; rewrite IHi2; auto.
    - rewrite access_subst_subst_eq_2; auto.
    - rewrite r_subst_subst_eq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). { reflexivity. }
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_neq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_neq; auto.
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
      rewrite IHi; auto.
      rewrite r_subst_subst_neq; auto.
  Qed.

  Lemma i_subst_subst_neq_3:
    forall c x y v1 v2,
    x <> y ->
    ~ NIn y v1 ->
    ~ NIn x v2 ->
    i_subst x v1 (i_subst y v2 c)
    =
    i_subst y v2 (i_subst x v1 c).
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      rewrite b_subst_subst_neq_3; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite access_subst_subst_neq_3; auto.
    - rewrite r_subst_subst_neq_3; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          reflexivity.
        }
        reflexivity.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        reflexivity.
      }
      rewrite IHc; auto.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; destruct H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_r_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_subst_inv_1:
    forall y x n i,
    In y (i_subst x (NNum n) i) ->
    In y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_b_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct H; auto.
    - eapply access_in_subst_neq; eauto.
      intros N.
      inversion N.
    - destruct H; auto.
      + apply in_r_subst_neq in H; eauto.
        intros N.
        inversion N.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (** Parallelize an access for [n] tasks. *)

  Context `{T:Tasks}.
  Inductive Run (n:nat) : inst -> history -> Prop :=
  | run_skip:
    Run n Skip []
  | run_access:
    forall e v,
    access_step (e, NNum n) v ->
    Run n (MemAcc e) v
  | run_seq:
    forall i j h1 h2,
    Run n i h1 ->
    Run n j h2 ->
    Run n (Seq i j) (h1 ++ h2)
  | run_if:
    forall i j e b hi hj,
    BStep e b ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) (if b then hi else hj)
  
  | run_for_cons:
    forall e1 e2 n1 n2 i x h1 h2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run n (i_subst x (NNum n1) i) h1 ->
    Run n (For x (NNum (S n1), NNum n2) i) h2 ->
    Run n (For x (e1, e2) i) (h1 ++ h2)
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run n (For x (e1, e2) i) []
  .

  Lemma run_if_true:
    forall e n i j hi hj,
    BStep e true ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) hi.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma run_if_false:
    forall e n i j hi hj,
    BStep e false ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) hj.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Definition REq i1 i2 :=
   forall n h,
   Run n i1 h <-> Run n i2 h.

  Inductive RunAll : nat -> inst -> history -> Prop :=
  | run_all_zero:
    forall i,
    RunAll 0 i []
  | run_all_succ:
    forall i n h1 h2,
    Run n (i_subst TID (NNum n) i) h1 ->
    RunAll n i h2 ->
    RunAll (S n) i (h1 ++ h2).

  Inductive IIn (a:access_val) : inst -> Prop :=
  | i_in_access:
    forall e,
    AIn a e ->
    IIn a (MemAcc e)
  | i_in_if_true:
    forall b i j,
    BData (access_tid a) b true ->
    IIn a i ->
    IIn a (If b i j)
  | i_in_if_false:
    forall b i j,
    BData (access_tid a) b false ->
    IIn a j ->
    IIn a (If b i j)
  | i_in_seq_l:
    forall i j,
    IIn a i ->
    IIn a (Seq i j)
  | i_in_seq_r:
    forall i j,
    IIn a j ->
    IIn a (Seq i j)
  | i_in_for:
    forall i r x n1 n n2,
    RData (access_tid a) r (n1, n2) ->
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (For x r i)
  .

  Lemma run_all_inv_in:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    exists m h',
    m < n /\ Run m (i_subst TID (NNum m )i) h' /\ incl h' h /\ List.In x h'.
  Proof.
    intros n i h H.
    induction H; intros. { contradiction. }
    apply in_app_or in H1.
    destruct H1.
    - exists n.
      exists h1.
      eauto using InUtil.incl_app_refl_l with *.
    - edestruct IHRunAll as (m, (h, (Hl, (Hr, (Hi,Hj))))); eauto.
      exists m.
      exists h.
      auto using incl_appr with *.
  Qed.

  Lemma run_inv_in_eq:
    forall n i h,
    Run n i h ->
    forall a,
    List.In a h ->
    access_tid a = n.
  Proof.
    intros n i h H.
    induction H; intros.
    - contradiction.
    - eauto using access_step_inv_in_eq.
    - apply List.in_app_iff in H1.
      destruct H1; auto.
    - destruct b; auto.
    - apply List.in_app_iff in H4.
      destruct H4; auto.
    - contradiction.
  Qed.

  Lemma run_all_inv_in_eq:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    access_tid x < n.
  Proof.
    intros.
    eapply run_all_inv_in in H0; eauto.
    destruct H0 as (m, (h', (?, (Hr, (Hi, Hj))))).
    eapply run_inv_in_eq in Hj; eauto.
    subst.
    assumption.
  Qed.

  Lemma run_all_inv_run:
    forall n i h,
    RunAll n i h ->
    forall m,
    m < n ->
    exists h',
    Run m (i_subst TID (NNum m )i) h' /\ incl h' h.
  Proof.
    intros n i h H.
    induction H; intros m Hl. { inversion Hl. }
    inversion Hl; subst; clear Hl. {
      exists h1.
      split; auto.
      apply InUtil.incl_app_refl_l.
    }
    apply IHRunAll in H2.
    destruct H2 as (h', (Hr, Hi)).
    exists h'.
    split; auto.
    apply incl_tran with (m:= h2); auto.
    apply InUtil.incl_app_refl_r.
  Qed.

  Inductive SRun n: inst -> history -> Prop :=
  | s_run_skip:
    SRun n Skip []
  | s_run_access:
    forall e v,
    access_step (access_subst TID (NNum n) e, NNum n) v ->
    SRun n (MemAcc e) v
  | s_run_seq:
    forall i j h1 h2,
    SRun n i h1 ->
    SRun n j h2 ->
    SRun n (Seq i j) (h1 ++ h2)
  | s_run_if:
    forall e i j b hi hj,
    BData n e b ->
    SRun n i hi ->
    SRun n j hj ->
    SRun n (If e i j) (if b then hi else hj)
  | s_run_for_cons:
    forall e1 e2 n1 n2 x i h1 h2,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 < n2 ->
    SRun n (i_subst x (NNum n1) i) h1 ->
    SRun n (For x (NNum (S n1), NNum n2) i) h2 ->
    SRun n (For x (e1, e2) i) (h1 ++ h2) 
  | s_run_for_nil:
    forall e1 e2 n1 n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 >= n2 ->
    SRun n (For x (e1, e2) i) []
  .

  Lemma run_to_s_run:
    forall n i h,
    Run n (i_subst TID (NNum n) i) h ->
    ~ Var TID i ->
    SRun n i h.
  Proof.
    intros n i h Hr.
    remember (i_subst _ _ _) as j.
    generalize dependent i.
    induction Hr; simpl; intros; symmetry in Heqj.
    - destruct i; inversion Heqj.
      apply s_run_skip.
    - destruct i; inversion Heqj; subst; clear Heqj.
      auto using s_run_access.
    - apply i_subst_inv_seq in Heqj.
      destruct Heqj as (i', (j', (?, (?,?)))).
      subst.
      simpl in H.
      eapply s_run_seq; eauto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      simpl in *.
      apply s_run_if; auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (r1, r2).
      simpl in *.
      inversion H5; subst; clear H5.
      eapply s_run_for_cons.
      + eauto.
      + eauto.
      + assumption.
      + apply IHHr1; auto.
        * destruct (Set_VAR.MF.eq_dec TID x). {
            assert (TID <> x) by auto.
            contradiction.
          }
          rewrite i_subst_subst_neq; auto.
        * intros N.
          apply var_subst_inv_1 in N.
          auto.
      + auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (r1, r2).
      simpl in *.
      inversion H5; subst; clear H5.
      eapply s_run_for_nil; eauto.
  Qed.

  Lemma s_run_to_run:
    forall n i h,
    SRun n i h ->
    ~ Var TID i ->
    Run n (i_subst TID (NNum n) i) h.
  Proof.
    intros n i h H.
    induction H; simpl; intros.
    - apply run_skip.
    - auto using run_access.
    - apply run_seq; eauto.
    - apply run_if; auto.
    - assert (TID <> x) by auto.
      remove_eq TID x.
      eapply run_for_cons; eauto.
      + rewrite i_subst_subst_neq; auto.
        apply IHSRun1.
        intros N.
        apply var_subst_inv_1 in N.
        auto.
      + remove_eq TID x.
        apply IHSRun2.
        auto.
    - assert (TID <> x) by auto.
      remove_eq TID x.
      eapply run_for_nil; eauto.
  Qed.

  Lemma s_run_iff:
    forall i,
    ~ Var TID i ->
    forall n h,
    Run n (i_subst TID (NNum n) i) h <-> SRun n i h.
  Proof.
    split; intros; auto using s_run_to_run, run_to_s_run.
  Qed.

  Lemma s_run_access_tid:
    forall m i h,
    SRun m i h ->
    forall a,
    List.In a h ->
    access_tid a = m.
  Proof.
    intros m i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - eapply access_step_inv_in_eq in H; eauto.
    - apply in_app_iff in Hi.
      destruct Hi as [Hi|Hi]; auto.
    - destruct b; auto.
    - apply in_app_iff in Hi.
      destruct Hi; auto.
    - contradiction.
  Qed.

  Lemma run_access_tid:
    forall i,
    ~ Var TID i ->
    forall m h,
    Run m (i_subst TID (NNum m) i) h ->
    forall a,
    List.In a h ->
    access_tid a = m.
  Proof.
    intros i Hv m h Hr.
    apply s_run_iff in Hr; eauto using s_run_access_tid.
  Qed.

  Lemma s_run_i_in:
    forall m i h,
    SRun m i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros m i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - apply i_in_access.
      unfold AIn.
      exists v.
      erewrite access_step_inv_in_eq; eauto.
    - apply in_app_iff in Hi.
      destruct Hi; eauto using i_in_seq_l, i_in_seq_r.
    - destruct b.
      + apply i_in_if_true; auto.
        unfold BData in *.
        erewrite s_run_access_tid with (i:=i); eauto.
      + apply i_in_if_false; auto.
        unfold BData in *.
        erewrite s_run_access_tid with (i:=j); eauto.
    - apply in_app_iff in Hi.
      destruct Hi.
      + apply i_in_for with (n1:=n1) (n2:=n2) (n:=n1); auto.
        assert (R: access_tid a = m). { eauto using s_run_access_tid. }
        rewrite R.
        split; auto.
      + assert (Hi := H2).
        apply IHHr2 in H2.
        inversion H2; subst; clear H2.
        destruct H6 as (Ha, Hb).
        assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
        assert (n3 = n2) by eauto using n_step_fun, n_step_num.
        subst.
        apply i_in_for with (n1:=n1) (n:=n) (n2:=n2); auto with *.
        assert (R: access_tid a = m). { eauto using s_run_access_tid. }
        rewrite R.
        split; auto.
    - contradiction.
  Qed.

  Lemma run_all_to_i_in:
    forall i,
    ~ Var TID i ->
    forall n h,
    RunAll n i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros.
    eapply run_all_inv_in in H0; eauto.
    destruct H0 as (m, (h', (Hi, (Hm, (Hinc,Hj))))).
    apply run_to_s_run in Hm; auto.
    eauto using s_run_i_in.
  Qed.

  Lemma in_to_i_in:
    forall i,
    ~ Var TID i ->
    forall m h,
    Run m (i_subst TID (NNum m) i) h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros i Hv m h Hr.
    apply s_run_iff in Hr; eauto using s_run_i_in.
  Qed.

  Lemma s_run_i_in_to_in:
    forall m i h,
    SRun m i h ->
    forall a,
    access_tid a = m ->
    IIn a i ->
    List.In a h.
  Proof.
    intros m i h Hr.
    induction Hr; intros a He Hi; inversion Hi; subst; clear Hi.
    - unfold AIn in *.
      destruct H1 as (l', (Hs, Hi)).
      assert (l' = v) by eauto using access_step_fun.
      subst.
      assumption.
    - apply in_app_iff.
      auto.
    - apply in_app_iff.
      auto.
    - assert (b = true) by eauto using b_step_fun.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun.
      subst.
      eauto.
    - apply in_app_iff.
      destruct H5 as (Hn1, Hn2).
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. eauto. }
      apply i_in_for with (r:=(NNum (S n1), NNum n2)) (n1:=S n1) (n2:=n2) in H7; auto with *.
      split; apply n_step_num.
    - destruct H5 as (Hn1, Hn2).
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      lia.
  Qed.

  Lemma s_run_i_in_iff:
    forall m i h,
    SRun m i h ->
    forall a,
    access_tid a = m ->
    IIn a i <-> List.In a h.
  Proof.
    intros.
    split; eauto using s_run_i_in_to_in, s_run_i_in.
  Qed.

  Lemma run_all_i_in_to_in:
    forall i,
    ~ Var TID i ->
    forall n h,
    RunAll n i h ->
    forall a,
    access_tid a < n ->
    IIn a i ->
    List.In a h.
  Proof.
    intros i Hv n h Hr a Hlt Hi.
    eapply run_all_inv_run in Hr; eauto.
    destruct Hr as (h', (Hr, Hinc)).
    apply Hinc; clear Hinc.
    apply s_run_iff in Hr; auto.
    eapply s_run_i_in_to_in; eauto.
  Qed.

  Lemma run_all_inv_skip:
    forall n h,
    RunAll n Skip h ->
    h = [].
  Proof.
    induction n; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    apply IHn in H2.
    subst.
    simpl in *.
    inversion H1; subst; clear H1.
    reflexivity.
  Qed.

  (* --------------------------- ABSTRACT CONC -------------------------- *)

  Inductive CIn : access_val -> inst -> Prop :=
  | c_in_def:
    forall a c,
    access_tid a < TID_COUNT ->
    IIn a c ->
    CIn a c.

  Lemma c_in_1:
    forall c h a,
    ~ Var TID c ->
    RunAll TID_COUNT c h ->
    List.In a h ->
    CIn a c.
  Proof.
    intros c h a Hv Hr Hi.
      eauto using c_in_def, run_all_inv_in_eq, run_all_to_i_in.
  Qed.

  Lemma c_in_2:
    forall c h a,
    ~ Var TID c ->
    RunAll TID_COUNT c h ->
    CIn a c ->
    List.In a h.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eapply run_all_i_in_to_in; eauto.
  Qed.

  Lemma c_in_seq_l:
    forall a i j,
    CIn a i ->
    CIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using i_in_seq_l.
  Qed.

  Lemma c_in_seq_r:
    forall a i j,
    CIn a j ->
    CIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using i_in_seq_r.
  Qed.

  Lemma c_in_inv_seq:
    forall a i j,
    CIn a (Seq i j) ->
    CIn a i \/ CIn a j.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H1; subst; clear H1; auto using c_in_def.
  Qed.

  Inductive CPairIn : (access_val * access_val) -> inst -> Prop :=
  | c_pair_in_def:
    forall a1 a2 c,
    CIn a1 c ->
    CIn a2 c ->
    CPairIn (a1, a2) c.

  Lemma c_pair_in_1:
    forall c h p,
    ~ Var TID c ->
    RunAll TID_COUNT c h ->
    PairIn p h ->
    CPairIn p c.
  Proof.
    intros c h (a1, a2) Hv Hr Hi.
    inversion Hi; subst; clear Hi.
    eauto using c_pair_in_def, c_in_1.
  Qed.

  Lemma c_pair_in_seq_l:
    forall a i j,
    CPairIn a i ->
    CPairIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply c_pair_in_def; auto using c_in_seq_l.
  Qed.

  Lemma c_pair_in_seq_r:
    forall a i j,
    CPairIn a j ->
    CPairIn a (Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply c_pair_in_def; auto using c_in_seq_r.
  Qed.

  Lemma c_in_skip:
    forall a,
    ~ CIn a Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    inversion H0; subst; clear H0.
  Qed.

  Lemma c_in_seq_seq:
    forall a c1 c2 c3,
    CIn a (Seq (Seq c1 c2) c3) ->
    CIn a (Seq c1 (Seq c2 c3)).
  Proof.
    intros.
    apply c_in_inv_seq in H.
    destruct H as [H|H]. {
      apply c_in_inv_seq in H.
      destruct H; auto using c_in_seq_l, c_in_seq_r.
    }
    auto using c_in_seq_l, c_in_seq_r.
  Qed.

  Lemma c_pair_in_skip:
    forall p,
    ~ CPairIn p Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    apply c_in_skip in H.
    contradiction.
  Qed.

  Lemma r_step_inv_next_eq:
    forall r n r' n',
    RStep r n r' ->
    RFirst r' n' ->
    n' = S n.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n' = S n) by eauto using n_step_num, n_step_fun.
    auto.
  Qed.

  Lemma r_step_to_pick2:
    forall r n r',
    RStep r n r' ->
    RHasNext r' ->
    RPick2 r n.
  Proof.
    intros.
    destruct r as (e1, e2).
    inversion H; subst; clear H.
    destruct H0 as (n', Hx).
    inversion Hx; subst; clear Hx.
    assert (n' = S n) by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply r_pick2_def; eauto.
  Qed.

  Lemma r_one_to_pick:
    forall r n,
    ROne r n ->
    RPick r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_pick_def; eauto.
  Qed.

  Definition CEq c1 c2 :=
    forall a,
    CIn a c1 <-> CIn a c2.

End C1.
