Require Import Coq.Lists.List.

Require Import Coq.micromega.Lia.
Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import RExp.
Require Import AExp.
Require Import Util.
Require Import Tasks.
Require Import PairInUtil.
Require Import Tictac.

Require Hist.

Import NExpNotations.
Import RExpNotations.
Import ListNotations.

Open Scope exp_scope.

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

  Fixpoint Occurs (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => AFree x e
    | If b i j => BFree x b \/ Occurs x i \/ Occurs x j
    | Seq i j => Occurs x i \/ Occurs x j
    | For y r i => x = y \/ RFree x r \/ Occurs x i
    end.

  Fixpoint Free (x:var) c :=
    match c with
    | Skip => False
    | MemAcc e => AFree x e
    | If b i j => BFree x b \/ Free x i \/ Free x j
    | Seq i j => Free x i \/ Free x j
    | For y r i => RFree x r \/ (x <> y /\ Free x i)
    end.

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => Var x i \/ Var x j
  | For y _ i => x = y \/ Var x i
  end.

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => InRange x i \/ InRange x j
  | For _ r i => RFree x r \/ InRange x i
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
       ~ NFree x v -> i_subst x e (i_subst x v i) = i_subst x v i.
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

  Lemma var_inv_subst:
    forall y x e i,
    Var y (i_subst x e i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; intuition.
    destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma var_subst:
    forall i x y,
    x <> y ->
    Var y i ->
    forall e,
    Var y (i_subst x e i).
  Proof.
    induction i; simpl; auto; intros.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]; eauto.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]; eauto.
    - rename_hyp (_ \/ _) as Hp.
      destruct Hp as [Hp|Hp]. {
        subst.
        auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        auto.
      }
      auto.
  Qed.

  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply r_free_subst_neq in H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma occurs_inv_subst:
    forall y x v i,
    Occurs y (i_subst x v i) ->
    Occurs y i \/ NFree y v.
  Proof.
    induction i; simpl; intros; auto; intuition.
    - rename_hyp (BFree _ _) as hb.
      apply b_free_inv_subst in hb.
      intuition.
    - apply access_free_inv_subst in H.
      intuition.
    - apply r_free_inv_subst in H; intuition.
    - destruct (Set_VAR.MF.eq_dec x v0); auto.
      intuition.
  Qed.

  Lemma occurs_inv_subst_num:
    forall y x n i,
    Occurs y (i_subst x (NNum n) i) ->
    Occurs y i.
  Proof.
    intros.
    apply occurs_inv_subst in H.
    intuition.
    invc H0.
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

  Section S_IIn.
  Variable x:var.
  Variable v:nexp.

  Inductive S_IIn (a:access_val) : inst -> Prop :=
  | s_i_in_access:
    forall e,
    AIn a (access_subst x v e) ->
    S_IIn a (MemAcc e)
  | s_i_in_if_true:
    forall b i j,
    BData (access_tid a) (b_subst x v b) true ->
    S_IIn a i ->
    S_IIn a (If b i j)
  | s_i_in_if_false:
    forall b i j,
    BData (access_tid a) (b_subst x v b) false ->
    S_IIn a j ->
    S_IIn a (If b i j)
  | s_i_in_seq_l:
    forall i j,
    S_IIn a i ->
    S_IIn a (Seq i j)
  | s_i_in_seq_r:
    forall i j,
    S_IIn a j ->
    S_IIn a (Seq i j)
  | s_i_in_for_eq:
    forall i r n1 n n2,
    RData (access_tid a) (r_subst x v r) (n1, n2) ->
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    S_IIn a (For x r i)
  | s_i_in_for_neq:
    forall i r y n1 n n2,
    x <> y ->
    RData (access_tid a) (r_subst x v r) (n1, n2) ->
    n1 <= n < n2 ->
    S_IIn a (i_subst y (NNum n) i) ->
    S_IIn a (For y r i)
  .
  End S_IIn.

  Lemma s_i_in_to_i_in:
    forall x v a i,
    S_IIn x v a i ->
    forall n, NStep v n ->
    IIn a (i_subst x v i).
  Proof.
    intros x v a i H.
    induction H; simpl; intros.
    - constructor; auto.
    - constructor; eauto.
    - apply i_in_if_false; eauto.
    - constructor; eauto.
    - apply i_in_seq_r; eauto.
    - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      econstructor; eauto.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      econstructor; eauto.
      assert (~ NFree x (NNum n)) by auto using n_free_num.
      assert (~ NFree y v) by eauto using n_step_to_not_free.
      rewrite i_subst_subst_neq_3; eauto.
  Qed.

  Lemma i_in_to_s_i_in:
    forall x v a i,
    IIn a (i_subst x v i) ->
    forall n, NStep v n ->
    S_IIn x v a i.
  Proof.
    intros x v a i Hi.
    remember (i_subst _ _ _) as j.
    generalize dependent x.
    generalize dependent v.
    generalize dependent i.
    induction Hi;
      intros i_src v y Heq m Hn;
      destruct i_src;
      inversion Heq; subst; clear Heq.
    - constructor.
      auto.
    - assert (IHHi := IHHi _ _ _ eq_refl _ Hn).
      apply s_i_in_if_true; auto.
    - assert (IHHi := IHHi _ _ _ eq_refl _ Hn).
      apply s_i_in_if_false; auto.
    - constructor; eauto.
    - apply s_i_in_seq_r; eauto.
    - rename v0 into x.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        eapply s_i_in_for_eq; eauto.
      }
      assert (r1: i_subst x (NNum n) (i_subst y v i_src) = i_subst y v (i_subst x (NNum n) i_src)). {
        rewrite i_subst_subst_neq_3; eauto using n_step_to_not_free.
      }
      eapply IHHi in r1; eauto.
      eapply s_i_in_for_neq; eauto.
  Qed.

  Lemma b_data_subst:
    forall v v' n n1 x e b,
    NStep v n ->
    NStep v' n ->
    x <> TID ->
    BData n1 (b_subst x v e) b ->
    BData n1 (b_subst x v' e) b. 
  Proof.
    intros.
    assert (r1: NEq v v') by eauto using n_eq_def.
    unfold BData in *.
    assert (~ NFree x (NNum n1)) by auto using n_free_num.
    assert (~ NFree TID v') by eauto using n_step_to_not_free.
    assert (~ NFree TID v) by eauto using n_step_to_not_free.
    rewrite b_subst_subst_neq_3; auto.
    rewrite b_subst_subst_neq_3 in H2; auto.
    rewrite <- r1.
    assumption.
  Qed.

  Lemma n_data_subst:
    forall v v' n n1 x e n',
    NStep v n ->
    NStep v' n ->
    x <> TID -> 
    NData n1 (n_subst x v e) n' ->
    NData n1 (n_subst x v' e) n'. 
  Proof.
    intros.
    assert (r1: NEq v v') by eauto using n_eq_def.
    unfold NData in *.
    assert (~ NFree x (NNum n1)) by auto using n_free_num.
    assert (~ NFree TID v') by eauto using n_step_to_not_free.
    assert (~ NFree TID v) by eauto using n_step_to_not_free.
    rewrite n_subst_subst_neq_3; auto.
    rewrite n_subst_subst_neq_3 in H2; auto.
    rewrite <- r1.
    assumption.
  Qed.

  Lemma r_data_subst:
    forall v v' n n1 x r p,
    NStep v n ->
    NStep v' n ->
    x <> TID -> 
    RData n1 (r_subst x v r) p ->
    RData n1 (r_subst x v' r) p.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    destruct p as (a, b).
    destruct H2 as (Hi,Hj).
    eapply n_data_subst with (v':=v') in Hi; eauto.
    eapply n_data_subst with (v':=v') in Hj; eauto.
  Qed.

  Lemma i_in_subst:
    forall x a i v v' n,
    NStep v n ->
    NStep v' n ->
    IIn a (i_subst x v i) ->
    x <> TID ->
    IIn a (i_subst x v' i).
  Proof.
    intros.
    eapply i_in_to_s_i_in in H1; eauto.
    eapply s_i_in_to_i_in; eauto.
    generalize dependent v'.
    generalize dependent n.
    induction H1; intros; assert (r1: NEq v v') by eauto using n_eq_def.
    - constructor.
      unfold AIn in *.
      destruct H as (l, (Hs, Hi)).
      exists l.
      split; auto.
      eapply access_step_proper; eauto.
      + assert (~ NFree x (NNum (access_tid a))) by auto using n_free_num.
        assert (~ NFree TID v) by eauto using n_step_to_not_free.
        assert (~ NFree TID v') by eauto using n_step_to_not_free.
        rewrite access_subst_subst_neq_3; auto.
        rewrite access_subst_subst_neq_3 with (x:=TID) (y:=x); auto.
        rewrite r1.
        reflexivity.
      + reflexivity.
    - apply s_i_in_if_true; eauto.
      eapply b_data_subst with (v:=v); eauto.
    - apply s_i_in_if_false; eauto.
      eapply b_data_subst with (v:=v); eauto.
    - constructor; eauto.
    - eapply s_i_in_seq_r; eauto.
    - eapply r_data_subst with (v':=v') in H; eauto.
      eauto using s_i_in_for_eq.
    - eapply r_data_subst with (v':=v') in H0; eauto.
      eauto using s_i_in_for_neq.
  Qed.

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
  Section XRun.
  Variable n:nat.
  Variable x:var.
  Variable e:nexp.
  Inductive XRun : inst -> history -> Prop :=
  | x_run_skip:
    XRun Skip []
  | x_run_access:
    forall a v,
    access_step (access_subst x e a, NNum n) v ->
    XRun (MemAcc a) v
  | x_run_seq:
    forall i j h1 h2,
    XRun i h1 ->
    XRun j h2 ->
    XRun (Seq i j) (h1 ++ h2)
  | x_run_if:
    forall e' i j b hi hj,
    BStep (b_subst x e e') b ->
    XRun i hi ->
    XRun j hj ->
    XRun (If e' i j) (if b then hi else hj)
  | x_run_for_cons_eq:
    forall e1 e2 n1 n2 i h1 h2,
    NStep (n_subst x e e1) n1 ->
    NStep (n_subst x e e2) n2 ->
    n1 < n2 ->
    Run n (i_subst x (NNum n1) i) h1 ->
    Run n (For x (NNum (S n1), NNum n2) i) h2 ->
    XRun (For x (e1, e2) i) (h1 ++ h2) 
  | x_run_for_cons_neq:
    forall e1 e2 n1 n2 y i h1 h2,
    x <> y ->
    NStep (n_subst x e e1) n1 ->
    NStep (n_subst x e e2) n2 ->
    n1 < n2 ->
    XRun (i_subst y (NNum n1) i) h1 ->
    XRun (For y (NNum (S n1), NNum n2) i) h2 ->
    XRun (For y (e1, e2) i) (h1 ++ h2) 
  | x_run_for_nil:
    forall e1 e2 n1 n2 y i,
    NStep (n_subst x e e1) n1 ->
    NStep (n_subst x e e2) n2 ->
    n1 >= n2 ->
    XRun (For y (e1, e2) i) []
  .
  End XRun.

  Lemma run_to_x_run:
    forall n x e i h,
    Run n (i_subst x e i) h ->
    forall m,
    NStep e m ->
    XRun n x e i h.
  Proof.
    intros.
    remember (i_subst x e i) as j.
    generalize dependent x.
    generalize dependent e.
    generalize dependent i.
    induction H; intros.
    - destruct i; inversion Heqj; subst; clear Heqj.
      constructor.
    - destruct i; inversion Heqj; subst; clear Heqj.
      constructor.
      assumption.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      constructor; eauto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      eauto using x_run_if.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (e1', e2').
      simpl in *.
      inversion H7; subst; clear H7.
      rename x0 into y.
      rename v into z.
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        eapply x_run_for_cons_eq; eauto.
      }
      apply x_run_for_cons_neq with (n1:=n1) (n2:=n2); auto.
      + apply IHRun1; auto.
        rewrite i_subst_subst_neq_3; auto.
        eauto using n_step_to_not_free.
      + apply IHRun2; auto.
        simpl.
        destruct (Set_VAR.MF.eq_dec y z). {
          contradiction.
        }
        auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (e1', e2').
      inversion H5; subst; clear H5.
      rename x0 into x.
      rename v into y.
      destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        eauto using x_run_for_nil.
      }
      apply x_run_for_nil with (n1:=n1) (n2:=n2); auto.
  Qed.

  Lemma x_run_to_run:
    forall n x e i h,
    XRun n x e i h ->
    forall m,
    NStep e m ->
    Run n (i_subst x e i) h.
  Proof.
    intros n x e i h H.
    induction H; intros; simpl.
    - constructor.
    - constructor; auto.
    - constructor; eauto.
    - constructor; eauto.
    - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      eapply run_for_cons; eauto.
    - destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        simpl in *.
        destruct (Set_VAR.MF.eq_dec y y) as [_|?]; try contradiction.
      }
      simpl in *.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_for_cons; eauto.
      assert (Hx: Run n (i_subst x e (i_subst y (NNum n1) i)) h1). {
        eauto.
      }
      rewrite i_subst_subst_neq_3 in Hx; auto.
      eauto using n_step_to_not_free.
    - destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        eapply run_for_nil; eauto.
      }
      eapply run_for_nil; eauto.
  Qed.

  Lemma run_subst t:
    forall c x e1 h n,
    NStep e1 n ->
    Run t (i_subst x e1 c) h ->
    forall e2,
    NStep e2 n ->
    Run t (i_subst x e2 c) h.
  Proof.
    intros c x e1 h n He1 Hr.
    eapply run_to_x_run in Hr; eauto.
    intros.
    eapply x_run_to_run; eauto.
    generalize dependent e2.
    generalize dependent n.
    induction Hr; intros.
    - simpl.
      constructor.
    - simpl.
      constructor.
      assert (r1: NEq e1 e2) by eauto using n_eq_def.
      eapply access_step_proper; eauto.
      + rewrite r1.
        reflexivity.
      + reflexivity.
    - simpl.
      constructor; eauto.
    - assert (r1: NEq e1 e2) by eauto using n_eq_def.
      rewrite r1 in H.
      eauto using x_run_if.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      rename e1 into e.
      rename e3 into e'.
      assert (r1: NEq e e') by eauto using n_eq_def.
      eapply x_run_for_cons_eq; eauto.
      + rewrite <- r1.
        auto.
      + rewrite <- r1.
        auto.
    - simpl in *.
      rename e1 into e.
      rename e3 into e'.
      assert (r1: NEq e e') by eauto using n_eq_def.
      eapply x_run_for_cons_neq; eauto.
      + rewrite <- r1.
        auto.
      + rewrite <- r1; auto.
    - rename e1 into e.
      rename e3 into e'.
      assert (r1: NEq e e') by eauto using n_eq_def.
      eapply x_run_for_nil; eauto.
      + rewrite <- r1.
        auto.
      + rewrite <- r1; auto.
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
          apply var_inv_subst in N.
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
        apply var_inv_subst in N.
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

  Definition CRun := RunAll TID_COUNT.

  Transparent CRun.

  Lemma run_all_impl:
    forall m,
    forall c1 c2,
    (forall n h, n < m -> Run n (i_subst TID (NNum n) c1) h -> Run n (i_subst TID (NNum n) c2) h) ->
    forall h,
    RunAll m c1 h ->
    RunAll m c2 h.
  Proof.
    induction m; intros. {
      inversion H0; subst; clear H0.
      apply run_all_zero.
    }
    inversion H0; subst; clear H0.
    apply run_all_succ; eauto.
  Qed.

  Lemma c_run_subst:
    forall x e e' c h,
    ~ Var TID c ->
    ~ NFree TID e ->
    ~ NFree TID e' ->
    x <> TID ->
    forall n,
    NStep e n ->
    NStep e' n ->
    CRun (i_subst x e c) h ->
    CRun (i_subst x e' c) h.
  Proof.
    intros.
    apply run_all_impl with (c1:=i_subst x e c); auto.
    intros.
    rewrite i_subst_subst_neq_3; auto.
    rewrite i_subst_subst_neq_3 in H7; auto.
    apply run_subst with (e1:=e)(n:=n); eauto.
  Qed.

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


  Lemma c_in_subst:
    forall (x : VAR.t) (a : access_val) (i : inst) (v v' : nexp) (n : nat),
    NStep v n ->
    NStep v' n ->
    x <> TID ->
    CIn a (i_subst x v i) ->
    CIn a (i_subst x v' i).
  Proof.
    intros.
    inversion H2; subst; clear H2.
    eapply i_in_subst with (v':=v') in H4; eauto.
    eauto using c_in_def.
  Qed.

  (* -------------------------------- C PAIR IN ---------------------- *)

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

  (* ---------------------- C SEQUENCE ---------------- *)
  Fixpoint c_seq (c1:inst) (c2:inst) :=
    match c1 with
    | Skip
    | If _ _ _
    | MemAcc _
    | For _ _ _
      => Seq c1 c2
    | Seq c1 c3 => c_seq c1 (c_seq c3 c2)
    end.

  Definition is_seq c :=
    match c with
    | Skip
    | If _ _ _
    | MemAcc _
    | For _ _ _
      => false
    | Seq _ _ => true
    end.

  Inductive CSeq : inst -> inst -> inst -> Prop :=
  | c_seq_1:
    forall c1 c2,
    is_seq c1 = false ->
    CSeq c1 c2 (Seq c1 c2)
  | c_seq_2:
    forall c1 c2 c3 c3_c2 c1_c3_c2,
    CSeq c3 c2 c3_c2 ->
    CSeq c1 c3_c2 c1_c3_c2 ->
    CSeq (Seq c1 c3) c2 c1_c3_c2.

  Lemma c_seq_to_prop:
    forall c1 c2 c3,
    c_seq c1 c2 = c3 ->
    CSeq c1 c2 c3.
  Proof.
    induction c1; intros; simpl in *; subst; try (apply c_seq_1; auto; fail).
    eapply c_seq_2; eauto.
  Qed.

  Lemma c_seq_from_prop:
    forall c1 c2 c3,
    CSeq c1 c2 c3 ->
    c_seq c1 c2 = c3.
  Proof.
    intros c1 c2 c3 H.
    induction H; simpl in *.
    - destruct c1; simpl in *; auto.
      inversion H.
    - rewrite IHCSeq1.
      rewrite IHCSeq2.
      reflexivity.
  Qed.

  Lemma c_seq_seq:
    forall c1 c2 c3,
    c_seq (c_seq c1 c2) c3 = c_seq c1 (c_seq c2 c3).
  Proof.
    induction c1; intros; simpl; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    auto.
  Qed.

  Lemma c_in_c_seq_r:
    forall a c1 c2,
    CIn a c2 ->
    CIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_in_seq_r.
  Qed.

  Lemma c_in_c_seq_l:
    forall a c1,
    CIn a c1 ->
    forall c2,
    CIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_in_seq_l.
    apply c_in_inv_seq in H.
    destruct H as [H|H].
    - auto using IHc1_1.
    - eapply IHc1_2 with (c2:=c2) in H; eauto using c_in_c_seq_r.
  Qed.

  Lemma c_seq_eq_seq:
    forall c1 c2,
    exists c1' c2', c_seq c1 c2 = Seq c1' c2'.
  Proof.
    induction c1; intros; simpl; eauto.
  Qed.

  Lemma c_seq_neq_mem_acc:
    forall e c1 c2,
    MemAcc e <> c_seq c1 c2.
  Proof.
    intros.
    intros N.
    destruct (c_seq_eq_seq c1 c2) as (c1', (c2', r1)).
    rewrite r1 in N.
    inversion N.
  Qed.

  Lemma c_seq_neq_if:
    forall b c1 c2 c3 c4,
    If b c1 c2 <> c_seq c3 c4.
  Proof.
    intros.
    intros N.
    destruct (c_seq_eq_seq c3 c4) as (c1', (c2', r1)).
    rewrite r1 in N.
    inversion N.
  Qed.

  Lemma i_in_inv_c_seq_l:
    forall a c1 c2 i j,
    IIn a i ->
    c_seq c1 c2 = Seq i j ->
    IIn a c1.
  Proof.
    induction c1; simpl; intros; try (inversion H0; subst; clear H0; assumption; fail).
    eauto using i_in_seq_l.
  Qed.

  Lemma c_seq_inv_if_2:
    forall c1 c2 c3 c4 b,
    ~ CSeq c1 c2 (If b c3 c4).
  Proof.
    induction c1; intros; intros N; inversion N.
    subst.
    apply IHc1_1 in H4.
    assumption.
  Qed.

  Lemma i_in_inv_c_seq_0:
    forall c1 c2 c3,
    CSeq c1 c2 c3 ->
    forall a,
    IIn a c3 ->
    IIn a c1 \/ IIn a c2.
  Proof.
    intros c1 c2 c3 H.
    induction H; intros.
    - inversion H0; auto.
    - apply IHCSeq2 in H1.
      destruct H1; auto using i_in_seq_l.
      apply IHCSeq1 in H1.
      destruct H1; auto using i_in_seq_r.
  Qed.

  Lemma i_in_inv_c_seq:
    forall c1 c2,
    forall a,
    IIn a (c_seq c1 c2) ->
    IIn a c1 \/ IIn a c2.
  Proof.
    intros.
    remember (c_seq c1 c2) as c3.
    symmetry in Heqc3.
    apply c_seq_to_prop in Heqc3.
    eapply i_in_inv_c_seq_0 in Heqc3; eauto.
  Qed.

  Lemma c_in_inv_c_seq:
    forall a c1 c2,
    CIn a (c_seq c1 c2) ->
    CIn a c1 \/ CIn a c2.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply i_in_inv_c_seq in H1.
    destruct H1 as [Hi|Hi]; eauto using c_in_def.
  Qed.

  Definition OneOf a c1 c2 :=
    CIn a c1 \/ CIn a c2.

  Lemma c_pair_in_inv_c_seq:
    forall p c1 c2,
    CPairIn p (c_seq c1 c2) ->
    let (a1, a2) := p in
    OneOf a1 c1 c2 /\
    OneOf a2 c1 c2.
  Proof.
    intros.
    invc H.
    apply c_in_inv_c_seq in H0.
    apply c_in_inv_c_seq in H1.
    unfold OneOf.
    simpl.
    intuition.
  Qed.

  Lemma c_pair_in_c_seq_l:
    forall a c1 c2,
    CPairIn a c1 ->
    CPairIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_pair_in_seq_l.
    invc H.
    apply c_in_inv_seq in H0.
    apply c_in_inv_seq in H1.
    intuition; auto using c_pair_in_def, c_in_c_seq_l, c_in_c_seq_r.
  Qed.

  Lemma c_pair_in_c_seq_r:
    forall a c1 c2,
    CPairIn a c2 ->
    CPairIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_pair_in_seq_r.
  Qed.

  Lemma c_pair_in_to_pair_in:
    forall c h,
    ~ Var TID c ->
    RunAll TID_COUNT c h ->
    forall p,
    CPairIn p c ->
    PairIn p h.
  Proof.
    intros.
    invc H1.
    apply pair_in_def; auto;
    eapply c_in_2; eauto.
  Qed.

  Lemma c_pair_in_subst:
    forall p x e1 c,
    x <> TID ->
    CPairIn p (i_subst x e1 c) ->
    forall n,
    NStep e1 n ->
    forall e2,
    NStep e2 n ->
    CPairIn p (i_subst x e2 c).
  Proof.
    intros.
    invc H0.
    rename_hyp (CIn a1 _) as Hc1.
    rename_hyp (CIn a2 _) as Hc2.
    eapply c_in_subst in Hc1; eauto.
    eapply c_in_subst in Hc2; eauto.
    eauto using c_pair_in_def.
  Qed.

  Lemma c_seq_subst:
    forall x v c1 c2,
    i_subst x v (c_seq c1 c2) = c_seq (i_subst x v c1) (i_subst x v c2).
  Proof.
    induction c1; intros; simpl; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    reflexivity.
  Qed.

  Lemma i_subst_subst_eq_1:
    forall e1 e2 x c,
    i_subst x e1 (i_subst x e2 c) = i_subst x (n_subst x e1 e2) c.
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - erewrite b_subst_subst_eq_1; eauto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite access_subst_subst_eq_1.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq_1.
        reflexivity.
      }
      rewrite r_subst_subst_eq_1.
      rewrite IHc; auto.
  Qed.

  Lemma occurs_inv_subst_eq:
    forall x e c,
    ~ Var x c ->
    Occurs x (i_subst x e c) ->
    NFree x e. 
  Proof.
    intros.
    induction c; simpl in *; intros; intuition.
    - eauto using b_free_inv_subst_eq.
    - eauto using access_free_inv_subst_eq.
    - eauto using r_free_inv_subst_eq.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        contradiction.
      }
      auto.
  Qed.

  Lemma i_subst_not_occurs:
    forall x c,
    ~ Occurs x c ->
    forall v,
    i_subst x v c = c.
  Proof.
    induction c; simpl; intros.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      assert (~ BExp.BFree x b) by intuition.
      rewrite BExp.b_subst_not_free; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite access_subst_not_free; auto.
    - rewrite IHc; auto.
      rewrite r_subst_not_free; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
  Qed.

  Lemma i_subst_not_free:
    forall x c,
    ~ Free x c ->
    forall v,
    i_subst x v c = c.
  Proof.
    induction c; simpl; intros.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      assert (~ BExp.BFree x b) by intuition.
      rewrite BExp.b_subst_not_free; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite access_subst_not_free; auto.
    - rewrite r_subst_not_free; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      rewrite IHc; auto.
  Qed.

  Lemma i_subst_subst_neq_5:
    forall c x y e1 e2,
    NClosed e1 ->
    y <> x ->
    ~ Var y c -> 
    i_subst y e1 (i_subst x e2 c) =
    i_subst x (n_subst y e1 e2) (i_subst y e1 c).
  Proof.
    induction c; intros; simpl in *.
    - reflexivity.
    - rewrite b_subst_subst_neq_5; auto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite access_subst_subst_neq_5; auto.
    - rename v into z.
      rewrite <- r_subst_subst_neq_5; auto.
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        intuition.
      }
      destruct (Set_VAR.MF.eq_dec x z). {
        subst.
        intuition.
      }
      rewrite IHc; auto.
  Qed.

  Lemma eq_c_seq_def:
    forall c1 c2 c1' c2',
    c1 = c1' ->
    c2 = c2' ->
    c_seq c1 c2 = c_seq c1' c2'.
  Proof.
    intros; subst.
    reflexivity.
  Qed.

  Fixpoint Distinct (c:inst) :=
    match c with
    | Skip | MemAcc _ => True
    | If _ c1 c2 | Seq c1 c2 => Distinct c1 /\ Distinct c2
    | For x _ c => ~ Var x c /\ Distinct c
    end.

  Lemma distinct_subst:
    forall c,
    Distinct c ->
    forall x v,
    Distinct (i_subst x v c).
  Proof.
    induction c; simpl; auto; intros.
    - intuition.
    - intuition.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        intuition.
      }
      intuition.
      apply var_inv_subst in H2.
      intuition.
  Qed.

  Lemma distinct_c_seq:
    forall c1 c2,
    Distinct c1 ->
    Distinct c2 ->
    Distinct (c_seq c1 c2).
  Proof.
    induction c1; simpl; intros; auto.
    destruct H as (d1, d2).
    auto.
  Qed.

  Lemma i_subst_c_seq:
    forall x v c1 c2,
    i_subst x v (c_seq c1 c2)
    = c_seq (i_subst x v c1) (i_subst x v c2).
  Proof.
    induction c1; simpl; intros; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    auto.
  Qed.

  Definition CClosed P :=
    forall x, ~ Occurs x P.

  Lemma var_inv_c_seq:
    forall x c1 c2,
    Var x (c_seq c1 c2) ->
    Var x c1 \/ Var x c2.
  Proof.
    induction c1; simpl; intros; try (intuition; fail).
    apply IHc1_1 in H.
    intuition.
    apply IHc1_2 in H0.
    intuition.
  Qed.

  Lemma occurs_inv_c_seq:
    forall x c1 c2,
    Occurs x (c_seq c1 c2) ->
    Occurs x c1 \/ Occurs x c2.
  Proof.
    induction c1; simpl; intros; try (intuition; fail).
    apply IHc1_1 in H.
    intuition.
    apply IHc1_2 in H0.
    intuition.
  Qed.

End C1.

Module CLangNotations.
  Declare Scope lang_scope.
  Notation  "'FOR' x '∈' r '{' c '}' " := (For x r c) : lang_scope. 
  Infix ";" := Seq (at level 50, only printing) : lang_scope.
  Notation "c [ x := v ]" := (i_subst x v c) (at level 30, only printing) : lang_scope. 
  Infix ";;" := c_seq (at level 50, only printing) : lang_scope.
  Infix "∈" := CIn (at level 30, only printing) : lang_scope.
  Infix "∈" := CPairIn (at level 30, only printing) : lang_scope.
End CLangNotations.
