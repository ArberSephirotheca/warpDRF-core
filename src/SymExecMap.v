Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import AccExp.
Require Import Exp.
Require Import MExp.
Require Import MultiHist.
Require Import SymExec2.
Require Import SymExecMRun.
Require Import SymExecEq.
Import ListNotations.
Import MHistNotations.

(* 

  Abstraction to handle loops.

 *)

Section Defs.
  Context {A:Access}.
  Context {I:AccessInst}.
  Notation history := (list access_val).

  (* --------------------- DeclMap ------------------------------- *)

  Notation Iter x i := (fun n=> FRun (i_subst x (NNum n) i)).  
  Notation BranchMap x i l m := (Map (Iter x i) l m).
  Definition DeclMap x i n1 n2 m := BranchMap x i (range_list n1 n2) m.

  Transparent DeclMap.

  Definition DeclRun x r i m :=
    exists l ms,
    RStep r l /\
    BranchMap x i l ms /\
    m == summation ms.

  Lemma decl_run_def:
    forall x r i m l ms,
    RStep r l ->
    BranchMap x i l ms ->
    m == summation ms ->
    DeclRun x r i m.
  Proof.
    unfold DeclRun; eauto.
  Qed.

  Lemma decl_run_eq:
    forall x r i ms l,
    RStep r l ->
    BranchMap x i l ms ->
    DeclRun x r i (summation ms).
  Proof.
    intros.
    eapply decl_run_def; eauto.
    reflexivity.
  Qed.

  Lemma decl_run_range:
    forall x n1 n2 i ms m,
    BranchMap x i (range_list n1 n2) ms ->
    m == summation ms ->
    DeclRun x (NNum n1, NNum n2) i m.
  Proof.
    intros.
    eapply decl_run_def; eauto using r_step_range_list.
  Qed.

  Lemma decl_run_range_eq:
    forall x n1 n2 i ms,
    BranchMap x i (range_list n1 n2) ms ->
    DeclRun x (NNum n1, NNum n2) i (summation ms).
  Proof.
    intros.
    eapply decl_run_range; eauto.
    reflexivity.
  Qed.

  Lemma branch_map_eq_list:
    forall l x i ms ms',
    EEqList ms' ms ->
    BranchMap x i l ms' ->
    BranchMap x i l ms.
  Proof.
    induction l; intros.
    - inversion H0; subst; clear H0; auto.
      inversion H; subst; clear H.
      auto using map_nil.
    - inversion H0; subst; clear H0.
      inversion H; subst; clear H.
      apply map_cons; eauto.
      rewrite <- H2.
      assumption.
  Qed.

  Lemma decl_run_inv_range:
    forall x n1 n2 i m,
    DeclRun x (NNum n1, NNum n2) i m ->
    exists ms, m == summation ms /\ BranchMap x i (range_list n1 n2) ms.
  Proof.
    unfold DeclRun.
    intros.
    destruct H as (l', (ms', (Hr, (Hb, R)))).
    apply r_step_to_range_list in Hr.
    subst.
    eauto.
  Qed.

  Lemma r_step_nil:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    RStep (e1, e2) [].
  Proof.
    intros.
    eauto using r_step_def, range_list_nil.
  Qed.

  Lemma r_step_cons:
    forall e1 e2 n1 n2 l,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RStep (NNum (S n1), NNum n2) l ->
    RStep (e1, e2) (n1 :: l).
  Proof.
    intros.
    apply r_step_to_range_list in H2.
    symmetry in H2.
    assert (Hx := r_step_range_list n1 n2).
    eapply r_step_def; eauto.
    apply range_list_cons; auto.
    rewrite <- H2.
    apply range_list_to_prop.
    reflexivity.
  Qed.

  Lemma decl_run_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    FRun (i_subst x (NNum n1) i) m1 ->
    DeclRun x (NNum (S n1), NNum n2) i m2 ->
    m3 == m1 + m2 ->
    DeclRun x (e1, e2) i m3.
  Proof.
    intros.
    unfold DeclRun in *.
    destruct H3 as (l, (ms, (Hr, (Hm, Hs)))).
    exists (n1::l).
    exists (m1::ms).
    simpl.
    split. { eauto using r_step_cons. }
    split. {
      apply map_cons; auto.
      intros N.
      apply r_step_to_range_list in Hr.
      subst.
      apply range_list_in_iff in N.
      Import Omega.
      omega.
    }
    repeat match goal with
      H: _ == _ |- _ => rewrite H; clear H
    end.
    reflexivity.
  Qed.

  Lemma decl_run_nil:
    forall e1 e2 n1 n2 m x i,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    m == One [] ->
    DeclRun x (e1, e2) i m.
  Proof.
    unfold DeclRun.
    intros.
    exists [].
    exists [].
    split. { eauto using r_step_nil. }
    split. { auto using map_nil. }
    simpl.
    assumption.
  Qed.

  Lemma f_run_to_decl_run:
    forall x r i m,
    FRun (Decl x r i) m ->
    DeclRun x r i m.
  Proof.
    intros.
    remember (Decl _ _ _) as j.
    generalize dependent x.
    generalize dependent r.
    generalize dependent i.
    induction H; intros; inversion Heqj; subst; clear Heqj.
    - eauto using decl_run_cons.
    - eauto using decl_run_nil.
  Qed.

  Lemma decl_run_to_f_run:
    forall x r i m,
    DeclRun x r i m ->
    FRun (Decl x r i) m.
  Proof.
    unfold DeclRun; intros.
    destruct H as (l, (ms, (Hr, (Hm, R)))).
    generalize dependent m.
    generalize dependent x.
    generalize dependent ms.
    generalize dependent i.
    inversion Hr; subst; clear Hr.
    generalize dependent e1.
    generalize dependent e2.
    induction H1; intros.
    - inversion Hm; subst; clear Hm.
      simpl in *.
      eapply f_run_decl_nil; eauto.
    - inversion Hm; subst; clear Hm.
      simpl in *.
      eapply f_run_decl_cons; eauto.
      eapply IHRangeList; eauto using n_step_num.
      reflexivity.
  Qed.

  Lemma decl_run_iff:
    forall x r i m,
    DeclRun x r i m <->
    FRun (Decl x r i) m.
  Proof.
    split; intros; auto using decl_run_to_f_run, f_run_to_decl_run.
  Qed.
(*
  Lemma f_run_branch_map:
    forall l i x ml,
    BranchMap x i l ml ->
    FRun (Branch x l i) (summation ml).
  Proof.
    induction l; intros; subst; inversion H; subst; clear H.
    - simpl.
      auto using f_run_branch_nil_eq.
    - apply IHl in H5; auto; clear IHl.
      simpl.
      apply f_run_branch_cons_eq; auto.
  Qed.
*)
  Lemma f_run_decl_map:
     forall n1 n2 i x lm m,
     DeclMap x i n1 n2 lm ->
     m == summation lm ->
     FRun (Decl x (NNum n1, NNum n2) i) m.
  Proof.
    intros.
    apply decl_run_iff.
    eauto using decl_run_range.
  Qed.

  Lemma f_run_decl_map_eq:
     forall n1 n2 i x lm,
     DeclMap x i n1 n2 lm ->
     FRun (Decl x (NNum n1, NNum n2) i) (summation lm).
  Proof.
    intros.
    eapply f_run_decl_map; eauto.
    reflexivity.
  Qed.

  Lemma f_run_inv_decl_map:
    forall n1 n2 i x m',
    FRun (Decl x (NNum n1, NNum n2) i) m' ->
    exists lm,
    EEq m' (summation lm) /\
    DeclMap x i n1 n2 lm.
  Proof.
    intros.
    apply decl_run_iff in H.
    apply decl_run_inv_range in H.
    eauto.
  Qed.

  Lemma branch_map_inv_seq:
    forall l x i j ms1, 
    BranchMap x (Seq i j) l ms1 ->
    exists ms2 ms3,
    BranchMap x i l ms2 /\ BranchMap x j l ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      eauto using map_nil, e_eq_list_nil.
    }
    inversion H; subst; clear H.
    simpl in H2.
    inversion H2; subst; clear H2.
    apply IHl in H5.
    destruct H5 as (ms2, (ms3, (Hb1, (Hb2, R2)))).
    eexists.
    eexists.
    repeat split.
    - eauto using map_cons.
    - eauto using map_cons.
    - rewrite map2_cons_rw.
      auto using e_eq_list_cons.
  Qed.

  Lemma branch_map_seq:
    forall l x i j ms1 ms2, 
    BranchMap x i l ms1 ->
    BranchMap x j l ms2 ->
    BranchMap x (Seq i j) l (map2 Prod ms1 ms2).
  Proof.
    induction l; intros; inversion H; inversion H0; subst; clear H H0. {
      apply map_nil.
    }
    rewrite map2_cons_rw.
    apply map_cons; auto.
    simpl.
    auto using f_run_seq_eq.
  Qed.

  Lemma decl_map_inv_seq:
    forall n1 n2 x i j ms1, 
    DeclMap x (Seq i j) n1 n2 ms1 ->
    exists ms2 ms3,
    DeclMap x i n1 n2 ms2 /\ DeclMap x j n1 n2 ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    eauto using branch_map_inv_seq.
  Qed.

  Lemma decl_map_seq:
    forall n1 n2 x i j ms1 ms2, 
    DeclMap x i n1 n2 ms1 ->
    DeclMap x j n1 n2 ms2 ->
    DeclMap x (Seq i j) n1 n2 (map2 Prod ms1 ms2).
  Proof.
    unfold DeclMap.
    eauto using branch_map_seq.
  Qed.

  Lemma decl_map_inv_i_subst_eq:
    forall x y i n1 n2 m1,
    ~ In x i ->
    DeclMap x (i_subst y (NVar x) i) n1 n2 m1 ->
    DeclMap y i n1 n2 m1.
  Proof.
    unfold DeclMap.
    intros x y i n1 n2 m1 Hn1 Hd.
    apply map_impl with (P:=Iter x (i_subst y (NVar x) i)); auto.
    intros.
    rewrite i_subst_subst_trans in H; auto.
  Qed.

  Lemma run_decl_seq:
    forall x n1 n2 i j m1 m2 m3,
    DeclMap x i n1 n2 m1 ->
    DeclMap x j n1 n2 m2 ->
    m3 == summation (map2 Prod m1 m2) ->
    FRun (Decl x (NNum n1, NNum n2) (Seq i j)) m3.
  Proof.
    intros.
    eapply f_run_decl_map; eauto.
    apply decl_map_seq; auto.
  Qed.

  Lemma run_decl_seq_eq:
    forall x n1 n2 i j m1 m2,
    DeclMap x i n1 n2 m1 ->
    DeclMap x j n1 n2 m2 ->
    FRun (Decl x (NNum n1, NNum n2) (Seq i j)) (summation (map2 Prod m1 m2)).
  Proof.
    intros.
    eapply run_decl_seq; eauto.
    reflexivity.
  Qed.

  Let i_subst_not_in_decl_rw:
    forall x n1 y n2 i hs,
    ~ In x i ->
    x <> y ->
    FRun (i_subst x (NNum n2) (Decl y (NNum n1, NVar x) i)) hs ->
    FRun (Decl y (NNum n1, NNum n2) i) hs.
  Proof.
    intros.
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
    end.
    simpl in Hr.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?].
    2: { contradiction. }
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]. { contradiction. }
    rewrite i_subst_not_in in Hr; auto.
  Qed.

  Lemma branch_map_inv_decl_not_in:
    forall l n1 i ms x y,
    ~ In x i ->
    x <> y ->
    l <> [] ->
    BranchMap x (Decl y (NNum n1, NVar x) i) l ms ->
    NoDup l ->
    exists hs,
    EEqList ms (map (fun x => (summation x)) hs) /\
    Map (DeclMap y i n1) l hs.
  Proof.
    induction l; intros n i ms x y Hn1 Hneq Hnil Hb Hd. {
      contradiction.
    }
    clear Hnil.
    destruct l; inversion Hb; subst; clear Hb. {
      match goal with
      | [ H: FRun _ _ |- _ ] => rename H into Hr
      end.
      apply i_subst_not_in_decl_rw in Hr; auto.
      apply f_run_inv_decl_map in Hr.
      destruct Hr as (ms1, (R, Hr)).
      inversion H4; clear H4.
      subst.
      exists [ms1].
      simpl.
      rewrite R.
      repeat split; auto using map_cons, map_nil.
      reflexivity.
    }
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
    end.
    apply i_subst_not_in_decl_rw in Hr; auto.
    apply f_run_inv_decl_map in Hr.
    destruct Hr as (ms1, (R, Hr)).
    subst.
    inversion Hd; subst; clear Hd.
    apply IHl in H4; auto; clear IHl.
    2: { intros N; inversion N. }
    destruct H4 as (hs, (R1, Hmap)).
    eexists.
    split. 2: { apply map_cons; eauto. }
    rewrite R1.
    simpl.
    rewrite R.
    reflexivity.
  Qed.

  Lemma decl_map_inv_decl_not_in:
    forall n1 n2 n3 i ms x y,
    ~ In x i ->
    x <> y ->
    n2 < n3 ->
    DeclMap x (Decl y (NNum n1, NVar x) i) n2 n3 ms ->

    exists hs,
    EEqList ms (map summation hs) /\
    Map (DeclMap y i n1) (range_list n2 n3) hs.
  Proof.
    intros.
    apply branch_map_inv_decl_not_in in H2; auto using range_list_no_dup, range_list_not_nil.
  Qed.

  Lemma branch_map_decl:
    forall l n1 i hs x y,
    ~ In x i ->
    x <> y ->
    l <> [] ->
    NoDup l ->
    Map (DeclMap y i n1) l hs ->
    BranchMap x (Decl y (NNum n1, NVar x) i) l (map summation hs).
  Proof.
    induction l; intros. {
      contradiction.
    }
    match goal with H: NoDup _ |- _ => inversion H; subst;clear H end.
    match goal with H: Map _ _ _ |- _ => inversion H; subst;clear H end.
    destruct l. {
      match goal with H: Map _ _ _ |- _ => inversion H; subst;clear H end.
      apply map_cons; auto using map_nil.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply f_run_decl_map_eq; eauto.
      rewrite i_subst_not_in; auto.
    }
    apply map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply f_run_decl_map_eq; eauto.
      rewrite i_subst_not_in; auto.
    - assumption.
    - apply IHl; auto.
      intros N; inversion N.
  Qed.

  Lemma decl_map_decl:
    forall n1 n2 n3 i j hs m x y,
    ~ In x i ->
    x <> y ->
    n2 < n3 ->
    FRun j m ->
    Map (DeclMap y i n1) (range_list n2 n3) hs ->
    DeclMap x (Decl y (NNum n1, NVar x) i) n2 n3 (map summation hs).
  Proof.
    intros.
    apply branch_map_decl; auto using range_list_no_dup, range_list_not_nil.
  Qed.



(*
  Lemma p_eq_branch_skip:
    forall l,
    NoDup l ->
    forall x,
    ProgEquiv (Branch x l Skip) Skip.
  Proof.
    intros.
    apply prog_equiv_def; apply prog_impl_def; intros.
    - generalize dependent m.
      induction l; intros. {
        inversion H0; subst; clear H0.
        rewrite H4.
        auto using f_run_skip_eq.
      }
      inversion H0; subst; clear H0.
      inversion H; subst; clear H.
      apply IHl in H7; auto.
      inversion H7; subst; clear H7.
      rewrite H in *.
      rewrite e_plus_nil_r in H8.
      rewrite H8 in *.
      simpl in *.
      assumption.
    - inversion H0; subst; clear H0.
      rewrite H1; clear H1.
      clear m.
      induction l; intros. {
        apply f_run_branch_nil.
        reflexivity.
      }
      inversion H; subst; clear H.
      eapply f_run_branch_cons; eauto.
      + simpl.
        apply f_run_skip_eq.
      + rewrite e_plus_nil_r.
        reflexivity.
  Qed.
*)
  Lemma map_inv_cons:
    forall A B (P: A -> B -> Prop) ks vs v,
    Map P ks (v :: vs) ->
    exists k ks', ks = k :: ks' /\ ~ List.In k ks' /\ P k v /\ Map P ks' vs.
  Proof.
    intros.
    inversion H; subst; clear H.
    exists k, ks0.
    auto.
  Qed.

  Lemma decl_map_inv_cons:
    forall x i n1 n2 m lm,
    DeclMap x i n1 n2 (m :: lm) ->
    Iter x i n1 m /\ 
    DeclMap x i (S n1) n2 lm.
  Proof.
    intros.
    unfold DeclMap in H.
    remember (range_list n1 n2) as ks.
    apply map_inv_cons in H.
    destruct H as (k, (ks', (?, (Hn, (Hf, Hb))))).
    subst.
    apply range_list_to_prop in H.
    inversion H; subst; clear H.
    apply prop_to_range_list in H5.
    subst.
    auto.
  Qed.

  Lemma branch_map_not_in:
    forall x i m l,
    ~ In x i ->
    FRun i m ->
    NoDup l ->
    BranchMap x i l (repeat m (length l)).
  Proof.
    induction l; intros.
    - apply map_nil.
    - intros.
      inversion H1; subst; clear H1.
      apply map_cons; auto.
      rewrite i_subst_not_in; auto.
  Qed.

  Lemma branch_map_inv_not_in:
    forall x i m l ms,
    ~ In x i ->
    FRun i m ->
    BranchMap x i l ms ->
    EEqList (repeat m (length l)) ms.
  Proof.
    induction l; intros.
    - inversion H1; subst; clear H1.
      simpl in *.
      reflexivity.
    - simpl in *.
      inversion H1; subst; clear H1.
      apply IHl in H7; auto with *.
      simpl.
      rewrite i_subst_not_in in H4; auto.
      apply e_eq_list_cons; auto.
      eauto using f_run_fun.
  Qed.

  Lemma f_run_decl_skip:
    forall x n1 n2,
    FRun (Decl x (NNum n1, NNum n2) Skip) (One []).
  Proof.
    intros.
    eapply f_run_decl_map.
    - apply branch_map_not_in.
      + intros N.
        inversion N.
      + apply f_run_skip_eq.
      + auto using range_list_no_dup.
    - rewrite e_summation_repeat_nil.
      reflexivity.
  Qed.

  Lemma f_run_inv_decl_skip:
    forall x r m,
    FRun (Decl x r Skip) m ->
    m == One [].
  Proof.
    intros.
    edestruct f_run_inv_decl_r_step as (l, Hr); eauto.
    inversion Hr; subst; clear Hr.
    eapply f_run_decl_1 in H; eauto.
    apply f_run_inv_decl_map in H.
    destruct H as (lm, (R, Hd)).
    eapply branch_map_inv_not_in in Hd; eauto using f_run_skip_eq.
    rewrite R.
    apply eq_list_summation_rw in Hd.
    rewrite <- Hd.
    rewrite e_summation_repeat_nil.
    reflexivity.
  Qed.

  Lemma p_eq_decl_skip:
    forall n1 n2 x,
    ProgEquiv (Decl x (NNum n1, NNum n2) Skip) Skip.
  Proof.  
    split; intros.
    - apply f_run_inv_decl_skip in H.
      auto using f_run_skip.
    - inversion H; subst; clear H.
      rewrite H0; clear H0 m.
      apply f_run_decl_skip.
  Qed.

  (* -------------------------- Program Equivalence ------------------------- *)

  Lemma p_eq_branch_map:
    forall l i j x hss,
    (forall n, List.In n l ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    BranchMap x i l hss ->
    BranchMap x j l hss.
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0.
      auto using map_nil.
    }
    inversion H0; subst; clear H0.
    assert (hi: List.In a (a :: l)) by eauto using in_eq.
    assert (Hx := H _ hi); clear hi.
    assert (Hy: forall n : nat,
       List.In n l -> ProgEquiv (i_subst x (NNum n) i) (i_subst x (NNum n) j)) by auto using in_cons.
    assert (IHl := IHl i j x vs Hy H6).
    apply map_cons; auto.
    eapply prog_equiv_inv_l in H3; eauto.
  Qed.

  Lemma p_eq_decl_map:
    forall n1 n2 i j x l,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    DeclMap x i n1 n2 l ->
    DeclMap x j n1 n2 l.
  Proof.
    intros.
    apply p_eq_branch_map with (j:=j) in H0; auto.
    intros.
    apply range_list_inv_in_2 in H1.
    auto.
  Qed.


  Lemma p_eq_decl_impl:
    forall n1 n2 i j x,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    ProgEquiv (Decl x (NNum n1, NNum n2) i) (Decl x (NNum n1, NNum n2) j).
  Proof.
    intros.
    split; intros.
    - apply f_run_inv_decl_map in H0.
      destruct H0 as (lm, (R, Hr1)).
      rewrite R; clear R m.
      eauto using p_eq_decl_map, f_run_decl_map_eq.
    - apply f_run_inv_decl_map in H0.
      destruct H0 as (lm, (R, Hr1)).
      rewrite R; clear R m.
      eapply p_eq_decl_map in Hr1; eauto using f_run_decl_map_eq.
      intros.
      rewrite H; auto.
      reflexivity.
  Qed.

  (* ------------------------------ 2d-map --------------------------------- *)

  Definition range_list_2d_inner n : list (nat*nat) :=
    List.map (pair n) (range_list 0 n).

  Definition range_list_2d n1 n2 :=
    List.flat_map range_list_2d_inner (range_list n1 n2).

  Definition Iter2d x y i (p:nat*nat) :=
    let (nx,ny) := p in
    FRun
      (i_subst y (NNum ny)
        (i_subst x (NNum nx) i))
  .

  Lemma f_run_branch_map_2d_inner:
    forall ks vs x y i n,
    Map (Iter2d x y i) (map (pair n) ks) vs ->
    FRun
      (Branch y ks (i_subst x (NNum n) i))
      (summation vs).
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      apply f_run_branch_nil.
      reflexivity.
    }
    inversion H; subst; clear H.
    simpl in *.
    apply IHks in H5.
    apply f_run_branch_cons_eq; auto.
  Qed.

  Lemma f_run_inv_branch_map_2d_inner:
    forall ks x y i n m,
    NoDup ks ->
    FRun
      (Branch y ks (i_subst x (NNum n) i))
      m ->
    exists vs,
    m == summation vs /\
    Map (Iter2d x y i) (map (pair n) ks) vs.
  Proof.
    induction ks; intros. {
      simpl.
      inversion H0; subst; inversion H0.
      subst.
      exists [].
      rewrite H4.
      split; auto using map_nil.
      reflexivity.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHks in H8; auto.
    destruct H8 as (vs, (R3, Hm)).
    exists (m1 :: vs).
    repeat match goal with
     H: _ == _ |- _ => rewrite H; clear H
    end.
    split. { reflexivity. }
    simpl.
    apply map_cons; auto.
    intros N.
    apply in_map_iff in N.
    destruct N as (m', (R, Hi)).
    inversion R; subst; clear R.
    contradiction.
  Qed.

  Lemma f_run_decl_map_2d_inner:
    forall x y i n l,
    Map (Iter2d x y i) (range_list_2d_inner n) l ->
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i)) (summation l).
  Proof.
    intros.
    apply f_run_decl with (l0:=range_list 0 n); auto using r_step_range_list.
    unfold range_list_2d_inner in H.
    auto using f_run_branch_map_2d_inner.
  Qed.

  Lemma f_run_inv_decl_map_2d_inner:
    forall x y i n m,
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i)) m ->
    exists l,
    m == summation l /\
    Map (Iter2d x y i) (range_list_2d_inner n) l.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply r_step_to_range_list in H4.
    subst.
    apply f_run_inv_branch_map_2d_inner in H5;
      auto using range_list_no_dup.
  Qed.

  Lemma f_run_branch_map_2d:
    forall ks x y i l,
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l ->
    x <> y ->
    FRun (Branch x ks (Decl y (NNum 0, NVar x) i)) (summation l).
  Proof.
    induction ks; intros. {
      simpl in *.
      inversion H; subst; clear H.
      apply f_run_branch_nil.
      reflexivity.
    }
    simpl in *.
    apply map_inv_app in H.
    destruct H as (l1', (l2', (?, (Hm1, Hm2)))).
    subst.
    apply IHks in Hm2.
    eapply f_run_branch_cons; eauto.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      apply f_run_decl_map_2d_inner; eauto.
    - rewrite e_summation_app.
      reflexivity.
    - assumption.
  Qed.

  Lemma no_dup_inv_app_in:
    forall A l1 l2,
    @NoDup A (l1 ++ l2) ->
    forall a,
    List.In a (l1 ++ l2) ->
    (List.In a l1 /\ ~ List.In a l2) \/
    (~ List.In a l1 /\ List.In a l2).
  Proof.
    induction l1; intros. {
      simpl in *.
      right.
      auto.
    }
    simpl in *.
    inversion H; subst; clear H.
    destruct H0 as [?|Hi]. {
      subst.
      left.
      split; auto.
      intros N.
      contradict H3.
      apply in_app_iff.
      auto.
    }
    apply IHl1 with (a:=a0) in H4; auto.
    destruct H4 as [(Ha,Hb)|(Ha,Hb)]; auto.
    right.
    split. {
      intros N.
      destruct N as [N|N]. {
        subst.
        contradiction.
      }
      contradiction.
    }
    assumption.
  Qed.

  Lemma no_dup_app:
    forall A l1 l2,
    @NoDup A l1 ->
    NoDup l2 ->
    (forall x, List.In x l1 -> List.In x l2 -> False) ->
    NoDup (l1 ++ l2). 
  Proof.
    induction l1; intros. {
      simpl.
      assumption.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl1 in H0; auto. {
      apply NoDup_cons; auto.
      intros N.
      apply no_dup_inv_app_in in N; auto.
      destruct N as [(N1,N2)|(N1,N2)]; try contradiction.
      eapply H1; eauto using in_eq.
    }
    intros.
    eapply H1; eauto using in_cons.
  Qed.

  Lemma no_dup_map_pair:
    forall A B l n,
    @NoDup B l ->
    NoDup (map (@pair A B n) l).
  Proof.
    induction l; intros. {
      apply NoDup_nil.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl with (n:=n) in H3.
    apply NoDup_cons; auto.
    intros N.
    apply in_map_iff in N.
    destruct N as (x, (R, Hi)).
    inversion R; subst; clear R.
    contradiction.
  Qed.

  Lemma no_dup_flat_map_range_2d_inner:
    forall l,
    NoDup l ->
    NoDup (flat_map range_list_2d_inner l).
  Proof.
    induction l; intros. {
      simpl.
      apply NoDup_nil.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl in H3; clear IHl.
    unfold range_list_2d_inner.
    apply no_dup_app; auto using range_list_no_dup, no_dup_map_pair.
    intros.
    apply in_map_iff in H.
    destruct H as (m, (R, Hi)).
    subst.
    apply in_flat_map in H0.
    destruct H0 as (y, (Hj, Hk)).
    apply in_map_iff in Hk.
    destruct Hk as (z, (R, Hk)).
    inversion R; subst; clear R.
    contradiction.
  Qed.

  Lemma f_run_inv_branch_map_2d:
    forall ks x y i m,
    FRun (Branch x ks (Decl y (NNum 0, NVar x) i)) m ->
    x <> y ->
    NoDup ks ->
    exists l,
    EEq m (summation l) /\
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l.
  Proof.
    induction ks; intros; inversion H; subst; clear H. {
      exists [].
      rewrite H5.
      split. { reflexivity. }
      simpl.
      apply map_nil.
    }
    inversion H1; subst; clear H1.
    apply IHks in H8; auto; clear IHks.
    destruct H8 as (lm2, (R2, Hm2)).
    simpl in H7.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
    apply f_run_inv_decl_map_2d_inner in H7.
    destruct H7 as (lm1, (R3, Hm1)).
    exists (lm1 ++ lm2).
    split. {
      repeat match goal with
        H: _ == _ |- _ => rewrite H; clear H
      end.
      rewrite e_summation_app.
      reflexivity.
    }
    remember (flat_map range_list_2d_inner (a :: ks)) as fl.
    rewrite Heqfl.
    simpl.
    apply map_app; auto.
    assert (R: range_list_2d_inner a ++ flat_map range_list_2d_inner ks
      = fl). {
      subst.
      reflexivity.
    }
    rewrite R.
    rewrite Heqfl.
    auto using no_dup_flat_map_range_2d_inner, NoDup_cons.
  Qed.

  Lemma f_run_decl_map_2d:
    forall x y i n1 n2 l,
    x <> y ->
    Map (Iter2d x y i) (range_list_2d n1 n2) l ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i))
      (summation l).
  Proof.
    intros.
    apply f_run_decl with (l0:=range_list n1 n2).
    - auto using r_step_range_list.
    - unfold range_list_2d in H.
      auto using f_run_branch_map_2d.
  Qed.

  Lemma f_run_inv_decl_map_2d:
    forall x y i n1 n2 m,
    x <> y ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i))
      m ->
    exists l,
    EEq m (summation l) /\
    Map (Iter2d x y i) (range_list_2d n1 n2) l.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    unfold range_list_2d.
    apply r_step_to_range_list in H5.
    subst.
    apply f_run_inv_branch_map_2d in H6; auto using range_list_no_dup.
  Qed.


  Lemma range_list_2d_inv_in:
    forall nx ny n1 n2,
    List.In (nx, ny) (range_list_2d n1 n2) ->
    n1 <= nx < n2 /\ 0 <= ny < nx.
  Proof.
    unfold range_list_2d.
    intros.
    apply in_flat_map in H.
    destruct H as (x, (Ha, Hb)).
    unfold range_list_2d_inner in *.
    apply in_map_iff in Hb.
    destruct Hb as (y, (R, Hc)).
    inversion R; subst; clear R.
    apply range_list_in_iff in Ha.
    apply range_list_in_iff in Hc.
    auto.
  Qed.

  Lemma iter_2d_inv_seq:
    forall x y i j p m,
    Iter2d x y (Seq i j) p m ->
    exists m1 m2,
    m == m1 * m2 /\
    Iter2d x y i p m1 /\
    Iter2d x y j p m2.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in H.
    inversion H; subst; clear H.
    exists m1, m2.
    split; auto.
  Qed.

  Lemma iter_2d_seq:
    forall x y i j p m1 m2 m3,
    Iter2d x y i p m1 ->
    Iter2d x y j p m2 ->
    m3 == m1 * m2 ->
    Iter2d x y (Seq i j) p m3.
  Proof.
    intros.
    unfold Iter2d in *.
    destruct p as (nx, ny).
    simpl.
    eapply f_run_seq; eauto.
  Qed.

  Lemma iter_2d_seq_eq:
    forall x y i j p m1 m2,
    Iter2d x y i p m1 ->
    Iter2d x y j p m2 ->
    Iter2d x y (Seq i j) p (m1 * m2).
  Proof.
    intros.
    eapply iter_2d_seq; eauto.
    reflexivity.
  Qed.

  Lemma map_iter_2d_inv_seq:
    forall ks vs i j x y,
    Map (Iter2d x y (Seq i j)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Prod vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d x y i) ks vs1 /\
    Map (Iter2d x y j) ks vs2.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      exists [], [].
      rewrite map2_nil_l.
      split. { reflexivity. }
      auto using map_nil.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    destruct H5 as (vs1, (vs2, (R1, (Hl, (Hm1, Hm2))))).
    apply iter_2d_inv_seq in H2.
    destruct H2 as (m1, (m2, (R2, (Hr1, Hr2)))).
    exists (m1 :: vs1), (m2::vs2).
    split. {
      rewrite R2.
      rewrite R1.
      rewrite map2_cons_rw.
      reflexivity.
    }
    simpl.
    auto using map_cons.
  Qed.


  Lemma map_iter2d_map2_prod:
    forall ks vs1 vs2 x y i j,
    Map (Iter2d x y i) ks vs1 ->
    Map (Iter2d x y j) ks vs2 ->
    Map (Iter2d x y (Seq i j)) ks (map2 Prod vs1 vs2).
  Proof.
    induction ks; intros. {
      inversion H; subst.
      rewrite map2_nil_l.
      apply map_nil.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHks with (vs1:=vs) (i:=i) in H8; eauto.
    apply map_cons; auto using iter_2d_seq_eq.
  Qed.

End Defs.