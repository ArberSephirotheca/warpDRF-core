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

  Lemma f_run_decl_map:
     forall n1 n2 i x lm,
     DeclMap x i n1 n2 lm ->
     FRun (Decl x (NNum n1, NNum n2) i) (summation lm).
  Proof.
    eauto using f_run_branch_map, f_run_decl, r_step_range_list.
  Qed.

  Lemma f_run_branch_inv_map:
    forall l i x m,
    FRun (Branch x l i) m ->
    NoDup l ->
    exists lm,
    EEq m (summation lm) /\
    BranchMap x i l lm.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      exists [].
      simpl.
      auto using map_nil.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHl in H7; auto; clear IHl.
    destruct H7 as (lm, (R2,Hr)).
    eexists. split. 2: {
      apply map_cons; eauto.
    }
    simpl.
    rewrite H8.
    rewrite R2.
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
    inversion H; subst; clear H.
    apply r_step_to_range_list in H4.
    subst.
    eauto using f_run_branch_inv_map, range_list_no_dup.
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
    forall x n1 n2 i j m1 m2,
    DeclMap x i n1 n2 m1 ->
    DeclMap x j n1 n2 m2 ->
    FRun (Decl x (NNum n1, NNum n2) (Seq i j)) (summation (map2 Prod m1 m2)).
  Proof.
    intros.
    eapply f_run_decl_map; eauto.
    apply decl_map_seq; auto.
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
      eapply f_run_decl_map; eauto.
      rewrite i_subst_not_in; auto.
    }
    apply map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply f_run_decl_map; eauto.
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
      eauto using p_eq_decl_map, f_run_decl_map. 
    - apply f_run_inv_decl_map in H0.
      destruct H0 as (lm, (R, Hr1)).
      rewrite R; clear R m.
      eapply p_eq_decl_map in Hr1; eauto using f_run_decl_map.
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

End Defs.