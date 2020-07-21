Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import AccExp.
Require Import Exp.
Require Import MExp.
Require Import SymExec2.
Require Import SymExecMRun.

Import ListNotations.
Import MHistNotations.


(* 

  Abstraction to handle doubly-nested loops.

 *)

Section Defs.
  Context {A:Access}.
  Context {I:AccessInst}.
  Notation history := (list access_val).
  Notation Iter x i := (fun n=> FRun (i_subst x (NNum n) i)).  
  Notation BranchMap x i l m := (Map (Iter x i) l m).

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

  (* ----------------------- ITER2D ------------------------------ *)

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

  (* ----------------------- INNER INVERSION --------------------- *)

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

  Let f_run_inv_decl_map_2d_inner_0:
    forall ks x y i n m n1 n2,
    RangeList n1 n2 ks ->
    FRun
      (Decl y (NNum n1, NNum n2) (i_subst x (NNum n) i))
      m ->
    exists vs,
    m == summation vs /\
    Map (Iter2d x y i) (map (pair n) ks) vs.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      apply f_run_inv_decl_nil in H0. {
        exists [].
        simpl.
        split. { assumption. }
        apply map_nil.
      }
      auto using r_pred_eq.
    }
    assert (ND: NoDup (a :: ks)). { 
      apply prop_to_range_list in H.
      rewrite <- H.
      apply range_list_no_dup.
    }
    inversion H; subst; clear H.
    apply f_run_inv_decl_cons in H0; auto.
    destruct H0 as (m1, (m2, (R, (Hf1, Hf2)))).
    apply IHks in Hf2; auto.
    destruct Hf2 as (vs, (R2, Hm)).
    exists (m1::vs).
    simpl.
    repeat match goal with
     H: _ == _ |- _ => rewrite H; clear H
    end.
    split. { reflexivity. }
    apply map_cons; auto.
    intros N.
    apply in_map_iff in N.
    destruct N as (m', (R, Hi)).
    inversion R; subst; clear R.
    inversion ND; auto.
  Qed.

  Lemma f_run_inv_decl_map_2d_inner:
    forall x y i n m,
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i)) m ->
    exists l,
    m == summation l /\
    Map (Iter2d x y i) (range_list_2d_inner n) l.
  Proof.
    intros.
    assert (Hr := range_list_spec 0 n).
    eapply f_run_inv_decl_map_2d_inner_0 in H; eauto.
  Qed.

  Let f_run_inv_decl_map_2d_0:
    forall ks x y i n1 n2 m,
    RangeList n1 n2 ks ->
    x <> y ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i))
      m ->
    exists l,
    EEq m (summation l) /\
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      apply f_run_inv_decl_nil in H1; auto using r_pred_eq.
      exists [].
      simpl.
      auto using map_nil.
    }
    assert (ND: NoDup (a :: ks)) by eauto using range_list_to_no_dup.
    inversion H; subst; clear H.
    apply f_run_inv_decl_cons in H1; auto.
    destruct H1 as (m1, (m2, (R, (Hf1, Hf2)))).
    apply IHks in Hf2; auto.
    destruct Hf2 as (l, (R1, Hm)).
    simpl in Hf1.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
    apply f_run_inv_decl_map_2d_inner in Hf1.
    destruct Hf1 as (l', (R', Hm1)).
    exists (l' ++ l).
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
    assert (Rx: range_list_2d_inner a ++ flat_map range_list_2d_inner ks
      = fl). {
      subst.
      reflexivity.
    }
    rewrite Rx.
    rewrite Heqfl.
    auto using no_dup_flat_map_range_2d_inner, NoDup_cons.
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
    eapply f_run_inv_decl_map_2d_0 in H0; eauto using range_list_spec.
  Qed.

  (* ----------------------- INNER CONSTRUCTION --------------------- *)

  Let f_run_decl_map_2d_inner_0:
    forall ks vs x y i n n1 n2,
    RangeList n1 n2 ks ->
    Map (Iter2d x y i) (map (pair n) ks) vs ->
    FRun
      (Decl y (NNum n1, NNum n2) (i_subst x (NNum n) i))
      (summation vs).
  Proof.
    induction ks; intros;
      inversion H; subst; clear H;
      simpl in *;
      inversion H0; subst; clear H0
    . {
      simpl.
      eapply f_run_decl_nil_eq; eauto using n_step_num.
    }
    eapply IHks in H7; eauto.
    simpl.
    eapply f_run_decl_cons; eauto using n_step_num.
    reflexivity.
  Qed.

  Let f_run_decl_map_2d_inner:
    forall x y i n l,
    Map (Iter2d x y i) (range_list_2d_inner n) l ->
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i)) (summation l).
  Proof.
    intros.
    eapply f_run_decl_map_2d_inner_0; eauto using range_list_spec.
  Qed.

  Let f_run_decl_map_2d_0:
    forall ks n1 n2 x y i l,
    RangeList n1 n2 ks ->
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l ->
    x <> y ->
    x <> y ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i))
       (summation l).
  Proof.
    induction ks; intros. {
      simpl in *.
      inversion H; subst; clear H.
      eapply f_run_decl_nil; eauto using r_pred_eq, n_step_num.
      inversion H0; subst; clear H0.
      reflexivity.
    }
    simpl in *.
    apply map_inv_app in H0.
    destruct H0 as (l1', (l2', (?, (Hm1, Hm2)))).
    subst.
    inversion H; subst; clear H.
    eapply IHks in Hm2; eauto.
    eapply f_run_decl_cons with (m1:=summation l1'); eauto using n_step_num.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      auto using f_run_decl_map_2d_inner.
    - rewrite e_summation_app.
      reflexivity.
  Qed.

  Lemma f_run_decl_map_2d:
    forall x y i n1 n2 l,
    x <> y ->
    Map (Iter2d x y i) (range_list_2d n1 n2) l ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i))
      (summation l).
  Proof.
    intros.
    eapply f_run_decl_map_2d_0; eauto using range_list_spec.
  Qed.

End Defs.