Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Conc.
Require Import SetTh.
Import ListNotations.
Require Import RangeList.
Require Import Tasks.
Require Import SymExec2.
Require LoopFree2.
Require SymHist2.
Require Import SymExecMRun.
Require Import SymExecMap.
Require Import SymExecEq.
Require Import MExp.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.

  Fixpoint proj (c:Conc2.inst) : inst (I:=SymHist2.SymAcc) :=
    match c with
    | Conc2.Skip => Skip
    | Conc2.Seq i j => Seq (proj i) (proj j)
    | Conc2.If b i j => If b (proj i) (proj j)
    | Conc2.MemAcc a => MemAcc (I:=SymHist2.SymAcc) (a, NVar TID)
    | Conc2.For x r i => Decl x r (proj i)
    | Conc2.Loop x l i => Branch x l (proj i)
    end.

  Definition do_proj x i := i_subst TID (NVar x) (proj i).

  Definition translate c : inst :=
    Decl T1 (NNum 1, NNum TID_COUNT)
      (Decl T2 (NNum 0, NVar T1)
        (Seq (do_proj T1 c) (do_proj T2 c))).

  Lemma in_proj_to_in:
    forall x i,
    x <> TID ->
    In x (proj i) ->
    Conc2.In x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0; auto.
    + destruct H1; auto.
    + inversion H1; subst; clear H1.
      contradiction.
    + destruct H1; auto.
  Qed.
(*
  Lemma i_subst_proj_rw_eq:
    forall i n,
    proj (Conc2.i_subst TID (NNum n) i) = i_subst TID (NNum n) (proj i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi1; auto);
      try (rewrite IHi2; auto);
      try (rewrite IHi; auto);
      auto
    .
    - destruct (Set_VAR.MF.eq_dec TID TID). {
        
      }
    - .
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
  Qed.
*)
  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (Conc2.i_subst x (NNum n) i) = i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi; auto.
  Qed.

  Lemma translate_def:
    forall i vs1 vs2,
    Map (Iter2d T1 T2 (i_subst TID (NVar T1) (proj i)))
        (range_list_2d 1 TID_COUNT) vs1 ->
    Map (Iter2d T1 T2 (i_subst TID (NVar T2) (proj i)))
        (range_list_2d 1 TID_COUNT) vs2 ->
    FRun (translate i) (summation (map2 Prod vs1 vs2)).
  Proof.
    intros.
    unfold translate.
    apply f_run_decl_map_2d; auto using t1_neq_t2.
    apply map_iter2d_map2_prod; auto.
  Qed.

  Lemma translate_inv:
    forall i m,
    FRun (translate i) m ->
    exists l,
    EEq m (summation l) /\
    exists vs1 vs2,
    EEqList l (map2 Prod vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d T1 T2 (i_subst TID (NVar T1) (proj i)))
        (range_list_2d 1 TID_COUNT) vs1 /\
    Map (Iter2d T1 T2 (i_subst TID (NVar T2) (proj i)))
        (range_list_2d 1 TID_COUNT) vs2
    .
  Proof.
    unfold translate.
    intros.
    apply f_run_inv_decl_map_2d in H; auto using t1_neq_t2.
    destruct H as (l, (R, Hm)).
    unfold do_proj in Hm.
    apply map_iter_2d_inv_seq in Hm.
    destruct Hm as (vs1, (vs2, (R2, (Hl1, (Hm1, Hm2))))).
    exists l.
    split; auto.
    exists vs1.
    exists vs2.
    auto.
  Qed.

  (* --------------------------- SKIP ---------------------------- *)

  Lemma f_run_decl_skip:
    forall x n1 n2,
    FRun (I:=SymHist2.SymAcc) (Decl x (NNum n1, NNum n2) Skip) (One []).
  Proof.
    intros.
    rewrite p_eq_decl_skip.
    apply f_run_skip_eq.
  Qed.

  Lemma translate_skip:
    FRun (translate Conc2.Skip) (One []).
  Proof.
    unfold translate.
    rewrite p_eq_decl_impl with (j:=Skip); auto using f_run_decl_skip.
    intros.
    simpl.
    remove_eq T1 T1.
    remove_eq T1 T2.
    rewrite p_eq_decl_impl with (j:=Skip); auto.
    - rewrite p_eq_decl_skip.
      reflexivity.
    - intros.
      simpl.
      rewrite p_eq_seq_skip_r.
      reflexivity.
  Qed.

  Lemma iter_2d_inv_skip I:
    forall x y p m,
    Iter2d (I:=I) x y Skip p m ->
    EEq m (One []).
  Proof.
    unfold Iter2d.
    intros x y (nx, ny) m Hm.
    simpl in *.
    inversion Hm; subst; clear Hm.
    assumption.
  Qed.

  Lemma map_iter_2d_inv_seq_skip_skip I:
    forall x y ks vs,
    Map (Iter2d (I:=I) x y (Seq Skip Skip)) ks vs ->
    EEq (summation vs) (One []).
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    simpl.
    rewrite H5; clear H5.
    rewrite e_plus_nil_r.
    apply iter_2d_inv_seq in H2.
    destruct H2 as (m1, (m2, (R, (Hi1, Hi2)))).
    apply iter_2d_inv_skip in Hi1.
    apply iter_2d_inv_skip in Hi2.
    rewrite Hi1 in *.
    rewrite Hi2 in *.
    rewrite e_prod_nil_l in R.
    assumption.
  Qed.

  Lemma translate_inv_skip:
     forall m,
     FRun (translate Conc2.Skip) m ->
     EEq m (One []).
  Proof.
    intros.
    unfold translate in H.
    apply f_run_inv_decl_map_2d in H; auto using t1_neq_t2.
    destruct H as (l, (R, Hm)).
    simpl in *.
    unfold do_proj in *.
    simpl in *.
    rewrite R; clear R.
    apply map_iter_2d_inv_seq_skip_skip in Hm.
    assumption.
  Qed.

  (* -------------------- ACCESS ---------------------------- *)
  
  Definition Access2d x y (e:access_exp * nexp) (p:nat*nat) m :=
    let (nx, ny) := p in
    let (a, e) := e in
      exists v,
      access_step
        (access_subst y (NNum ny)
          (access_subst x (NNum nx) a),
           n_subst y (NNum ny) (n_subst x (NNum nx) e)) v /\
      m = One v.


  Lemma access_2d_to_iter_2d:
    forall x y e a m,
    Access2d x y e a m ->
    Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e) a m.
  Proof.
    unfold Access2d, Iter2d.
    intros.
    destruct a as (nx, ny).
    destruct e as (a, e).
    destruct H as (v, (H,R)).
    subst.
    simpl.
    eapply f_run_access; eauto.
    reflexivity.
  Qed.

  Lemma iter_2d_inv_access:
    forall x y e p m,
    Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e) p m ->
    exists m', EEq m m' /\ Access2d x y e p m'.
  Proof.
    intros.
    unfold Iter2d in H.
    destruct p as (nx, ny).
    destruct e as (a, e).
    simpl in H.
    inversion H; subst; clear H.
    unfold Iter2d, Access2d.
    simpl in *.
    eauto.
  Qed.

  Lemma map_iter_2d_inv_acc:
    forall x y e ks vs,
    Map (Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e)) ks vs ->
    exists vs',
    EEqList vs vs' /\
    length vs = length vs' /\
    Map (Access2d x y e) ks vs'.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      exists [].
      split. { reflexivity. }
      split. { reflexivity. }
      apply map_nil.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    destruct H5 as (vs1, (R1, (Hl1, Hm2))).
    apply iter_2d_inv_access in H2.
    destruct H2 as (m1, (R2, Hacc)).
    exists (m1::vs1).
    split. {
      rewrite R2.
      rewrite R1.
      reflexivity.
    }
    simpl.
    rewrite Hl1.
    auto using map_cons.
  Qed.

  Lemma map_iter_2d_access_skip:
    forall x y e ks vs,
    Map (Access2d x y e) ks vs ->
    Map (Iter2d x y (MemAcc (I:=SymHist2.SymAcc) e)) ks vs.
  Proof.
    eauto using map_impl, access_2d_to_iter_2d.
  Qed.

  Lemma translate_access:
    forall e vs1 vs2,
    Map (Access2d T1 T2 (access_subst TID (NVar T1) e, NVar T1))
          (range_list_2d 1 TID_COUNT) vs1 ->
    Map (Access2d T1 T2 (access_subst TID (NVar T2) e, NVar T2))
          (range_list_2d 1 TID_COUNT) vs2 ->
    FRun (translate (Conc2.MemAcc e)) (summation (map2 Prod vs1 vs2)).
  Proof.
    intros.
    unfold translate.
    unfold do_proj.
    apply f_run_decl_map_2d; auto using t1_neq_t2.
    apply map_iter2d_map2_prod.
    + simpl.
      remove_eq TID TID.
      apply map_iter_2d_access_skip; simpl in *.
      remove_eq TID TID.
      assumption.
    + apply map_iter_2d_access_skip.
      simpl in *.
      remove_eq TID TID.
      assumption.
  Qed.


  (* --------------------------- SEQ ------------------------ *)

  Lemma iter_2d_inv_seq I:
    forall x y i j m p,
    Iter2d (I:=I) x y (Seq i j) p m ->
    exists m1 m2,
    EEq m (Prod m1 m2) /\
    Iter2d x y i p m1 /\
    Iter2d x y j p m2.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in H.
    inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma map_iter_2d_inv_fork I:
    forall x y ks vs i j,
    Map (Iter2d (I:=I) x y (Seq i j)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Prod vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d x y i) ks vs1 /\
    Map (Iter2d x y j) ks vs2.
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      exists [], [].
      auto using map_nil, e_eq_list_nil.
    }
    inversion H; subst; clear H.
    edestruct IHks as (vs1, (vs2, (Rl, (Hl, (Hm1, Hm2))))); eauto.
    edestruct iter_2d_inv_seq as (ma, (mb, (R2, (Hr1, Hr2)))); eauto.
    exists (ma :: vs1), (mb :: vs2).
    rewrite Rl.
    rewrite R2.
    simpl.
    rewrite Hl.
    rewrite map2_cons_rw.
    split. { reflexivity. }
    split. { reflexivity. }
    split; auto using map_cons.
  Qed.

  Lemma translate_inv_seq i j m:
    FRun (translate (Conc2.Seq i j)) m ->
    exists vs1_1 vs2_1 vs1_2 vs2_2,
    EEq m (summation (map2 Prod (map2 Prod vs1_1 vs2_1) (map2 Prod vs1_2 vs2_2))) /\
    length vs1_1 = length vs2_1 /\
    length vs2_1 = length vs1_2 /\
    length vs1_2 = length vs2_2 /\
    FRun (translate i) (summation (map2 Prod vs1_1 vs1_2)) /\
    FRun (translate j) (summation (map2 Prod vs2_1 vs2_2)).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (lm, (R1, (vs1, (vs2, (R2, (Hl, (Hm1, Hm2))))))).
    simpl in *.
    apply map_iter_2d_inv_seq in Hm1.
    destruct Hm1 as (vs1_1, (vs2_1, (R_1, (Hl1, (Hm1_1, Hm2_1))))).
    apply map_iter_2d_inv_seq in Hm2.
    destruct Hm2 as (vs1_2, (vs2_2, (R_2, (Hl2, (Hm1_2, Hm2_2))))).
    eexists.
    eexists.
    eexists.
    eexists.
    split.
    2: {
      split. 2: {
        split. 2: {
          split. 2: {
            split.
            - eapply translate_def; eauto.
            - eapply translate_def; eauto.
          }
          auto.
        }
        apply e_eq_list_inv_length_r in R_1; auto.
        apply e_eq_list_inv_length_r in R_2; auto.
        auto with *.
      }
      auto.
    }
    rewrite R1.
    rewrite R2.
    rewrite R_1.
    rewrite R_2.
    reflexivity.
  Qed.

  (* ------------------------ LOOP NIL ------------------ *)

  Lemma iter_2d_inv_branch_nil I:
    forall x y z i m p,
    Iter2d (I:=I) x y (Branch z [] i) p m ->
    EEq m (One []).
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in *.
    remove_eq y z;
      remove_eq x z;
        rewrite p_eq_branch_nil in H;
        inversion H; subst; clear H;
        assumption.
  Qed.

  Lemma map_iter_2d_inv_branch_nil I:
    forall x y ks vs i z,
    Map (Iter2d (I:=I) x y (Branch z [] i)) ks vs ->
    EEq (summation vs) (One []).
  Proof.
    induction ks; intros; inversion H; subst; clear H. {
      reflexivity.
    }
    apply IHks in H5.
    simpl.
    rewrite H5.
    apply iter_2d_inv_branch_nil in H2.
    rewrite H2.
    simpl.
    rewrite e_plus_nil_l.
    reflexivity.
  Qed.

  Lemma translate_inv_loop_nil:
    forall z i m,
    FRun (translate (Conc2.Loop z [] i)) m ->
    EEq m (One []).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (l, (R, (vs1, (vs2, (R2, (Hl, (Hm1, Hm2))))))).
    simpl in *.
    apply map_iter_2d_inv_branch_nil in Hm1.
    apply map_iter_2d_inv_branch_nil in Hm2.
    rewrite R; clear R m.
    rewrite R2; clear R2 l.
    generalize dependent vs2.
    generalize dependent vs1.
    induction vs1; intros. {
      destruct vs2; inversion Hl.
      simpl.
      reflexivity.
    }
    destruct vs2; inversion Hl; clear Hl.
    rewrite map2_cons_rw.
    simpl.
    simpl in Hm1, Hm2.
    apply e_plus_inv_nil in Hm1.
    apply e_plus_inv_nil in Hm2.
    destruct Hm1 as (R1, R2).
    destruct Hm2 as (R3, R4).
    rewrite R1; clear R1.
    rewrite R3; clear R3.
    rewrite e_prod_nil_l.
    rewrite e_plus_nil_l.
    apply IHvs1; auto.
  Qed.

  (* ------------------------ LOOP-CONS ------------------- *)


  Lemma iter_2d_inv_branch_cons I:
    forall x y z i m p l n,
    Iter2d (I:=I) x y (Branch z (n::l) i) p m ->
    x <> y ->
    x <> z ->
    y <> z ->
    exists m1 m2,
    EEq m (Plus m1 m2) /\ 
    Iter2d x y (i_subst z (NNum n) i) p m1 /\
    Iter2d x y (Branch z l i) p m2
    .
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in H.
    inversion H; subst; clear H.
    exists m1, m2.
    remove_eq y z.
    remove_eq x z.
    remove_eq y z.
    rewrite (i_subst_subst_neq z y) in H8; auto.
    rewrite (i_subst_subst_neq z x) in H8; auto.
  Qed.

  Lemma map_iter_2d_inv_branch_cons I z i n l x y
    (Hn1: x <> y)
    (Hn2: x <> z)
    (Hn3: y <> z)
    :
    forall ks vs,
    Map (Iter2d (I:=I) x y (Branch z (n::l) i)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Plus vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d x y (i_subst z (NNum n) i)) ks vs1 /\
    Map (Iter2d x y (Branch z l i)) ks vs2
    .
  Proof.
    induction ks; intros. {
      inversion H.
      subst.
      exists [], [].
      split. { reflexivity. }
      auto using map_nil.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    destruct H5 as (vs1, (vs2, (R1, (R2, (Ha, Hb))))).
    apply iter_2d_inv_branch_cons in H2; auto.
    destruct H2 as (m1, (m2, (R3, (Hi1, Hi2)))).
    exists (m1::vs1), (m2::vs2).
    rewrite map2_cons_rw.
    split. {
      rewrite R1 in *.
      rewrite R3.
      reflexivity.
    }
    split. { simpl. rewrite R2; auto. }
    auto using map_cons.
  Qed.

  Lemma translate_inv_loop_cons z i m n l
    (t1_nin: ~ Conc2.Var T1 (Conc2.Loop z (n::l) i))
    (t2_nin: ~ Conc2.Var T2 (Conc2.Loop z (n::l) i))
    (tid_nin: TID <> z)
  :
    FRun (translate (Conc2.Loop z (n::l) i)) m ->
    exists vs1 vs2 vs3 vs4,
    EEq m (summation (map2 Prod (map2 Plus vs1 vs3) (map2 Plus vs2 vs4))) /\
    length vs1 = length vs2 /\
    length vs2 = length vs3 /\
    length vs3 = length vs4 /\
    FRun (translate (Conc2.i_subst z (NNum n) i)) (summation (map2 Prod vs1 vs2)) /\
    FRun (translate (Conc2.Loop z l i)) (summation (map2 Prod vs3 vs4)).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (lm, (R1, (vs1, (vs2, (R2, (Hl, (Hm1, Hm2))))))).
    simpl in *.
    apply map_iter_2d_inv_branch_cons in Hm1; auto using t1_neq_t2.
    apply map_iter_2d_inv_branch_cons in Hm2; auto using t1_neq_t2.
    destruct Hm1 as (vsi_m1, (vsl_m1, (Rl_m1, (Hl_m1, (Hm1_m1, Hm2_m1))))).
    destruct Hm2 as (vsi_m2, (vsl_m2, (Rl_m2, (Hl_m2, (Hm1_m2, Hm2_m2))))).
    remove_eq TID z.
    exists vsi_m1, vsi_m2, vsl_m1, vsl_m2.
    split. {
      rewrite R1; clear R1 m.
      rewrite R2; clear R2 lm.
      rewrite Rl_m1 in *; clear Rl_m1.
      rewrite Rl_m2 in *; clear Rl_m2.
      reflexivity.
    }
    assert (length vs1 = length vsi_m1) by eauto using e_eq_list_inv_length_l.
    assert (length vs1 = length vsl_m1) by eauto using e_eq_list_inv_length_r.
    assert (length vs2 = length vsi_m2) by eauto using e_eq_list_inv_length_l.
    assert (length vs2 = length vsl_m2) by eauto using e_eq_list_inv_length_r.
    split. { auto with *. }
    split. { auto with *. }
    split. { auto with *. }
    split.
    - (* i [ z := n ] *)
      apply translate_def.
      + rewrite i_subst_proj_rw in *; auto.
        assert (T1 <> z) by auto.
        rewrite i_subst_subst_neq_2; auto.
      + rewrite i_subst_proj_rw in *; auto.
        assert (T2 <> z) by auto.
        rewrite i_subst_subst_neq_2; auto.
    - (* Loop z l i  *) 
      apply translate_def.
      + simpl.
        remove_eq TID z.
        auto.
      + simpl.
        remove_eq TID z.
        auto.
  Qed.

  (* ------------------------ FOR -------------------------- *)

  (* ------------------------ IF -------------------------- *)


End Defs.
