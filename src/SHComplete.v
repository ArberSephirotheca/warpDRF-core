Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
Require Import Recdef.
Require Import Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Access.
Require Import Util.
Require LoopFree.
Require Import SetTh.
Import ListNotations.
Require Import Tasks.
Require Import SymHist.
Require Import MExp.
Require Import SymHistMExp.
Require LoopFreeMExp.
Require Import RangeList.
Require Import SHCompiler.
Require Import MultiHist.
Require InUtil.
Import MHistNotations.
Require Conc.
Section Compiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).
  Definition mk_empty_1 n1 n2 : list history :=
    List.concat (map (fun _ => [[]]) (range_list n1 n2)) ++ [[]].

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
    Iter2d x y (seq i j) p m ->
    exists m1 m2,
    m == m1 * m2 /\
    Iter2d x y i p m1 /\
    Iter2d x y j p m2.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    rewrite i_subst_seq in H.
    rewrite i_subst_seq in H.
    apply f_run_inv_seq in H.
    destruct H as (m1, (m2, (r1, (r2, r3)))).
    exists m1, m2.
    split; auto.
  Qed.

  Lemma iter_2d_seq:
    forall x y i j p m1 m2 m3,
    Iter2d x y i p m1 ->
    Iter2d x y j p m2 ->
    m3 == m1 * m2 ->
    Iter2d x y (seq i j) p m3.
  Proof.
    intros.
    unfold Iter2d in *.
    destruct p as (nx, ny).
    rewrite i_subst_seq.
    rewrite i_subst_seq.
    eapply f_run_seq; eauto.
  Qed.

  Lemma iter_2d_seq_eq:
    forall x y i j p m1 m2,
    Iter2d x y i p m1 ->
    Iter2d x y j p m2 ->
    Iter2d x y (seq i j) p (m1 * m2).
  Proof.
    intros.
    eapply iter_2d_seq; eauto.
    reflexivity.
  Qed.

  Lemma map_iter_2d_inv_seq:
    forall ks vs i j x y,
    Map (Iter2d x y (seq i j)) ks vs ->
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
    Map (Iter2d x y (seq i j)) ks (map2 Prod vs1 vs2).
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

  Lemma i_subst_inv_nil:
    forall x v i,
    SymHist.i_subst x v i = SymHist.Skip ->
    i = SymHist.Skip.
  Proof.
    intros.
    destruct i; simpl in *.
    - reflexivity.
    - destruct p.
      inversion H.
    - inversion H.
    - inversion H.
  Qed.

  (* --------------------------- ACCESS ----------------------------- *)


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
    Iter2d x y (Acc e Skip) a m.
  Proof.
    unfold Access2d, Iter2d.
    intros.
    destruct a as (nx, ny).
    destruct e as (a, e).
    destruct H as (v, (H,R)).
    subst.
    simpl.
    eapply f_run_access; eauto using f_run_skip_eq.
    rewrite e_prod_nil_r.
    reflexivity. 
  Qed.

  Lemma iter_2d_inv_access:
    forall x y e i p m,
    Iter2d x y (Acc e i) p m ->
    exists m1 m2,
    m == m1 * m2 /\
    Access2d x y e p m1 /\
    Iter2d x y i p m2.
  Proof.
    intros.
    unfold Iter2d in H.
    destruct p as (nx, ny).
    destruct e as (a, e).
    simpl in H.
    apply f_run_inv_access in H.
    destruct H as (v', (m', (Rv, (Ha, Hc)))).
    exists (One v'), m'.
    unfold Iter2d, Access2d.
    eauto.
  Qed.

  Lemma f_run_inv_access:
    forall i e m,
    FRun (Acc e i) m ->
    exists v m',
    m == One v * m' /\
    access_step e v /\
    FRun i m'.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists v, hs.
    auto using f_run_eq.
  Qed.

  Lemma map_iter_2d_inv_acc:
    forall x y e i ks vs,
    Map (Iter2d x y (Acc e i)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Prod vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Access2d x y e) ks vs1 /\
    Map (Iter2d x y i) ks vs2.
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
    destruct H5 as (vs1, (vs2, (R1, (Hl1, (Hm1, Hm2))))).
    apply iter_2d_inv_access in H2.
    destruct H2 as (m1, (m2, (R2, (Hacc, Hi)))).
    exists (m1::vs1), (m2::vs2).
    split. {
      rewrite R2.
      rewrite R1.
      rewrite map2_cons_rw.
      reflexivity.
    }
    simpl.
    auto using map_cons.
  Qed.

  Lemma map_iter_2d_access_skip:
    forall x y e ks vs,
    Map (Access2d x y e) ks vs ->
    Map (Iter2d x y (Acc e Skip)) ks vs.
  Proof.
    eauto using map_impl, access_2d_to_iter_2d.
  Qed.
  
  Lemma translate_access_skip:
    forall e vs1 vs2,
    Map (Access2d T1 T2 (access_subst TID (NVar T1) e, NVar T1))
          (range_list_2d 1 TID_COUNT) vs1 ->
    Map (Access2d T1 T2 (access_subst TID (NVar T2) e, NVar T2))
          (range_list_2d 1 TID_COUNT) vs2 ->
    FRun (translate (Conc.Acc e Conc.Skip)) (Σ (map2 Prod vs1 vs2)).
  Proof.
    intros.
    unfold translate.
    unfold do_proj.
    apply f_run_decl_map_2d; auto using t1_neq_t2.
    apply map_iter2d_map2_prod.
    + simpl.
      remove_eq TID TID.
      auto using map_iter_2d_access_skip.
    + simpl.
      remove_eq TID TID.
      auto using map_iter_2d_access_skip.
  Qed.

  Lemma translate_inv_access:
    forall e m i,
    FRun (translate (Conc.Acc e i)) m ->
    exists vs1 vs2 vs3 vs4,
    m == summation (map2 Prod (map2 Prod vs1 vs3) (map2 Prod vs2 vs4)) /\
    length vs1 = length vs2 /\
    length vs2 = length vs3 /\
    length vs3 = length vs4 /\
    FRun (translate (Conc.Acc e Conc.Skip)) (summation (map2 Prod vs1 vs2)) /\
    FRun (translate i) (summation (map2 Prod vs3 vs4)).
  Proof.
    intros e m i Hr.
    unfold translate in Hr.
    apply f_run_inv_decl_map_2d in Hr; auto using t1_neq_t2.
    destruct Hr as (r, (R1, Hm)).
    unfold do_proj in Hm.
    apply map_iter_2d_inv_seq in Hm.
    destruct Hm as (vs1, (vs2, (R2, (Hl1, (Hm1, Hm2))))).
    simpl in Hm1, Hm2.
    remove_eq TID TID.
    apply map_iter_2d_inv_acc in Hm1.
    destruct Hm1 as (vs3, (vs4, (R3, (Hl2, (Hm3, Hm4))))).
    apply map_iter_2d_inv_acc in Hm2.
    destruct Hm2 as (vs5, (vs6, (R4, (Hl3, (Hm5, Hm6))))).
    exists vs3, vs5, vs4, vs6.
    split. {
      rewrite R1.
      rewrite R2.
      rewrite R3.
      rewrite R4.
      reflexivity.
    }
    (* Handle vector lengths *)
    assert (length vs3 = length vs1) by (symmetry; eauto using e_eq_list_inv_length_l).
    assert (length vs2 = length vs5) by eauto using e_eq_list_inv_length_l.
    assert (length vs1 = length vs5) by (transitivity (length vs2); auto).
    assert (length vs1 = length vs4) by eauto using e_eq_list_inv_length_r.
    split. { transitivity (length vs1); auto. }
    split. { transitivity (length vs1); auto. }
    split. {
      transitivity (length vs1); auto.
      transitivity (length vs2); eauto using e_eq_list_inv_length_r.
    }
    (* Handle FRun *)
    split. { auto using translate_access_skip. }
    auto using translate_def.
  Qed.

  Lemma translate_inv_in_access e (t1_nin: ~ Conc.In T1 (Conc.Acc e Conc.Skip)) (t2_nin: ~ Conc.In T2 (Conc.Acc e Conc.Skip)):
    forall m,
    FRun (translate (Conc.Acc e Conc.Skip)) m ->
    forall x,
    EIn x m ->
    exists nx ny,
    1 <= nx < TID_COUNT /\ 0 <= ny < nx
    /\ exists vx vy,
    access_step (access_subst TID (NNum nx) e, NNum nx) vx /\
    access_step (access_subst TID (NNum ny) e, NNum ny) vy /\
    (List.In x vx \/ List.In x vy).
  Proof.
    intros.
    unfold translate in H.
    apply f_run_inv_decl_map_2d in H; auto using t1_neq_t2.
    destruct H as (l, (R, Hr)).
    unfold do_proj in *.
    simpl in *.
    remove_eq TID TID.
    rewrite R in *.
    apply e_in_inv_summation in H0.
    destruct H0 as (m', (Hi, He)).
    eapply map_inv_value in Hr; eauto.
    destruct Hr as ((nx, ny), (Hj, Hr)).
    apply range_list_2d_inv_in in Hj.
    destruct Hj as (Ha, Hb).
    exists nx.
    exists ny.
    split; auto.
    split; auto.
    unfold Iter2d in Hr.
    simpl in *.
    remove_eq T1 T1.
    remove_eq T1 T2.
    remove_eq T2 T2.
    apply f_run_inv_access in Hr.
    destruct Hr as (v1, (m'', (Hs1, (Hs2, Hf)))).
    rewrite Hs1 in *; clear Hs1.
    simpl in He.
    apply f_run_inv_access in Hf.
    destruct Hf as (v2, (m2, (Hx, (Hy, Hz)))).
    rewrite Hx in *; clear Hx.
    apply f_run_inv_skip in Hz.
    rewrite Hz in *; clear Hz.
    simpl in *.
    exists v1; exists v2.
    split. {
      rewrite access_subst_subst_trans in Hs2. {
        rewrite access_subst_not_in in Hs2; auto.
        intros N.
        contradict t2_nin.
        apply Conc.in_acc_1.
        apply access_in_subst_neq in N; auto using t2_neq_tid.
        intros M.
        inversion M.
      }
      intros N.
      contradict t1_nin.
      auto using Conc.in_acc_1.
    }
    split. {
      rewrite (access_subst_not_in T1) in Hy. {
        rewrite access_subst_subst_trans in Hy; auto.
        intros N.
        contradict t2_nin.
        auto using Conc.in_acc_1.
      }
      intros N.
      contradict t1_nin.
      apply access_in_subst_neq in N; auto using t1_neq_tid, Conc.in_acc_1.
      intros M.
      inversion M.
      apply t1_neq_t2 in H0.
      assumption.
    }
    intuition.
  Qed.

  Lemma translate_inv:
    forall i m,
    FRun (translate i) m ->
    exists l,
    m == summation l /\
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
    FRun (Decl x (NNum n1, NNum n2) Skip Skip) (One []).
  Proof.
    intros.
    rewrite prog_equiv_decl_skip.
    apply f_run_skip_eq.
  Qed.

  Lemma translate_skip:
    FRun (translate Conc.Skip) (One []).
  Proof.
    unfold translate.
    simpl.
    rewrite f_run_decl_impl_rw with (j:=Skip); auto using f_run_decl_skip.
    intros.
    simpl.
    remove_eq T1 T1.
    remove_eq T1 T2.
    rewrite prog_equiv_decl_skip.
    reflexivity.
  Qed.

  Lemma iter_2d_inv_skip:
    forall x y p m,
    Iter2d x y Skip p m ->
    m == One [].
  Proof.
    unfold Iter2d.
    intros x y (nx, ny) m (m', (R, H)).
    rewrite R.
    simpl in *.
    inversion H; subst; clear H.
    reflexivity.
  Qed.

  Lemma map_iter_2d_inv_skip:
    forall x y ks vs,
    Map (Iter2d x y Skip) ks vs ->
    summation vs == One [].
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    apply IHks in H5.
    simpl.
    rewrite H5.
    apply iter_2d_inv_skip in H2.
    rewrite H2.
    rewrite e_plus_nil_l.
    reflexivity.
  Qed.

  Lemma translate_inv_skip:
     forall m,
     FRun (translate Conc.Skip) m ->
     m == One [].
  Proof.
    intros.
    unfold translate in H.
    apply f_run_inv_decl_map_2d in H; auto using t1_neq_t2.
    destruct H as (l, (R, Hm)).
    simpl in *.
    unfold do_proj in *.
    simpl in *.
    rewrite R; clear R.
    apply map_iter_2d_inv_skip in Hm.
    assumption.
  Qed.

  (* --------------------------- LOOP-NIL -------------------- *)

  Lemma iter_2d_inv_branch_nil:
    forall x y z i j m p,
    Iter2d x y (Branch z [] i j) p m ->
    Iter2d x y j p m.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in *.
    remove_eq y z. {
      remove_eq x z. {
        apply f_run_inv_branch_nil in H.
        assumption.
      }
      apply f_run_inv_branch_nil in H.
      assumption.
    }
    apply f_run_inv_branch_nil in H.
    assumption.
  Qed.

  Lemma map_iter_2d_inv_branch_nil:
    forall x y ks vs i j z,
    Map (Iter2d x y (Branch z [] i j)) ks vs ->
    Map (Iter2d x y j) ks vs.
  Proof.
    intros.
    apply map_impl with (P:=Iter2d x y (Branch z [] i j));
    eauto using iter_2d_inv_branch_nil.
  Qed.

  Lemma translate_inv_loop_nil:
    forall z i j m,
    FRun (translate (Conc.Loop z [] i j)) m ->
    FRun (translate j) m.
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (l, (R1, (vs1, (vs2, (R2, (Hl, (Hm1, Hm2))))))).
    simpl in *.
    remove_eq TID z;
      apply map_iter_2d_inv_branch_nil in Hm1;
      apply map_iter_2d_inv_branch_nil in Hm2;
      rewrite R1;
      rewrite R2;
      apply translate_def; auto.
  Qed.

  (* --------------------------- LOOP-CONS -------------------- *)

  Lemma iter_2d_inv_branch_cons:
    forall x y z i j m p l n,
    Iter2d x y (Branch z (n::l) i j) p m ->
    x <> y ->
    x <> z ->
    y <> z ->
    exists m1 m2,
    m == m1 + m2 /\ 
    Iter2d x y (seq (i_subst z (NNum n) i) j) p m1 /\
    Iter2d x y (Branch z l i j) p m2
    .
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in H.
    apply f_run_inv_branch_cons in H.
    destruct H as (m1, (m2, (R, (Hf1, Hf2)))).
    exists m1, m2.
    split; auto; clear R.
    rewrite i_subst_seq.
    rewrite i_subst_seq.
    simpl.
    remove_eq y z.
    remove_eq x z.
    split; auto.
    assert (R:
      i_subst y (NNum ny) (i_subst x (NNum nx) (i_subst z (NNum n) i))
      =
      i_subst z (NNum n) (i_subst y (NNum ny) (i_subst x (NNum nx) i))
    ). {
      rewrite (i_subst_subst_neq z y); auto.
      rewrite (i_subst_subst_neq z x); auto.
    }
    rewrite R.
    assumption.
  Qed.


  Lemma map_iter_2d_inv_branch_cons z i j n l x y
    (Hn1: x <> y)
    (Hn2: x <> z)
    (Hn3: y <> z)
    :
    forall ks vs,
    Map (Iter2d x y (Branch z (n::l) i j)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Plus vs1 vs2) /\
    length vs1 = length vs2 /\
    Map (Iter2d x y (seq (i_subst z (NNum n) i) j)) ks vs1 /\
    Map (Iter2d x y (Branch z l i j)) ks vs2
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

  Lemma translate_inv_loop_cons z i j m n l
  (tid_nin: ~ Conc.Var TID (Conc.Loop z (n::l) i j))
  (t1_nin: ~ Conc.In T1 (Conc.Loop z (n::l) i j))
  (t2_nin: ~ Conc.In T2 (Conc.Loop z (n::l) i j))
  :
    FRun (translate (Conc.Loop z (n::l) i j)) m ->
    exists vs1 vs2 vs3 vs4,
    m == summation (map2 Prod (map2 Plus vs1 vs3) (map2 Plus vs2 vs4)) /\
    length vs1 = length vs2 /\
    length vs2 = length vs3 /\
    length vs3 = length vs4 /\
    FRun (translate (Conc.seq (Conc.i_subst z (NNum n) i) j)) (summation (map2 Prod vs1 vs2)) /\
    FRun (translate (Conc.Loop z l i j)) (summation (map2 Prod vs3 vs4)).
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (lm, (R1, (vs1, (vs2, (R2, (Hl, (Hm1, Hm2))))))).
    simpl in *.
    assert (TID <> z). {
      intros N.
      subst.
      contradict tid_nin.
      auto using Conc.var_loop_1.
    }
    assert (T1 <> z). {
      intros N.
      subst.
      contradict t1_nin.
      auto using Conc.in_loop_1.
    }
    assert (T2 <> z). {
      intros N.
      subst.
      contradict t2_nin.
      auto using Conc.in_loop_1.
    }
    remove_eq TID z.
    apply map_iter_2d_inv_branch_cons in Hm1; auto using t1_neq_t2.
    apply map_iter_2d_inv_branch_cons in Hm2; auto using t1_neq_t2.
    destruct Hm1 as (vs3, (vs4, (Rl1, (Hl1, (Hma, Hmb))))).
    destruct Hm2 as (vs5, (vs6, (Rl2, (Hl2, (Hmc, Hmd))))).
    rewrite Rl1 in *.
    rewrite Rl2 in *.
    exists vs3, vs5, vs4, vs6.
    split. {
      rewrite R1; clear R1.
      rewrite R2; clear R2.
      reflexivity. 
    }
    assert (Hx1: length vs3 = length vs1)
      by (symmetry; eauto using e_eq_list_inv_length_l).
    assert (Hx2: length vs1 = length vs5). {
      transitivity (length vs2); eauto using e_eq_list_inv_length_l.
    }
    assert (Hx3: length vs1 = length vs4) by  eauto using e_eq_list_inv_length_r.
    assert (Hx4: length vs1 = length vs6). {
      rewrite <- Hl2.
      auto.
    }
    split. {
      transitivity (length vs1); auto.
    }
    split. {
      transitivity (length vs1); auto. 
    }
    split. {
      transitivity (length vs1); auto.
    }
    split. {
      apply translate_def; simpl.
      - rewrite proj_seq.
        rewrite i_subst_seq.
        rewrite i_subst_proj_rw; auto.
        rewrite <- (i_subst_subst_neq_2) in Hma; auto. 
      - rewrite proj_seq.
        rewrite i_subst_seq.
        rewrite i_subst_proj_rw; auto.
        rewrite <- (i_subst_subst_neq_2) in Hmc; auto. 
    }
    apply translate_def; simpl; remove_eq TID z; auto.
  Qed.

  (* ----------------------------- FOR ------------------------------- *)

  Lemma iter_2d_inv_decl:
    forall x y z i j m p r,
    ~ RIn x r ->
    ~ RIn y r ->
    Iter2d x y (Decl z r i j) p m ->
    exists l,
    RStep r l /\ Iter2d x y (Branch z l i j) p m.
  Proof.
    unfold Iter2d.
    intros.
    destruct p as (nx, ny).
    simpl in *.
    apply f_run_inv_decl in H1.
    destruct H1 as (l, (Hr, Hf)).
    exists l.
    split; auto.
    rewrite r_subst_not_in in Hr.
    - rewrite r_subst_not_in in Hr; auto.
    - rewrite r_subst_not_in; auto.
  Qed.

  Lemma map_iter_2d_inv_decl:
    forall x y ks vs i j z r,
    ks <> [] ->
    ~ RIn x r ->
    ~ RIn y r ->
    Map (Iter2d x y (Decl z r i j)) ks vs ->
    exists l, RStep r l /\ Map (Iter2d x y (Branch z l i j)) ks vs.
  Proof.
    intros.
    assert (Hr: exists l, RStep r l). {
      inversion H2; subst; clear H2. { contradiction. }
      apply iter_2d_inv_decl in H3; auto.
      destruct H3 as (l, (Hr, Hk)).
      eauto.
    }
    destruct Hr as (l, Hr).
    exists l.
    split; auto.
    apply map_impl with (P:=Iter2d x y (Decl z r i j)); auto.
    intros k v Hi.
    apply iter_2d_inv_decl in Hi; auto.
    destruct Hi as (l', (Hr', Hi)).
    assert (l' = l) by eauto using r_step_fun.
    subst.
    assumption.
  Qed.

  Lemma translate_inv_for x r i j
    (Hv: ~ Conc.InRange TID (Conc.For x r i j))
    (t1_nin: ~ Conc.In T1 (Conc.For x r i j))
    (t2_nin: ~ Conc.In T2 (Conc.For x r i j))
    :
    forall m,
    FRun (translate (Conc.For x r i j)) m ->
    exists l, RStep r l /\ FRun (translate (Conc.Loop x l i j)) m.
  Proof.
    intros.
    apply translate_inv in H.
    destruct H as (ml, (R, (vs1, (vs2, (Rl, (Hl, (Hm1, Hm2))))))).
    simpl in Hm1.
    assert (~ RIn T1 (r_subst TID (NVar T1) r)). {
      intros N.
      apply r_in_subst_eq in N.
      - contradict Hv.
        auto using Conc.in_range_for_eq.
      - intros M.
        contradict t1_nin.
        auto using Conc.in_for_1.
    }
    assert (~ RIn T2 (r_subst TID (NVar T1) r)). {
      intros N.
      rewrite r_subst_not_in in N.
      - contradict t2_nin.
        auto using Conc.in_for_1.
      - intros M.
        contradict Hv.
        auto using Conc.in_range_for_eq.
    }
    assert (range_list_2d 1 TID_COUNT <> []). {
      intros N.
      unfold range_list_2d in *.
      unfold range_list in N.
      destruct TID_COUNT eqn:Hn. {
        assert (Hx := tid_count_1_lt).
        rewrite Hn in Hx.
        inversion Hx.
      }
      simpl in N.
      destruct n. {
        simpl in N.
        assert (Hx := tid_count_1_lt).
        rewrite Hn in Hx.
        auto with *.
      }
      simpl in N.
      inversion N.
    }
    apply map_iter_2d_inv_decl in Hm1; auto.
    destruct Hm1 as (l, (Hr1, Hm1)).
    simpl in Hm2.
    assert (~ RIn T1 (r_subst TID (NVar T2) r)). {
      intros N.
      rewrite r_subst_not_in in N.
      - contradict t1_nin.
        auto using Conc.in_for_1.
      - intros M.
        contradict Hv.
        auto using Conc.in_range_for_eq.
    }
    assert (~ RIn T2 (r_subst TID (NVar T2) r)). {
      intros N.
      apply r_in_subst_eq in N.
      - contradict Hv.
        auto using Conc.in_range_for_eq.
      - intros M.
        contradict t2_nin.
        auto using Conc.in_for_1.
    }
    apply map_iter_2d_inv_decl in Hm2; auto.
    destruct Hm2 as (l', (Hr2, Hm2)).
    assert (~ RIn TID r). {
      intros N.
      contradict Hv.
      auto using Conc.in_range_for_eq.
    }
    rewrite r_subst_not_in in Hr1; auto.
    rewrite r_subst_not_in in Hr2; auto.
    assert (l' = l) by eauto using r_step_fun; subst.
    exists l.
    split; auto.
    rewrite R.
    rewrite Rl.
    apply translate_def; auto.
  Qed.

  Lemma completeness_1
      (i:Conc.inst)
      (T1_nin_i: ~ Conc.In T1 i)
      (T2_nin_i: ~ Conc.In T2 i)
      (tid_nin: ~ Conc.Var TID i)
      (tid_rin: ~ Conc.InRange TID i)
    :
    forall m_l,
    LoopFreeMExp.FRun i m_l ->
    forall m_h,
    SymHistMExp.FRun (translate i) m_h ->
    forall x,
    EIn x m_h ->
    EIn x m_l.
  Proof.
    intros m_l (m_l', (R_h_l, H)).
    generalize dependent m_l.
    induction H; intros; rewrite R_h_l; clear R_h_l.
    - apply translate_inv_skip in H.
      rewrite H in H0.
      assumption.
    - apply translate_inv_access in H1.
      destruct H1 as (vs1, (vs2, (vs3, (vs4, (R, (Hl1, (Hl2, (Hl3, (Hr1, Hr2))))))))).
      rename H2 into Hx.
      rewrite R in Hx; clear R.
      apply e_in_summation_map2_prod_or in Hx.
      assert (X:
        EIn x (summation (map2 Prod vs1 vs2)) \/
        EIn x (summation (map2 Prod vs3 vs4))
      ). {
        destruct Hx as [Ha|Ha];
            apply e_in_summation_map2_prod_or in Ha;
            destruct Ha as [Ha|Ha].
        - left.
          apply e_in_rw_summation_map2_prod; auto.
        - right.
          apply e_in_rw_summation_map2_prod; auto.
        - left.
          apply e_in_rw_summation_map2_prod; auto.
        - right.
          apply e_in_rw_summation_map2_prod; auto.
      }
      clear Hx.
      simpl.
      destruct X as [Hx|Hx]. {
        (* must be in the access *)
        left.
        eapply translate_inv_in_access in Hr1; eauto; clear Hx.
        - destruct Hr1 as (nx, (ny, (Hle1, (Hle2, (vx, (vy, (Hs1, (Hs2, [])))))))).
          + eapply Hist.gen_access_to_in in Hs1; eauto with *.
            apply InUtil.m_in_to_in_concat.
            eauto using InUtil.m_in_def.
          + eapply Hist.gen_access_to_in in Hs2; eauto with *.
            apply InUtil.m_in_to_in_concat.
            eauto using InUtil.m_in_def.
        - intros N.
          contradict T1_nin_i.
          inversion N; subst; clear N; auto using Conc.in_acc_1.
          inversion H2.
        - intros N.
          contradict T2_nin_i.
          inversion N; subst; clear N; auto using Conc.in_acc_1.
          inversion H2.
      }
      (* Must be in the continuation. *)
      eapply IHERun in Hr2; eauto; try reflexivity.
      + intros N.
        contradict T1_nin_i.
        auto using Conc.in_acc_2.
      + intros N.
        contradict T2_nin_i.
        auto using Conc.in_acc_2.
      + intros N.
        contradict tid_nin.
        auto using Conc.var_acc.
      + intros N.
        contradict tid_rin.
        auto using Conc.in_range_access.
  - rename H1 into Hf.
    apply translate_inv_for in Hf; auto.
    destruct Hf as (l', (Hr, Hf)).
    assert (l' = l) by eauto using r_step_fun; subst.
    assert (R: m == m) by reflexivity.
    eapply IHERun in R; eauto.
    + intros N.
      contradict T1_nin_i.
      eauto using Conc.in_loop_to_for.
    + intros N.
      contradict T2_nin_i.
      eauto using Conc.in_loop_to_for.
    + intros N.
      contradict tid_nin.
      eauto using Conc.var_loop_to_for.
    + intros N.
      contradict tid_rin.
      eauto using Conc.in_range_loop_to_for.
  - apply translate_inv_loop_cons in H1; auto.
    destruct H1 as (vs1, (vs2, (vs3, (vs4, (R1, (Hl1, (Hl2, (Hl3, (Hf1, Hf2))))))))).
    simpl.
    rewrite R1 in H2; clear R1.
    rename H2 into Hx.
    apply e_in_summation_map2_prod_or in Hx.
    assert (X:
      EIn x0 (summation (map2 Prod vs1 vs2)) \/
      EIn x0 (summation (map2 Prod vs3 vs4))
    ). {
      destruct Hx as [Ha|Ha];
          apply e_in_summation_map2_plus_or in Ha;
          destruct Ha as [Ha|Ha].
      - left.
        apply e_in_rw_summation_map2_prod; auto.
      - right.
        apply e_in_rw_summation_map2_prod; auto.
      - left.
        apply e_in_rw_summation_map2_prod; auto.
      - right.
        apply e_in_rw_summation_map2_prod; auto.
    }
    clear Hx.
    destruct X as [Hx|Hx]. {
      assert (Hm: m1 == m1) by reflexivity.
      eapply IHERun1 in Hm; eauto.
      + intros N.
        apply Conc.in_seq_inv in N.
        destruct N as [N|N]. {
          apply Conc.in_subst_inv_1 in N.
          contradict T1_nin_i.
          auto using Conc.in_loop_2.
        }
        contradict T1_nin_i.
        auto using Conc.in_loop_3.
      + intros N.
        apply Conc.in_seq_inv in N.
        destruct N as [N|N]. {
          apply Conc.in_subst_inv_1 in N.
          contradict T2_nin_i.
          auto using Conc.in_loop_2.
        }
        contradict T2_nin_i.
        auto using Conc.in_loop_3.
      + intros N.
        apply Conc.var_seq_inv in N.
        destruct N as [N|N]. {
          apply Conc.var_subst_inv_1 in N.
          contradict tid_nin.
          auto using Conc.var_loop_2.
        }
        contradict tid_nin.
        auto using Conc.var_loop_3.
      + intros N.
        apply Conc.in_range_inv_seq in N.
        destruct N as [N|N].
        * apply Conc.in_range_subst_inv_1 in N.
          contradict tid_rin.
          auto using Conc.in_range_loop_l.
        * contradict tid_rin.
          auto using Conc.in_range_loop_r.
    }
    eapply IHERun2 in Hf2; eauto.
    + intros N.
      contradict T1_nin_i.
      auto using Conc.in_loop_cons.
    + intros N.
      contradict T2_nin_i.
      auto using Conc.in_loop_cons.
    + intros N.
      contradict tid_nin.
      auto using Conc.var_loop_cons.
    + intros N.
      contradict tid_rin.
      auto using Conc.in_range_loop_cons.
    + reflexivity.

  - apply translate_inv_loop_nil in H0.
    eapply IHERun in H0; eauto.
    + intros N.
      contradict T1_nin_i.
      auto using Conc.in_loop_3.
    + intros.
      contradict T2_nin_i.
      auto using Conc.in_loop_3.
    + intros N.
      contradict tid_nin.
      auto using Conc.var_loop_3.
    + intros N.
      contradict tid_rin.
      eauto using Conc.in_range_loop_r.
    + reflexivity.
  Qed.

  Corollary completeness:
    forall i m_l,
    LoopFree.Run i m_l ->
    forall m_h,
    SymHist.Run (translate i) m_h ->
    Hist.MSafe m_l ->
    ~ Conc.In T1 i ->
    ~ Conc.In T2 i ->
    ~ Conc.Var TID i ->
    ~ Conc.InRange TID i ->
    Hist.MSafeStrong m_h.
  Proof.
    intros.
    eapply Hist.m_safe_to_m_safe_strong; eauto.
    apply InUtil.all_incl_all_def.
    intros.
    apply SymHistMExp.e_run_2 in H0.
    apply LoopFreeMExp.e_run_2 in H.
    destruct H as (e1, (Hr1, Hm1)).
    destruct H0 as (e2, (Hr2, Hm2)).
    rewrite Hm1.
    rewrite Hm2 in H6.
    apply e_in_2 in H6.
    apply e_in_1.
    eapply completeness_1; eauto using f_run_eq, LoopFreeMExp.f_run_eq.
  Qed.

  End Defs.

End Compiler.
