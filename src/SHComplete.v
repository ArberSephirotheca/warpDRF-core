Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
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
Require Import RangeList.
Require Import SHCompiler.
Require Import MultiHist.
Import MHistNotations.
Require Conc.
Section Compiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).
  Definition mk_empty_1 n1 n2 : list history :=
    List.concat (map (fun _ => [[]]) (range_list n1 n2)) ++ [[]].

  Lemma f_run_decl_skip:
    forall x n1 n2,
    FRun (Decl x (NNum n1, NNum n2) Skip Skip) (One []).
  Proof.
    intros.
    rewrite prog_equiv_decl_skip.
    apply f_run_skip_eq.
  Qed.

  Lemma trans_run_skip:
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

  Lemma map_iter_2d_inv_seq:
    forall ks vs i j x y,
    Map (Iter2d x y (seq i j)) ks vs ->
    exists vs1 vs2,
    EEqList vs (map2 Prod vs1 vs2) /\
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
    destruct H5 as (vs1, (vs2, (R1, (Hm1, Hm2)))).
    apply iter_2d_inv_seq in H2.
    destruct H2 as (m1, (m2, (R2, (Hr1, Hr2)))).
    exists (m1 :: vs1), (m2::vs2).
    split; auto using map_cons.
    rewrite R2.
    rewrite R1.
    rewrite map2_cons_rw.
    reflexivity.
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
    destruct H5 as (vs1, (vs2, (R1, (Hm1, Hm2)))).
    apply iter_2d_inv_access in H2.
    destruct H2 as (m1, (m2, (R2, (Hacc, Hi)))).
    exists (m1::vs1), (m2::vs2).
    split; auto using map_cons.
    rewrite R2.
    rewrite R1.
    rewrite map2_cons_rw.
    reflexivity.
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

  Lemma translate_inv_access e m i (t1_nin: ~ Conc.In T1 (Conc.Acc e i)) (t2_nin: ~ Conc.In T2 (Conc.Acc e i)):
    FRun (translate (Conc.Acc e i)) m ->
    exists vs1 vs2 vs3 vs4,
    FRun (translate (Conc.Acc e Conc.Skip)) (summation (map2 Prod vs1 vs2)) /\
    FRun (translate i) (summation (map2 Prod vs3 vs4)) /\
    m == summation (map2 Prod (map2 Prod vs1 vs3) (map2 Prod vs2 vs4)).
  Proof.
    intros Hr.
    unfold translate in Hr.
    apply f_run_inv_decl_map_2d in Hr; auto using t1_neq_t2.
    destruct Hr as (r, (R1, Hm)).
    unfold do_proj in Hm.
    apply map_iter_2d_inv_seq in Hm.
    destruct Hm as (vs1, (vs2, (R2, (Hm1, Hm2)))).
    simpl in Hm1, Hm2.
    remove_eq TID TID.
    apply map_iter_2d_inv_acc in Hm1.
    destruct Hm1 as (vs3, (vs4, (R3, (Hm3, Hm4)))).
    apply map_iter_2d_inv_acc in Hm2.
    destruct Hm2 as (vs5, (vs6, (R4, (Hm5, Hm6)))).
    exists vs3, vs5, vs4, vs6.
    split. { auto using translate_access_skip. }
    split. { auto using translate_def. }
    rewrite R1.
    rewrite R2.
    rewrite R3.
    rewrite R4.
    reflexivity.
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
(*
  Lemma completeness_1
      (i:Conc.inst)
      (T1_nin_i: ~ Conc.In T1 i)
      (T2_nin_i: ~ Conc.In T2 i)
    :
    forall hs1,
    LoopFree.Run i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    SymHist.Run (translate i) hs2 ->
    Incl (MMember hs2) (MMember hs1).
  Proof.
    intros hs1 H.
    induction H; intros.
    - assert (hs2 = mk_empty_2 1 TID_COUNT). {
        assert (Hx := run_skip).
        eauto using SymHist.run_fun.
      }
      subst.
      rewrite mk_empty_2_rw.
      rewrite mem_equiv_cons_nil_rw.
      reflexivity.
    - apply c2_run_acc_inv_1 in H2; auto.
      destruct H2 as (f1, (Heq, Hf)).
      subst.
      rewrite mequiv_app_nil_r.
      destruct (list_eq_nil hs) as [N|hs_not_nil]. {
        subst.
        simpl.
        apply incl_mmember_nil.
        admit.
      }
      rewrite mmember_prepend_rw; auto.
      rewrite member_concat_rw.
      rewrite mequiv_app_nil_r.
      (*
      rewrite incl_l_either_iff.
      split. {
        apply c2_run_acc_inv_1 in H2; auto.
        destruct H2 as (f1, (?, Hf1)).
        subst.
        clear IHRun. (* We don't need IHRun *)
        (* Show that all members of v are in hss *)
        (* 1. simplify defs *)
        apply incl_def; intros.
        rewrite mmember_rw in *.
        apply m_in_app_l.
        (* At this point we know that the access is in the output of 
             Hist.GenAccess TID e TID_COUNT v
           So, we need to find out which task has created it. *)
        apply Hist.m_in_gen_access_inv with (v0:=x) in H; auto.
        destruct H as (t, (vs, (Ht, (Ha, (Hi, Hj))))).
        (* Knowing that some task performed the access, we need to
           figure out whether it was T1 or T2.
           If t = 0, then t = T2, otherwise t = T1. *)
        assert (Hd: t = 0 \/ 1 <= t) by omega.
        destruct Hd. {
          (* t = T2 *)
          (* In this case, we can pick any other task, say T1 = 1 *)
          assert (Hx1: 1 <= 1 < TID_COUNT) by auto using tid_count_1_lt with *.
          assert (Hx2: 0 <= 0 < 1 ) by omega.
          assert (Hf1 := Hf1 1 0 Hx1 Hx2); subst.
          destruct Hf1 as (f2, (hs1, (hs2, (?, (?, (Hr1, Hr2)))))).
          inversion Hr2; subst; clear Hr2.
          assert (v0 = vs) by eauto using access_step_fun.
          subst.
          apply m_in_branch_iter with (n:=1); auto.
          rewrite H.
          apply m_in_app_l.
          apply m_in_branch_iter with (n:=0); auto.
          rewrite H3.
          destruct (list_eq_nil hs1). {
            subst.
            apply SymHist.run_inv_nil in Hr1.
            contradiction.
          }
          apply m_in_prod_r; auto.
          assert (hs0 <> []). {
            intros N; subst.
            apply SymHist.run_inv_nil in H8.
            contradiction.
          }
          apply m_in_prepend_l; auto.
        }
        (* t = T1 *)
        (* In this case, we can pick any other task for T1 = 0 *)
        give_up.
      }
      (* Show that all members of hs are in hss *)
      (* We have that the access is in hs, so we must use the IH *)
      apply incl_def; intros.
      rewrite mmember_rw in *.
      assert (R: (Conc.Acc e i) = Conc.seq (Conc.Acc e Conc.Skip) i) by auto.
      rewrite R in H2; clear R.
      apply translate_seq in H2; auto.
      + destruct H2 as (m, (Hm, Hr)).
        apply SymHist.run_inv_seq in Hr.
        destruct Hr as (ma, (mb, (?, (Hr1, Hr2)))).
        assert (Hx := Hr2).
        apply IHRun in Hx.
        * subst.
          rewrite Hm.
          assert (ma <> nil). {
            intros N; subst.
            apply SymHist.run_inv_nil in Hr1.
            assumption.
          }
          apply m_in_prod_r; auto.
          give_up.
        * give_up.
        * give_up.
        * give_up.
      + give_up.
      + give_up.
      + give_up.
      + give_up.
    - give_up.
    - give_up.
    - give_up.
    *)
  Admitted.
*)
  Notation "'<[' x ']>'" := (translate x).
  Coercion NNum: nat >-> nexp.  
  Infix "⇓" := LoopFree.Run (at level 80).
  Notation "⊢" := Hist.Safe.
  Notation "⊨" := Hist.MSafe.
  (*
  Infix "*⊆" := AllIncl (at level 80).
  Infix "⊆*" := InclAll (at level 80).
  Infix "*⊆*" := AllInclAll (at level 70).
  *)
  Infix "×" := prod (at level 50).
  Infix "⤋" := SymHist.Run (at level 80).
  Notation "x *⊆* y" := (Incl (MMember x) (MMember y)) (at level 80).
  Notation "i '[' x ':=' n ']'" := (Conc.i_subst x n i) (at level 40).


  Theorem completeness:
    forall i hs1,
    LoopFree.Run i hs1 ->
    forall hs2,
    SymHist.Run (translate i) hs2 ->
    Hist.MSafe hs1 ->
    ~ Conc.In T1 i ->
    ~ Conc.In T2 i ->
    ~ Conc.Var TID i -> 
    Hist.MSafeStrong hs2.
  Proof.
    intros.
    eapply Hist.m_safe_to_m_safe_strong; eauto.
    unfold InUtil.AllInclAll, Ensembles.Included, Ensembles.In.
    intros.

  Admitted.

(*


 (*
  Lemma access_step_subst_1:
    forall t1 t2 e v,
    ~ access_in T1 e ->
    ~ access_in T2 e ->
    access_step
       (access_subst T2 (NNum t2)
          (access_subst T1 (NNum t1) (access_subst TID (NVar T1) e)), 
       NNum t1) v ->
    access_step
       (access_subst TID (NNum t1) e, NNum t1) v.
  Proof.
    intros.
    rename H1 into Hx.
    rewrite access_subst_subst_trans in Hx; auto.
    rewrite access_subst_subst_neq in Hx; auto using t2_neq_tid.
    rewrite access_subst_not_in with (x:=T2) in Hx; auto.
  Qed.
*)

(*
  Definition add {A:Type} f (a:nat) (v:A) :=
    (fun n => if PeanoNat.Nat.eq_dec n a then v else f n).

  Lemma add_eq_rw:
    forall A f a (hs1:A),
    add f a hs1 a = hs1.
  Proof.
    unfold add; intros.
    destruct (PeanoNat.Nat.eq_dec a a). {
      reflexivity.
    }
    contradiction.
  Qed.

  Lemma add_neq_rw:
    forall A f a b (x:A),
    a <> b ->
    add f a x b = f b.
  Proof.
    unfold add.
    intros.
    destruct (PeanoNat.Nat.eq_dec b a). {
      subst.
      contradiction.
    }
    reflexivity.
  Qed.

  Lemma map_add_rw_not_in:
    forall A a f l (x:A),
    ~ List.In a l ->
    map (add f a x) l = map f l.
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    assert (a <> a0). {
      intros N.
      subst.
      contradict H.
      auto using in_eq.
    }
    rewrite add_neq_rw; auto.
    assert (Hi : ~ List.In a l). {
      intros N.
      contradict H.
      auto using in_cons.
    }
    assert (IHl := IHl x Hi).
    rewrite IHl.
    reflexivity.
  Qed.
*)
(*
  Lemma c2_run_branch_inv:
    forall l i1 i2 x hs',
    SymHist.Run (SymHist.Branch x l i1 i2) hs' ->
    NoDup l ->
    exists f hs,
    hs' = ((List.concat (List.map f l)) ++ hs) /\ SymHist.Run i2 hs
    /\
    (forall n, List.In n l -> SymHist.Run (SymHist.seq (SymHist.i_subst x (NNum n) i1) i2) (f n)).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      simpl.
      exists (fun x => []).
      exists hs'.
      repeat split; auto.
      intros.
      contradiction.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHl in H8; auto.
    destruct H8 as (f, (hs3, (?,(?,Hr)))).
    subst.
    exists (add f a hs1).
    exists hs3.
    simpl.
    repeat split; auto.
    - rewrite add_eq_rw.
      rewrite app_assoc.
      rewrite map_add_rw_not_in; auto.
    - intros.
      destruct H. {
        subst.
        rewrite add_eq_rw.
        assumption.
      }
      assert (a <> n). {
        intros N; subst.
        contradiction.
      }
      rewrite add_neq_rw; auto.
  Qed.
*)

  Lemma subst_t1_tid_eq:
    forall v e,
    ~ SymHist.In T1 e ->
    SymHist.i_subst T1 v (SymHist.i_subst TID (NVar T1) e) =
    SymHist.i_subst TID v e.
  Proof.
    intros.
    rewrite SymHist.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_tid_eq:
    forall v e,
    ~ SymHist.In T2 e ->
    SymHist.i_subst T2 v (SymHist.i_subst TID (NVar T2) e) =
    SymHist.i_subst TID v e.
  Proof.
    intros.
    rewrite SymHist.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_neq:
    forall e n1 n2,
    ~ SymHist.In T2 e ->
    SymHist.i_subst T2 (NNum n2) (SymHist.i_subst TID (NNum n1) e)
    =
    SymHist.i_subst TID (NNum n1) e.
  Proof.
    intros.
    rewrite SymHist.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply SymHist.in_i_subst_neq in N; auto using t2_neq_tid.
    intros M.
    inversion M.
  Qed.

  Lemma subst_t1_t2_neq:
    forall v e,
    ~ SymHist.In T1 e ->
    SymHist.i_subst T1 v (SymHist.i_subst TID (NVar T2) e)
    = 
    SymHist.i_subst TID (NVar T2) e.
  Proof.
    intros.
    rewrite SymHist.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply SymHist.in_subst_inv_in in N; auto using t1_neq_t2, t1_neq_tid.
  Qed.


  Lemma rw_1 e (t1_nin: ~ SymHist.In T1 (proj e)):
    forall n1,
        SymHist.i_subst T1 (NNum n1)
           (SymHist.Decl T2 (NNum 0, NVar T1)
              (SymHist.seq (do_proj T1 e)
                 (do_proj T2 e)) SymHist.Skip)
   =
       SymHist.Decl T2 (NNum 0, NNum n1)
        (SymHist.seq (SymHist.i_subst TID (NNum n1) (proj e))
                (do_proj T2 e)) SymHist.Skip.
  Proof.
    intros.
    simpl.
    remove_eq T1 T2.
    remove_eq T1 T1.
    rewrite SymHist.i_subst_seq.
    unfold do_proj in *.
    rewrite subst_t1_tid_eq; auto.
    rewrite subst_t1_t2_neq; auto.
  Qed.

  Lemma nin_t1_tid:
    ~ NIn T1 (NVar TID).
  Proof.
    intros N.
    inversion N.
    tasks_absurd.
  Qed.

  Lemma rw_2:
    forall e n1 n2,
    ~ Conc.In T2 e ->
    SymHist.i_subst T2 (NNum n2)
       (SymHist.seq
          (SymHist.i_subst TID (NNum n1) (proj e))
          (do_proj T2 e))
    = 
    SymHist.seq
      (SymHist.i_subst TID (NNum n1) (proj e))
      (SymHist.i_subst TID (NNum n2) (proj e)).
  Proof.
    intros.
    rewrite SymHist.i_subst_seq.
    assert (~ SymHist.In T2 (proj e)). {
      intros N.
      eapply in_proj_to_in in N; eauto using t2_neq_tid.
    }
    rewrite subst_t2_neq; auto.
    unfold do_proj.
    rewrite subst_t2_tid_eq; auto.
  Qed.

(*
  Lemma map_rw_repeat:
    forall A B m l,
    @map A B (fun _ : A => m) l = List.repeat m (List.length l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma map_repeat_rw:
    forall A B (x:B) l,
    map (fun _ : A => x) l = List.repeat x (List.length l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma concat_eq_rw:
    forall A B m l,
    @List.concat (list B) (map (fun _ : A => [m]) l) = List.repeat m (List.length l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Definition summation :=
  List.fold_right Nat.add 0.

  Lemma repeat_app:
    forall A (x:A) n1 n2,
    repeat x (n1 + n2) = repeat x n1 ++ repeat x n2.
  Proof.
    induction n1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHn1.
    reflexivity.
  Qed.

  Lemma concat_eq_nil_rw:
    forall (l:list nat),
    List.concat (map (fun n => repeat (@nil nat) n) l) =
    List.repeat [] (summation l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    rewrite repeat_app.
    reflexivity.
  Qed.
  Import C2Notations.
*)
(*
  Lemma run_trans_inv e  (t1_nin: ~ Conc.In T1 e) (t2_nin: ~ Conc.In T2 e) hs:
    FRun (translate e) hs ->
    exists f1,
    hs = List.concat (SymHist.branch_iter 1 TID_COUNT f1)
    /\
    forall n1,
    1 <= n1 < TID_COUNT ->
    exists f2,
    f1 n1 = List.concat (SymHist.branch_iter 0 n1 f2) ++ [[]] /\
    forall n2,
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      SymHist.Run (SymHist.i_subst TID (NNum n1) (proj e)) hs1 /\
      SymHist.Run (SymHist.i_subst TID (NNum n2) (proj e)) hs2

  .
  Proof.
    intros.
    unfold translate in *.
    apply SymHist.run_decl_inv_map in H.
    destruct H as (ms, (m, (?, (Hs, H)))).
    inversion Hs; subst; clear Hs.
    rewrite prod_nil_nil_r.
    apply SymHist.decl_map_inv in H.
    destruct H as (f1, (R1, Hf)).
    exists f1.
    rewrite R1.
    split; auto.
    intros n1 Ha.
    apply Hf in Ha; clear Hf.
    assert (X:~ SymHist.In T1 (proj e)). {
      intros N.
      contradict t1_nin.
      auto using in_proj_to_in, t1_neq_tid.
    }
    rewrite rw_1 in Ha; auto.
    apply SymHist.run_decl_inv_map in Ha.
    destruct Ha as (ms2, (hs, (R2,(Ha,Hc)))).
    apply SymHist.decl_map_inv in Hc.
    destruct Hc as (f2, (R3, Hc)). 
    inversion Ha; subst; clear Ha.
    exists f2.
    rewrite R2.
    assert (forall n2, 
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      SymHist.Run (SymHist.i_subst TID (NNum n1) (proj e)) hs1 /\
      SymHist.Run (SymHist.i_subst TID (NNum n2) (proj e)) hs2
    ). {
      intros n2 Hb.
      apply Hc in Hb; clear Hc.
      rewrite rw_2 in Hb; auto.
      apply SymHist.run_inv_seq in Hb.
      destruct Hb as (hsa, (hsb, (?,(Hr,Hs)))).
      eauto.
    }
    rewrite prod_nil_nil_r.
    eauto.
  Qed.
*)
  Definition TranslatedProj f e :=
    forall n, 0 <= n < TID_COUNT -> SymHist.Run (SymHist.i_subst TID (NNum n) (proj e)) (f n).

  Lemma i_subst_do_proj:
    forall x i n,
    ~ In x (proj i) ->
    i_subst x (NNum n) (do_proj x i) =
    i_subst TID (NNum n) (proj i).
  Proof.
    intros.
    unfold do_proj.
    apply i_subst_subst_trans.
    assumption.
  Qed.

(*
  Definition multi_prepend (m1:list (list history)) mm2 :=
    List.map
      (fun (p:list history * list (list history)) => let (h, m) := p in List.concat (prepend h m) )
      (List.combine m1 mm2).

  Lemma map_simpl_1:
    forall hs,
    MMEquivStruct
      (map (fun x : list (list history) => prod (List.concat x) [[]] ++ [[]])
             hs) 
      (map (List.concat (A:=history)) hs).
  Proof.
    induction hs; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    rewrite IHhs.
    rewrite prod_nil_nil_r.
    rewrite mequiv_app_nil_r.
    reflexivity.
  Qed.
*)
  Import Morphisms.

  Lemma run_trans_inv_2 e  (t1_nin: ~ Conc.In T1 e) (t2_nin: ~ Conc.In T2 e) hs:
    FRun (translate e) hs ->
    exists m1 ms2,
    hs == summation (map2 Prod m1 (map summation ms2))
   /\
    DeclMap T1 (do_proj T1 e) 1 TID_COUNT m1 /\
    Map (DeclMap T2 (do_proj T2 e) 0) (range_list 1 TID_COUNT)
        ms2
  .
  Proof.
    intros.
    apply f_run_decl_inv_map in H.
    destruct H as (mm1, (m2, (?, (Hs, Hd)))).
    apply f_run_inv_skip in Hs.
    rewrite Hs in *.
    clear Hs.
    rewrite e_prod_nil_r in H.
    assert (~ In T1 (proj e)). {
      intros N.
      contradict t1_nin.
      apply in_proj_to_in; auto using t1_neq_tid.
    }
    apply decl_map_rw with (
      j:=seq (do_proj T1 e) (Decl T2 (NNum 0, NVar T1) (do_proj T2 e) Skip)
    ) in Hd.
    2: {
      intros.
      repeat rewrite i_subst_seq.
      rewrite rw_1; auto.
      unfold do_proj.
      rewrite i_subst_subst_trans; auto.
      simpl.
      remove_eq T1 T1.
      remove_eq T1 T2.
      remember (i_subst TID _ _) as i1.
      rewrite subst_t1_t2_neq; auto.
      remember (i_subst _ (NVar T2) _) as i2.
      apply equiv_i_subst_decl_seq; auto with *.
      subst.
      intros N.
      contradict t2_nin.
      apply in_i_subst_neq in N; auto using t2_neq_tid.
      - apply in_proj_to_in; auto using t2_neq_tid.
      - intros M; inversion M.
    }
    apply decl_map_inv_seq in Hd.
    destruct Hd as (ms1, (ms3, (Hb1, (Hb2, Hrl)))).
    rewrite Hrl in *; clear Hrl mm1.
    apply decl_map_inv_decl_not_in in Hb2; auto using tid_count_1_lt, t1_neq_t2.
    - exists ms1.
      destruct Hb2 as (m, (m1, (R, (Hr, Hf2)))).
      rewrite R in H; clear R.
      apply f_run_inv_skip in Hr.
      exists m1.
      assert (Rm: EEqList (map (fun x : list mexp => Σ x * m) m1) (map summation m1)). {
        apply e_eq_list_map_rw.
        intros.
        rewrite Hr.
        rewrite e_prod_nil_r.
        reflexivity.
      }
      rewrite Rm in H.
      rewrite H.
      split. { reflexivity. }
      split; auto.
    - unfold do_proj.
      intros N.
      apply in_subst_inv_in in N; auto using t1_neq_t2, t1_neq_tid.
    - intros N.
      inversion N.
  Qed.
(*
  Lemma concat_map_eq_repeat:
    forall A m n1 n2,
    @List.concat (list A) (map (fun _ : nat => [m]) (range_list n1 n2)) =
    repeat m (n2 - n1).
  Proof.
    intros.
    rewrite concat_eq_rw.
    rewrite range_list_fun_length.
    reflexivity.
  Qed.

  Lemma mk_empty_1_rw:
    forall n1 n2,
    mk_empty_1 n1 n2 == [].
  Proof.
    intros.
    unfold mk_empty_1.
    rewrite concat_eq_rw.
    rewrite mem_equiv_nil_rw.
    rewrite mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Lemma mk_empty_2_rw:
    forall n1 n2,
    mk_empty_2 n1 n2 == [].
  Proof.
    unfold mk_empty_2.
    intros.
    rewrite mem_equiv_cons_nil_rw.
    rewrite app_nil_r.
    remember (map _ _).
    destruct (list_eq_nil l) as [R|Hne]. {
      rewrite R.
      reflexivity.
    }
    apply mem_equiv_concat_refl_rw; auto.
    intros.
    subst.
    apply in_map_iff in H.
    destruct H as (n, (?, Hi)).
    subst.
    rewrite mk_empty_1_rw.
    reflexivity.
  Qed.
*)
  Lemma t1_not_in_proj_skip:
    ~ SymHist.In T1 (proj Conc.Skip).
  Proof.
    simpl.
    intros N.
    inversion N.
  Qed.
(*
  Lemma repeat_nil_rw_1:
    forall {A} n,
    repeat (@nil A) n ++ [[]] = [] :: repeat [] n.
  Proof.
    induction n; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma mk_empty_1_spec:
    forall n1 n2,
    mk_empty_1 n1 n2 = @repeat history [] (S (n2 - n1)).
  Proof.
    intros.
    unfold mk_empty_1.
    rewrite concat_eq_rw.
    simpl.
    rewrite range_list_fun_length.
    rewrite repeat_nil_rw_1.
    reflexivity.
  Qed.

  Lemma mk_empty_2_spec:
    forall n1 n2,
    exists n,
    mk_empty_2 n1 n2 = @repeat history [] (S n).
  Proof.
    intros.
    unfold mk_empty_2.
    remember (range_list n1 n2).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    induction Heql.
    - simpl.
      exists 0.
      reflexivity.
    - destruct IHHeql as (n, Hr).
      exists (S (low - 0) + n).
      simpl.
      rewrite app_assoc_reverse.
      rewrite Hr; clear Hr.
      rewrite mk_empty_1_spec.
      rewrite PeanoNat.Nat.sub_0_r.
      repeat rewrite <- repeat_app.
      rewrite PeanoNat.Nat.add_succ_r.
      reflexivity.
  Qed.

  Lemma prod_mk_empty_2_rw:
    forall m,
    m == prod (mk_empty_2 1 TID_COUNT) m.
  Proof.
    intros.
    apply prod_absorb_l.
    - unfold mk_empty_2.
      destruct (List.concat _). {
        intros N.
        inversion N.
      }
      intros N; inversion N.
    - apply mk_empty_2_rw.
  Qed.
*)
(*
  Lemma run_translate:
    forall i f1,
    ~ In T1 (proj i) ->
    ~ Conc.In T2 i ->
    (forall n1,
    1 <= n1 < TID_COUNT ->
    exists f2,
    f1 n1 = List.concat (branch_iter 0 n1 f2) ++ [[]] /\
    forall n2,
    0 <= n2 < n1 ->
    exists hs1 hs2, f2 n2 = prod hs1 hs2 /\
    FRun (i_subst TID (NNum n1) (proj i)) hs1 /\
    FRun (i_subst TID (NNum n2) (proj i)) hs2) ->
    FRun (translate i) (List.concat (branch_iter 1 TID_COUNT f1) ++ [[]]).
  Proof.
    intros i f1 Hni1 Hni2 Hf1.
    unfold translate.
    eapply run_decl_map_def with (f:=f1) (hs:=[[]]).
    - rewrite prod_nil_nil_r.
      unfold branch_iter.
      reflexivity.
    - intros n1 Hn1.
      rewrite rw_1; auto.
      assert (Hf1 := Hf1 _ Hn1).
      destruct Hf1 as (f2, (Heq1, Hf2)).
      apply run_decl_map_def with (f:=f2) (hs:=[[]]).
      + rewrite Heq1.
        unfold branch_iter.
        rewrite prod_nil_nil_r.
        reflexivity.
      + intros n2 Hn2.
        assert (Hf2 := Hf2 _ Hn2).
        destruct Hf2 as (hs1, (hs2, (He2, (Hr1, Hr2)))).
        rewrite rw_2; auto.
        rewrite He2.
        apply run_seq; auto.
      + apply SymHist.run_skip.
    - apply SymHist.run_skip.
  Qed.
*)
(*
  Lemma translate_acc_inv e hs i (t1_nin: ~ Conc.In T1 (Conc.Acc e i)) (t2_nin: ~ Conc.In T2 (Conc.Acc e i)):
    FRun (translate (Conc.Acc e i)) hs ->
    exists f1,
    hs = List.concat (branch_iter 1 TID_COUNT f1) ++ [[]]
    /\
    forall n1,
    1 <= n1 < TID_COUNT ->
    exists f2,
    f1 n1 = List.concat (branch_iter 0 n1 f2) ++ [[]] /\
    forall n2, 0 <= n2 < n1 ->
    exists hs1 hs2,
    f2 n2 = prod hs1 hs2/\
    SymHist.Run
        (SymHist.Acc (access_subst TID (NNum n1) e, NNum n1)
           (SymHist.i_subst TID (NNum n1) (proj i))) hs1 /\
    SymHist.Run
        (SymHist.Acc (access_subst TID (NNum n2) e, NNum n2)
           (SymHist.i_subst TID (NNum n2) (proj i))) hs2
   .
  Proof.
    intros.
    (* ---- *)
    apply run_trans_inv in H; auto.
    destruct H as (f1, (?, Hf)).
    exists f1.
    split; auto.
    intros n1 Hn1.
    assert (Hf := Hf _ Hn1).
    destruct Hf as (f2, (?, Hf2)).
    exists f2.
    split; auto.
    intros n2 Hn2.
    assert (Hf2 := Hf2 _ Hn2).
    destruct Hf2 as (hs1, (hs2, (?, (Hr1, Hr2)))).
    simpl in *.
    remove_eq TID TID.
    eauto.
  Qed.
*)
(*
  Lemma map_branch_map_inv_acc:
    forall l x e i (f:nat -> list nat) hs,
    Map (fun n hss => BranchMap x (Acc e i) (f n) hss) l hs ->
    exists hs1 hs2,
    hs = map2 (map2 prod) hs1 hs2 /\
    Map (fun n hss => BranchMap x (Acc e Skip) (f n) hss) l hs1 /\
    Map (fun n hss => BranchMap x i (f n) hss) l hs2.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      exists [].
      exists [].
      auto using map_nil.
    }
    inversion H; subst; clear H.
    apply IHl in H5.
    destruct H5 as (hs1, (hs2, (?, (Hm1, Hm2)))).
    subst.
    apply branch_map_inv_acc in H2.
    destruct H2 as (ms1, (ms2, (?, (Hb1, Hb2)))).
    subst.
    eapply map_cons in Hm1; eauto.
    eapply map_cons in Hm2; eauto.
    eexists.
    eexists.
    repeat split; eauto.
    rewrite map2_cons_rw.
    auto.
  Qed.
*)
(*
  Lemma map_decl_map_inv_acc:
    forall x a i n l hs,
    Map (DeclMap x (Acc a i) n) l hs ->
    exists hs1 hs2,
    EEqList hs (map2 (map2 Prod) hs1 hs2) /\
    Map (DeclMap x (Acc a Skip) n) l hs1 /\
    Map (DeclMap x i n) l hs2.
  Proof.
    unfold DeclMap.
    intros.
    apply map_branch_map_inv_acc in H.
    destruct H as (hs1, (hs2, (?, (Hm1, Hm2)))).
    eauto.
  Qed.
  *)
(*
  Lemma map_decl_map_simpl_1:
    forall x y i l m n,
    ~ In x i ->
    Map (DeclMap x (i_subst y (NVar x) i) n) l m ->
    Map (DeclMap y i n) l m.
  Proof.
    intros.
    apply map_impl with (P:=(DeclMap x (i_subst y (NVar x) i) n)); auto.
    intros.
    eapply decl_map_inv_i_subst_eq; eauto.
  Qed.

  Lemma repeat_map_range_list:
    forall A (h:A) n1 n2, 
    repeat h (n2 - n1) = map (fun _ : nat => h) (range_list n1 n2).
  Proof.
    intros.
    rewrite map_repeat_rw.
    rewrite range_list_fun_length.
    reflexivity.
  Qed.

  Lemma decl_map_not_in:
    forall x i h n1 n2,
    ~ In x i ->
    Run i h ->
    DeclMap x i n1 n2 (repeat h (n2 - n1)).
  Proof.
    intros.
    rewrite repeat_map_range_list.
    apply decl_map_def.
    intros.
    rewrite i_subst_not_in; auto.
  Qed.

  Definition m_decl n1 n2 (m1 m2 : list history) :=
    (prod (List.concat (repeat m1 (n2 - n1))) m2 ++ m2).

  Lemma run_decl_map_not_in:
    forall i j m1 m2 x n1 n2,
    ~ In x i ->
    Run i m1 ->
    Run j m2 ->
    Run (Decl x (NNum n1, NNum n2) i j) (m_decl n1 n2 m1 m2). 
  Proof.
    unfold m_decl.
    eauto using run_decl_map, decl_map_not_in.
  Qed.

  Definition m_decl_seq (m1 : list history) (m2 m3 : list (list history)) :=
    prod (List.concat (map2 prod m2 m3)) m1 ++ m1.

  Lemma branch_map_decl_not_in:
    forall l i m1 m2 x y j,
    ~ In y i ->
    ~ In x j ->
    x <> y ->
    Run j m1 ->
    BranchMap x i l m2 ->
    BranchMap x (Decl y (NNum 0, NVar x) i j) l (map2 (fun n m => m_decl 0 n m m1) l m2).
  Proof.
    induction l; intros; inversion H3; subst; clear H3. {
      apply branch_map_nil.
    }
    rewrite map2_cons_rw.
    apply branch_map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      apply run_decl_map_not_in.
      + intros N.
        contradict H.
        eapply in_i_subst_neq; eauto.
        intros M.
        inversion M.
      + assumption.
      + rewrite i_subst_not_in; auto.
    - apply IHl; auto.
  Qed.


  Lemma decl_map_decl_not_in:
    forall n1 n2 i m1 m2 x y j,
    ~ In y i ->
    ~ In x j ->
    x <> y ->
    Run j m1 ->
    DeclMap x i n1 n2 m2 ->
    DeclMap x (Decl y (NNum 0, NVar x) i j) n1 n2 (map2 (fun n m => m_decl 0 n m m1) (range_list n1 n2) m2).
  Proof.
    intros.
    apply branch_map_decl_not_in; auto.
  Qed.

  Definition m_t1 m :=
    map2 (fun n m => m_decl 0 n m [[]]) (range_list 1 TID_COUNT) m.

  Lemma decl_map_translate_t1:
    forall i m,
     ~ In T1 (proj i) ->
     ~ In T2 (proj i) ->
     DeclMap T1 (do_proj T1 i) 1 TID_COUNT m ->
     DeclMap T1 (Decl T2 (NNum 0, NVar T1) (do_proj T1 i) Skip) 1 TID_COUNT (m_t1 m).
  Proof.
    intros.
    apply decl_map_decl_not_in; auto using SymHist.run_skip, t1_neq_t2.
    - unfold do_proj.
      intros N.
      contradict H0.
      apply in_i_subst_neq in N; auto using t2_neq_tid.
      intros M.
      inversion M.
      contradict H2.
      auto using t1_neq_t2.
    - intros N.
      inversion N.
  Qed.

  Lemma branch_map_translate_t2:
    forall l i m,
    ~ Conc.In T1 i ->
    Map (DeclMap T2 (do_proj T2 i) 0) l m ->
    BranchMap T1 (Decl T2 (NNum 0, NVar T1) (do_proj T2 i) Skip) l (map (fun n=> prod (List.concat n) [[]] ++ [[]]) m).
  Proof.
    induction l; intros; inversion H0; subst; clear H0. {
      apply branch_map_nil.
    }
    apply IHl in H6; auto.
    apply branch_map_cons; auto.
    simpl.
    remove_eq T1 T2.
    remove_eq T1 T1.
    eapply run_decl_map; eauto using SymHist.run_skip.
    rewrite i_subst_not_in; auto.
    intros N.
    contradict H.
    unfold do_proj in *.
    apply in_subst_inv_in in N; auto using t1_neq_t2, t1_neq_tid.
    apply in_proj_to_in; auto using t1_neq_tid.
  Qed.

  Definition m_t2 (m:list (list (list history))) := (map (fun n=> prod (List.concat n) [[]] ++ [[]]) m).

  Lemma decl_map_translate_t2:
    forall i m,
    ~ Conc.In T1 i ->
    Map (DeclMap T2 (do_proj T2 i) 0) (range_list 1 TID_COUNT) m ->
    DeclMap T1 (Decl T2 (NNum 0, NVar T1) (do_proj T2 i) Skip) 1 TID_COUNT (m_t2 m).
  Proof.
    intros.
    apply branch_map_translate_t2; auto.
  Qed.
(*
  Lemma run_translate_def2:
    forall m1 i m2,
    ~ In T1 (proj i) ->
    ~ Conc.In T2 i ->
    DeclMap T1 (i_subst TID (NVar T1) (proj i)) 1 TID_COUNT m1 ->
    Map (DeclMap T2 (i_subst TID (NVar T2) (proj i)) 0)
        (range_list 1 TID_COUNT) m2 ->
    Run (translate i) (List.concat (map2 prod (m_t1 m1) (m_t2 m2))).
  Proof.
    intros.
    assert (~ In T2 (proj i)). {
      intros N.
      contradict H0.
      apply in_proj_to_in; auto using t2_neq_tid.
    }
    apply decl_map_translate_t1 in H1; auto.
    apply decl_map_translate_t2 in H2; auto.
    - unfold translate.
      apply run_decl_seq.
    eexists.
    apply run_decl_map_skip.
    eapply decl_map_inv_i_subst_eq in H1; eauto.
    apply run_decl_map.
    rewrite equiv_i_subst_decl_seq.
    eapply map_decl_map_simpl_1 in H2; eauto.
    eexists.
    assert (Hd: exists md,
      DeclMap
        T1
        (Decl T2 (NNum 0, NVar T1) (seq (do_proj T1 i) (do_proj T2 i)) Skip) 1
        TID_COUNT
        md
      ). {
      apply decl_map_iter_def.
      intros n1 Hn1.
      (* -- *)
      Search (DeclMap _ _ _ _ ).
      Search Map.
      eapply run_decl_map in H1; eauto using SymHist.run_skip.
      apply decl_map_from_map in H2.
      eapply run_decl_map in H2; eauto using SymHist.run_skip.
      eapply map_in_range_list in H1; eauto.
      destruct Hn1 as (h, (Hi_m1, Hr)).
      apply decl_map_not_in with (x:=T2) (n1:=0) (n2:=n1) in Hr; auto.
      2: {
        intros N.
        contradict H0.
        apply in_i_subst_neq in N; auto using t2_neq_tid.
        apply in_proj_to_in; auto using t2_neq_tid.
        intros M.
        inversion M.
      }
      (* -- *)
      eapply map_in_range_list in H2; eauto.
      destruct H2 as (v, (Ht2,Hv)).
      simpl.
      remove_eq T1 T2.
      remove_eq T1 T1.
      exists (prod (List.concat (map2 prod (repeat h (n1 - 0)) v)) [[]] ++ [[]]).
      eapply run_decl_map; eauto using SymHist.run_skip.
      rewrite i_subst_seq.
      apply decl_map_seq.
      - unfold do_proj.
        rewrite i_subst_subst_trans; eauto.
      - unfold do_proj.
        rewrite subst_t1_t2_neq; eauto.
    }
    destruct Hd as (m, Hd).
    exists (prod (List.concat m) [[]] ++ [[]]).
    unfold translate.
    eauto using run_decl_map, SymHist.run_skip.
  Qed.
*)
*)
(*
  Lemma run_translate_def2:
    forall m1 i m2,
    ~ In T1 (proj i) ->
    ~ Conc.In T2 i ->
    DeclMap T1 (i_subst TID (NVar T1) (proj i)) 1 TID_COUNT m1 ->
    Map (DeclMap T2 (i_subst TID (NVar T2) (proj i)) 0)
        (range_list 1 TID_COUNT) m2 ->
    exists hs2, Run (translate i) hs2.
  Proof.
    intros.
    unfold translate.
    eexists.
    rewrite equiv_i_subst_decl_seq.
    eapply decl_map_inv_i_subst_eq in H1; eauto.
    eapply map_decl_map_simpl_1 in H2; eauto.
    eexists.
    assert (Hd: exists md,
      DeclMap
        T1
        (Decl T2 (NNum 0, NVar T1) (seq (do_proj T1 i) (do_proj T2 i)) Skip) 1
        TID_COUNT
        md
      ). {
      apply decl_map_iter_def.
      intros n1 Hn1.
      (* -- *)
      Search (DeclMap _ _ _ _ ).
      Search Map.
      eapply run_decl_map in H1; eauto using SymHist.run_skip.
      apply decl_map_from_map in H2.
      eapply run_decl_map in H2; eauto using SymHist.run_skip.
      eapply map_in_range_list in H1; eauto.
      destruct Hn1 as (h, (Hi_m1, Hr)).
      apply decl_map_not_in with (x:=T2) (n1:=0) (n2:=n1) in Hr; auto.
      2: {
        intros N.
        contradict H0.
        apply in_i_subst_neq in N; auto using t2_neq_tid.
        apply in_proj_to_in; auto using t2_neq_tid.
        intros M.
        inversion M.
      }
      (* -- *)
      eapply map_in_range_list in H2; eauto.
      destruct H2 as (v, (Ht2,Hv)).
      simpl.
      remove_eq T1 T2.
      remove_eq T1 T1.
      exists (prod (List.concat (map2 prod (repeat h (n1 - 0)) v)) [[]] ++ [[]]).
      eapply run_decl_map; eauto using SymHist.run_skip.
      rewrite i_subst_seq.
      apply decl_map_seq.
      - unfold do_proj.
        rewrite i_subst_subst_trans; eauto.
      - unfold do_proj.
        rewrite subst_t1_t2_neq; eauto.
    }
    destruct Hd as (m, Hd).
    exists (prod (List.concat m) [[]] ++ [[]]).
    unfold translate.
    eauto using run_decl_map, SymHist.run_skip.
  Qed.
*)


  Lemma translate_seq e1 (t1_nin1: ~ Conc.In T1 e1) (t2_nin1: ~ Conc.In T2 e1):
    forall e2,
    ~ Conc.In T1 e2 ->
    ~ Conc.In T2 e2 ->
    forall m1,
    SymHist.Run (translate (Conc.seq e1 e2)) m1 ->
    exists m2,
    m1 == m2 /\ SymHist.Run (SymHist.seq (translate e1) (translate e2)) m2.
  Proof.
    induction e1; intros e2 t1_nin2 t2_nin2 m1 Hr.
    - simpl in Hr.
      assert (Hx := Hr).
      exists (prod (mk_empty_2 1 TID_COUNT) m1).
      split. {
        apply prod_mk_empty_2_rw.
      }
      apply SymHist.run_seq; auto using run_skip.
    - simpl in Hr.
      eexists.
      split.
      2: {
        apply run_seq.
      }
      apply c2_run_acc_inv_1 in Hr.
      + destruct Hr as (f1, (?, Hf)).
        subst.
  Admitted.
*)
(*
  Lemma m_in_branch_iter:
    forall A x n n1 n2 f,
    n1 <= n < n2 ->
    MIn x (f n) ->
    @MIn A x (branch_iter n1 n2 f).
  Proof.
    intros.
    unfold branch_iter.
    apply range_list_in in H.
    apply m_in_concat with (l:=f n); auto.
    apply in_map.
    auto.
  Qed.
*)



  End Defs.

End Compiler.
