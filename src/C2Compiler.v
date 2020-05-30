Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
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
Require Import Acc.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Conc1.
Require Import SetTh.
Import ListNotations.
Require Import Conc2.

Section Compiler.
  Import Conc1.
  Section Defs.
  Context {A:Access}.
  Variable TID_COUNT: nat.
  Variable TID : var.

  Fixpoint proj (c:C1.inst) : C2.inst :=
    match c with
    | C1.Skip => C2.Skip
    | C1.Acc a c1 => C2.Acc (a, NVar TID) (proj c1)
    | C1.For x r c1 c2 => C2.Decl x r (proj c1) (proj c2)
    | C1.Loop x l c1 c2 => C2.Branch x l (proj c1) (proj c2) 
    end.

  Variable T1: var.
  Variable T2: var.

  Definition do_proj x i := C2.i_subst TID (NVar x) (proj i).

  Definition translate (c:C1.inst) : C2.inst :=
      (C2.Decl T1 (NNum 1, NNum TID_COUNT)
        (C2.Decl T2 (NNum 0, NVar T1)
          (C2.seq (do_proj T1 c) (do_proj T2 c))
        C2.Skip)
      C2.Skip).

(*
  Notation "i '[' x ':=' n ']'" := (C2.i_subst x n i) (at level 40).
  Notation "i '[' x ':=' n ']'" := (C1.i_subst x n i) (at level 40).
(*  Notation "'[[' i ']]'" := (proj i) (at level 40). *)
  Coercion NNum: nat >-> nexp.
*)

  Lemma in_to_in_proj:
    forall x i,
    C1.In x i ->
    C2.In x (proj i).
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H;
        auto using C2.in_acc_1, C2.in_acc_3, C2.in_decl_1, C2.in_decl_2, C2.in_decl_3,
          C2.in_decl_4, C2.in_branch_1, C2.in_branch_2, C2.in_branch_3.
  Qed.

  Lemma in_proj_to_in:
    forall x i,
    x <> TID ->
    C2.In x (proj i) ->
    C1.In x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0;
        auto using C1.in_acc_1, C1.in_acc_2, C1.in_for_1, C1.in_for_2, C1.in_for_3,
          C1.in_for_4, C1.in_loop_1, C1.in_loop_2, C1.in_loop_3.
    inversion H2; subst; clear H2.
    contradiction.
  Qed.

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (C1.i_subst x (NNum n) i) = C2.i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
  Qed.

  Lemma var_eq_dec_rw_eq:
    forall x,
    exists e, Set_VAR.MF.eq_dec x x = @left _ _ e.
  Proof.
    intros.
    destruct (Set_VAR.MF.eq_dec x x).
    - exists e.
      reflexivity.
    - contradiction.
  Qed.

  Lemma proj_seq:
    forall i1 i2,
    proj (C1.seq i1 i2) = C2.seq (proj i1) (proj i2).
  Proof.
    induction i1; intros; simpl.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
  Qed.

  Theorem run_m_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n hs1,
    n < TID_COUNT ->
    C2.Run (C2.i_subst TID (NNum n) (proj i)) hs1 ->
    ~ C1.Var TID i ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    intros i hs2 H.
    induction H; intros.
    - inversion H0; subst; clear H0.
      reflexivity.
    - inversion H2; subst; clear H2.
      apply C1.var_not_in_acc in H3.
      assert (IHRun := IHRun _ _ H1 H8 H3).
      subst.
      destruct (var_eq_dec_rw_eq TID) as (?, R).
      rewrite R in *; clear R.
      erewrite Hist.m_proj_prepend; eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (l0 = l). {
        assert (R: r_subst TID (NNum n) r = r). {
          apply r_subst_not_in.
          eapply r_step_to_not_in; eauto.
        }
        rewrite R in *.
        eauto using r_step_fun.
      }
      subst.
      assert (~ C1.Var TID (C1.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        eauto using C1.var_loop_to_for.
      }
      eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (~ C1.Var TID (C1.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        auto using C1.var_loop_cons.
      }
      apply IHRun2 in H11; auto; clear IHRun2.
      subst.
      rewrite Hist.m_proj_app.
      assert (Hist.m_proj n0 hs1 = hs3). {
        destruct (Set_VAR.MF.eq_dec TID x). {
          apply C1.var_not_in_loop in H3.
          destruct H3 as (?, _).
          contradiction.
        }
        apply IHRun1; auto; clear IHRun1.
        + rewrite C2.i_subst_subst_neq in H10; auto.
          rewrite <- C2.i_subst_seq in H10.
          rewrite <- i_subst_proj_rw in H10; auto.
          rewrite proj_seq in *.
          auto.
        + intros N.
          contradict H2.
          eauto using C1.var_iter_loop.
      }
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (~ C1.Var TID i2). {
        intros N.
        contradict H2.
        auto using C1.var_loop_3.
      }
      auto.
  Qed.

  Lemma run_do_proj (T:var):
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n hs1,
    n < TID_COUNT -> 
    C2.Run (C2.i_subst T (NNum n) (do_proj T i)) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T i ->
    T <> TID ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    unfold do_proj.
    intros.
    rewrite C2.i_subst_subst_trans in H1; auto.
    + eapply run_m_proj; eauto.
    + intros N.
      contradict H3.
      apply in_proj_to_in; auto.
  Qed.

  Variable t1_neq_tid: T1 <> TID.
  Variable t2_neq_tid: T2 <> TID.
  Variable t1_neq_t2: T1 <> T2.


  Lemma run_do_proj_do_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT ->
    n2 < TID_COUNT ->
    C2.Run
        (C2.i_subst T2 (NNum n1)
           (C2.i_subst T1 (NNum n2) (C2.seq (do_proj T1 i) (do_proj T2 i)))) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    prod (Hist.m_proj n2 hs2) (Hist.m_proj n1 hs2) = hs1.
  Proof.
    intros.
    rewrite C2.i_subst_seq in H2.
    rewrite C2.i_subst_seq in H2.
    apply C2.run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ C2.In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in.
    }
    assert (t2_nin_proj_i: ~ C2.In T2 (proj i)). {
      intros N.
      contradict H5.
      auto using in_proj_to_in.
    }
    (* Simplify Hra: *)
    assert (~ C2.In T2 (C2.i_subst T1 (NNum n2) (do_proj T1 i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto. {
        unfold do_proj in N.
        apply C2.in_i_subst_neq in N; auto.
        intros M.
        inversion M.
        subst.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hra; auto.
    eapply run_do_proj in Hra; eauto.
    subst.
    (* Simplify Hrb *)
    rewrite C2.i_subst_subst_neq in Hrb; auto.
    assert (~ C2.In T1 (C2.i_subst T2 (NNum n1) (do_proj T2 i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto. {
        unfold do_proj in N.
        apply C2.in_i_subst_neq in N; auto.
        intros M.
        inversion M.
        subst.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hrb; auto.
    eapply run_do_proj in Hrb; eauto.
    subst.
    reflexivity.
  Qed.

  (*
  Lemma run_proj_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT -> 
    n2 < TID_COUNT -> 
    C2.Run 
      (C2.i_subst T2 (NNum n2)
          (C2.i_subst T1 (NNum n1)
             (C2.seq (C2.i_subst TID (NVar T1) (proj i))
                     (C2.i_subst TID (NVar T2) (proj i))))) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    prod (Hist.m_proj n1 hs2) (Hist.m_proj n2 hs2) = hs1.
  Proof.
    intros.
    rewrite C2.i_subst_seq in H2.
    rewrite C2.i_subst_seq in H2.
    apply C2.run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ C2.In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in.
    }
    assert (t2_nin_proj_i: ~ C2.In T2 (proj i)). {
      intros N.
      contradict H5.
      auto using in_proj_to_in.
    }
    (* Simplify Hra: *)
    rewrite C2.i_subst_subst_trans in Hra; auto.
    assert (~ C2.In T2 (C2.i_subst TID (NNum n1) (proj i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto.
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hra; auto.
    eapply run_m_proj in Hra; eauto.
    subst.
    (* Simplify Hrb *)
    rewrite C2.i_subst_subst_neq in Hrb; auto.
    rewrite C2.i_subst_subst_trans in Hrb; auto.
    assert (~ C2.In T1 (C2.i_subst TID (NNum n2) (proj i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto.
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hrb; auto.
    eapply run_m_proj in Hrb; eauto.
    subst.
    reflexivity.
  Qed.
*)
  Lemma in_branch_inv:
    forall l hs x i1 i2,
    C2.Run (C2.Branch x l i1 i2) hs ->
    forall n,
    List.In n l ->
    exists hs2,
    incl hs2 hs /\ C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) hs2.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H0; subst; clear H0;
        inversion H; subst; clear H. {
      exists hs1.
      repeat split; auto using incl_app_refl_l.
    }
    assert (IHl := IHl hs2 x i1 i2 H8 _ H1).
    destruct IHl as (hs3, (Hinc, Hr)).
    exists hs3.
    split; auto.
    apply incl_appr.
    auto.
  Qed.

  Lemma in_decl_inv:
    forall e1 e2 hs x i1 i2,
    C2.Run (C2.Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    ((n1 >= n2 /\ C2.Run i2 hs)
    \/
    forall n,
    n1 <= n < n2 ->
    exists hs2,
    incl hs2 hs /\ C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) hs2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst.
    exists n1.
    exists n2.
    split; auto.
    split; auto.
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    intros.
    apply (Ha n) in H.
    eapply in_branch_inv in H6; eauto.
  Qed.


  Variable tid_ge_2: TID_COUNT > 2.

  Theorem a_pair_incl
      (i:C1.inst)
      (T1_nin_i: ~ C1.In T1 i)
      (T2_nin_i: ~ C1.In T2 i)
      (TID_nvar_i: ~ C1.Var TID i)
    :
    forall hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    C2.Run (translate i) hs2 ->
    Hist.APairIncl hs1 hs2.
  Proof.
    unfold translate.
    intros.
    unfold Hist.APairIncl.
    intros.
    apply C2.run_decl_inv in H1.
    destruct H1 as (n1, (n2, (Hn1, (Hn2, Hx)))).
    inversion Hn1; subst; clear Hn1.
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    subst.
    clear Hn2.
    destruct Hx as [(N,Hx)|(hss, (?, Hx))]. {
      Import Omega.
      omega.
    }
    subst.
    assert (x_lt_tc: access_tid x < TID_COUNT) by eauto.
    assert (y_lt_tc: access_tid y < TID_COUNT) by eauto.
    (* Check the tids of both accesses. *)
    assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
      by omega.
    destruct Ht as [Ht | [Ht|Ht]].
    - (* x = y *)
      omega.
    - (* x < y *)
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= access_tid y < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid y) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply C2.run_decl_inv in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid x < access_tid y) by omega.
      assert (Hx := Hx (access_tid x) Hb).
      destruct Hx as (hs, (Hx,Hz)).
      destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
        subst.
        contradiction.
      }
      (* Now we want to handle the seq in Hx *)
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto.
      subst.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
      apply m_pair_in_prod_2.
      + auto using Hist.in_m_proj.
      + auto using Hist.in_m_proj.
    - (* y < x *)
      Import Omega.
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= access_tid x < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid x) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply C2.run_decl_inv in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid y < access_tid x) by omega.
      assert (Hx := Hx (access_tid y) Hb).
      destruct Hx as (hs, (Hx,Hz)).
      destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
        subst.
        contradiction.
      }
      (* Now we want to handle the seq in Hx *)
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto.
      subst.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
      apply m_pair_in_prod_1.
      + auto using Hist.in_m_proj.
      + auto using Hist.in_m_proj.
  Qed.

  Ltac remove_eq ta tb :=
  destruct (Set_VAR.MF.eq_dec ta tb);
    try contradiction; simpl in *.

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
    rewrite access_subst_subst_neq in Hx; auto.
    rewrite access_subst_not_in with (x:=T2) in Hx; auto.
  Qed.

  Lemma m_in_prepend_iff:
    forall A x l ls,
    ls <> [] ->
    MIn (A:=A) x (prepend l ls) <-> (List.In x l \/ MIn x ls).
  Proof.
    intros.
    split; intros.
    - apply m_in_prepend_inv in H0.
      assumption.
    - destruct H0. {
        apply m_in_prepend_l; auto.
      }
      apply m_in_prepend; auto.
  Qed.

  Definition Member {A} l a := In (A:=A) a l.

  Inductive PMember {A : Type} {B: Type} (P: B -> list A -> Prop) (ls : B) (a:A)  : Prop :=
 | p_member_def :
    forall l,
    P ls l -> Member l a -> PMember P ls a.

  Definition MMember {A} := PMember (@Member (list A)).
  Definition MMMember {A} := PMember (@MMember (list A)).
  Lemma not_in_mmember:
    forall A (x:A),
    ~ MMember [] x.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    unfold Member in *.
    contradiction.
  Qed.

  Lemma not_in_mmmember:
    forall A (x:A),
    ~ MMMember [] x.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    apply not_in_mmember in H.
    assumption.
  Qed.

  Lemma mmember_app_l:
    forall A (x:A) l1 l2,
    MMember l1 x ->
    MMember (l1 ++ l2) x.
  Proof.
    unfold MMember.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    eapply p_member_def; eauto using in_or_app.
  Qed.

  Lemma mmember_app_r:
    forall A (x:A) l1 l2,
    MMember l2 x ->
    MMember (l1 ++ l2) x.
  Proof.
    unfold MMember.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    eapply p_member_def; eauto using in_or_app.
  Qed.

  Lemma mmember_def_2:
    forall A (x:A) l ls,
    In x l ->
    In l ls ->
    MMember ls x.
  Proof.
    intros.
    apply p_member_def with (l0:=l); auto.
  Qed.

  Lemma mmember_def:
    forall A (x:A) l ls,
    Member l x ->
    Member ls l ->
    MMember ls x.
  Proof.
    apply mmember_def_2.
  Qed.


  Lemma mmember_inv_app:
    forall A (x:A) l1 l2,
    MMember (l1 ++ l2) x ->
    MMember l1 x \/ MMember l2 x.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    apply in_app_or in H0.
    destruct H0. {
      left.
      eauto using mmember_def.
    }
    right.
    eauto using mmember_def.
  Qed.

  Lemma mmember_inv_concat:
    forall A (x:A) ls,
    MMember (List.concat ls) x ->
    exists l, List.In l ls /\ MMember l x.
  Proof.
    induction ls; simpl; intros.
    - apply not_in_mmember in H.
      contradiction.
    - apply mmember_inv_app in H.
      destruct H. {
        exists a.
        auto.
      }
      apply IHls in H.
      destruct H as (l, (Hi, Hm)).
      exists l.
      auto.
  Qed.

  Lemma mmmember_def:
    forall A (x:A) l1 l2 ls,
    Member l1 x ->
    Member l2 l1 ->
    Member ls l2 ->
    MMMember ls x.
  Proof.
    intros.
    apply p_member_def with (l:=l1); auto.
    eauto using mmember_def.
  Qed.

  Lemma mmmember_to_mmember:
    forall A ls (x:A),
    MMMember ls x ->
    MMember (List.concat ls) x.
  Proof.
    induction ls; intros.
    - apply not_in_mmmember in H.
      contradiction.
    - inversion H; subst; clear H.
      simpl.
      inversion H0; subst; clear H0.
      inversion H; subst; clear H. {
        apply mmember_app_l.
        eauto using mmember_def.
      }
      apply mmember_app_r.
      apply IHls.
      eauto using mmmember_def.
  Qed.

  Lemma mmmember_eq:
    forall A a x ls,
    @MMember A a x ->
    MMMember (a :: ls) x.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply mmmember_def with (l2:=a); eauto.
    apply in_eq.
  Qed.

  Lemma mmmember_cons:
    forall A a x ls,
    @MMMember A ls x ->
    MMMember (a :: ls) x.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply mmmember_def; eauto.
    apply in_cons; auto.
  Qed.

  Lemma mmember_to_mmmember:
    forall A ls (x:A),
    MMember (List.concat ls) x ->
    MMMember ls x.
  Proof.
    induction ls; intros. {
      apply not_in_mmember in H.
      contradiction.
    }
    simpl in *.
    apply mmember_inv_app in H.
    destruct H. {
      auto using mmmember_eq.
    }
    apply IHls in H.
    auto using mmmember_cons.
  Qed.

  Lemma mmember_iff_mmmember:
    forall A ls (x:A),
    MMember (List.concat ls) x <-> MMMember ls x.
  Proof.
    split; auto using mmember_to_mmmember, mmmember_to_mmember.
  Qed.


  Lemma mmember_concat_rw:
    forall A ls,
    Equiv (MMember (List.concat ls)) (@MMMember A ls).
  Proof.
    auto using equiv_def, mmmember_to_mmember, mmember_to_mmmember.
  Qed.

  Lemma mmember_rw:
    forall A ls (x:A),
    MMember ls x <-> MIn x ls.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      eauto using m_in_def.
    - inversion H; subst; clear H.
      eauto using mmember_def.
  Qed.

  Lemma mmember_prepend_iff:
    forall A l ls (x:A),
    ls <> [] ->
    MMember (prepend l ls) x <-> Member l x \/ MMember ls x.
  Proof.
    intros.
    repeat rewrite mmember_rw.
    apply m_in_prepend_iff; assumption.
  Qed.

  Lemma mmember_prepend_rw:
    forall A (l:list A) ls,
    ls <> [] ->
    Equiv (MMember (prepend l ls)) (Either (Member l) (MMember ls)).
  Proof.
    intros.
    apply equiv_def; intros a Ha.
    - apply mmember_prepend_iff in Ha; auto.
    - apply mmember_prepend_iff in Ha; auto.
  Qed.

  Lemma member_concat_rw:
    forall A ls,
    Equiv (Member (List.concat ls)) (@MMember A ls).
  Proof.
    intros.
    apply equiv_def; unfold Member; intros.
    - rewrite mmember_rw.
      auto using in_concat_to_m_in.
    - rewrite mmember_rw in *.
      auto using m_in_to_in_concat.
  Qed.

  Lemma incl_mmember_nil_nil:
    forall A P,
    @Incl A (MMember [[]]) P.
  Proof.
    intros.
    apply incl_def.
    intros.
    rewrite mmember_rw in H.
    apply m_in_nil_nil in H.
    contradiction.
  Qed.

  Lemma incl_mmember_nil:
    forall A P,
    @Incl A (MMember []) P.
  Proof.
    intros.
    apply incl_def.
    intros.
    rewrite mmember_rw in H.
    apply m_in_nil in H.
    contradiction.
  Qed.

  Lemma r_step_range_list:
    forall n1 n2,
    RStep (NNum n1, NNum n2) (range_list n1 n2).
  Proof.
    intros.
    remember (range_list _ _).
    apply r_step_def with (n1:=n1) (n2:=n2); auto using n_step_num.
    apply range_list_to_prop.
    auto.
  Qed.

  Lemma c2_branch:
    forall f l i1 i2 x hs hs',
    hs' = ((List.concat (List.map f l)) ++ hs) ->
    (forall n, List.In n l -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)) ->
    C2.Run i2 hs ->
    C2.Run (C2.Branch x l i1 i2) hs'.
  Proof.
    induction l; intros; subst.
    - simpl.
      apply C2.run_branch_nil; auto.
    - simpl.
      rewrite app_assoc_reverse.
      Search (_ ++ _ ++ _).
      apply C2.run_branch_cons. {
        auto using in_eq.
      }
      apply IHl with (hs:=hs); auto.
      intros.
      apply H0.
      auto using in_cons.
  Qed.

  Definition mk_empty_1 n1 n2 : list Hist.history :=
    List.concat (map (fun _ => [[]]) (range_list n1 n2)) ++ [[]].

  Lemma c2_decl_skip:
    forall n1 n2,
    C2.Run (C2.Decl T2 (NNum n1, NNum n2) C2.Skip C2.Skip) (mk_empty_1 n1 n2).
  Proof.
    intros.
    apply C2.run_decl with (l:=range_list n1 n2).
    - apply r_step_range_list.
    - apply c2_branch with (f:=fun x => [[]]) (hs:=[[]]).
      + reflexivity.
      + intros.
        simpl.
        apply C2.run_skip.
      + apply C2.run_skip.
  Qed.

  Definition mk_empty_2 n1 n2 : list Hist.history :=
    List.concat (map (fun n => mk_empty_1 0 n) (range_list n1 n2))
     ++ [[]].

  Lemma c2_run_skip:
    C2.Run (translate C1.Skip) (mk_empty_2 1 TID_COUNT).
  Proof.
    unfold translate.
    simpl.
    apply C2.run_decl with (l:=range_list 1 TID_COUNT).
    - apply r_step_range_list.
    - apply c2_branch with (f:=fun n => mk_empty_1 0 n) (hs:=[[]]).
      + reflexivity.
      + intros.
        simpl.
        remove_eq T1 T1.
        remove_eq T1 T2.
        apply c2_decl_skip.
      + apply C2.run_skip.
  Qed.

  Definition add {A:Type} f (a:nat) (v:A) :=
    (fun n => if Nat.eq_dec n a then v else f n).

  Lemma add_eq_rw:
    forall A f a (hs1:A),
    add f a hs1 a = hs1.
  Proof.
    unfold add; intros.
    destruct (Nat.eq_dec a a). {
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
    destruct (Nat.eq_dec b a). {
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
    assert (Hi : ~ In a l). {
      intros N.
      contradict H.
      auto using in_cons.
    }
    assert (IHl := IHl x Hi).
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma c2_run_branch_inv:
    forall l i1 i2 x hs',
    C2.Run (C2.Branch x l i1 i2) hs' ->
    NoDup l ->
    exists f hs,
    hs' = ((List.concat (List.map f l)) ++ hs) /\ C2.Run i2 hs
    /\
    (forall n, List.In n l -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)).
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

  Definition branch_iter n1 n2 f (hs: list Hist.history) :=
    List.concat (List.map f (range_list n1 n2)) ++ hs.


  Lemma c2_run_decl_inv:
    forall n1 n2 i1 i2 x hs',
    C2.Run (C2.Decl x (NNum n1, NNum n2) i1 i2) hs' ->
    exists f hs,
    hs' = branch_iter n1 n2 f hs /\
    C2.Run i2 hs /\
    (forall n, n1 <= n < n2 -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)).
  Proof.
    intros.
    unfold branch_iter.
    inversion H; subst; clear H.
    apply r_step_to_range_list in H5.
    subst.
    apply c2_run_branch_inv in H6.
    destruct H6 as (f, (hs1, (?, (Hr1, Hr2)))).
    subst.
    exists f.
    exists hs1.
    repeat split; auto.
    intros.
    apply Hr2.
    - apply range_list_in_iff; assumption.
    - auto using range_list_no_dup.
  Qed.

  Lemma c2_acc_inv:
    forall e hs,
    C2.Run (translate (C1.Acc e C1.Skip)) hs ->
    exists f1,
    hs = branch_iter 1 TID_COUNT f1 [[]]
    /\
    forall n1 n2,
      1 <= n1 < TID_COUNT ->
      0 <= n2 < n1 ->
      exists f2,
      f1 n1 = branch_iter 0 n1 f2 [[]] /\
      C2.Run
       (C2.Acc
          (access_subst T2 (NNum n2)
             (access_subst T1 (NNum n1) (access_subst TID (NVar T1) e)),
          NNum n1)
          (C2.Acc
             (access_subst T2 (NNum n2)
                (access_subst T1 (NNum n1) (access_subst TID (NVar T2) e)),
             NNum n2) C2.Skip)) (f2 n2)
   .
  Proof.
    intros.
    unfold translate in *.
    apply c2_run_decl_inv in H.
    destruct H as (f1, (hs1, (?, (Hr, Hf1)))).
    inversion Hr; subst; clear Hr.
    exists f1.
    split. {
      reflexivity.
    }
    intros.
    apply Hf1 in H; clear Hf1.
    apply C2.run_inv_seq in H.
    destruct H as (hsa, (hsb, (?, (Hr1, Hr2)))).
    inversion Hr2; subst; clear Hr2.
    rewrite prod_nil_nil_r in *.
    simpl in *.
    remove_eq T1 T1.
    remove_eq T1 T2.
    remove_eq TID TID.
    remove_eq T1 T1.
    remove_eq T1 T2.
    subst.
    Search (prod _ [[]]).
    apply c2_run_decl_inv in Hr1.
    destruct Hr1 as (f2, (?, (?, (?,?)))).
    inversion H1; subst; clear H1.
    exists f2.
    split; auto.
    apply H2 in H0.
    apply C2.run_inv_seq in H0.
    destruct H0 as (hsa, (hsb, (?,(Hr,Hs)))).
    inversion Hs; subst; clear Hs.
    rewrite prod_nil_nil_r in *.
    subst.
    simpl in *.
    remove_eq T2 T2.
    inversion Hr; subst; clear Hr.
    inversion H5; subst; clear H5.
    inversion H8; subst; clear H8.
    
  Qed.

  Lemma translate_acc_inv:
    forall e i hs,
    C2.Run (translate (C1.Acc e i)) hs ->
    exists hs1 hs2,
    hs = prod hs1 hs2 /\
    C2.Run (translate (C1.Acc e C1.Skip)) hs1 /\
    C2.Run (translate i) hs2.
  Proof.
    induction i; intros.
    - exists (prod hs (mk_empty_2 1 TID_COUNT)).
      exists (mk_empty_2 1 TID_COUNT).
      repeat split; auto using c2_run_skip.
      + 
      unfold translate in *.
      simpl in *.
      rewrite prod_nil_nil_r.
      repeat split; auto.
      unfold translate.
  Qed.

  Lemma all_incl_all
      (i:C1.inst)
      (T1_nin_i: ~ C1.In T1 i)
      (T2_nin_i: ~ C1.In T2 i)
      (TID_nvar_i: ~ C1.Var TID i)
    :
    forall hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    (forall x, MIn x hs2 -> access_tid x < TID_COUNT) ->
    C2.Run (translate i) hs2 ->
    Incl (MMember hs1) (MMember hs2).
  Proof.
    intros hs1 H.
    induction H; intros.
    - apply incl_mmember_nil_nil.
    - assert (Hx: hs = nil \/ hs <> nil). {
        destruct hs; auto.
        right.
        intros N.
        inversion N.
      }
      destruct Hx as [N|hs_not_nil]. {
        subst.
        simpl.
        apply incl_mmember_nil.
      }
      rewrite mmember_prepend_rw; auto.
      rewrite member_concat_rw.
      rewrite incl_l_either_iff.
      split. {
        clear IHRun. (* We don't need IHRun *)
        (* Show that all members of v are in hss *)
        (* 1. simplify defs *)
        apply incl_def; intros.
        rewrite mmember_rw in *.
        (* At this point we know that the access is in the output of 
             Hist.GenAccess TID e TID_COUNT v
           So, we need to find out which task has created it. *)
        apply Hist.m_in_gen_access_inv with (v0:=x) in H; auto.
        destruct H as (t, (vs, (Ht, (Ha, Hi)))).
        (* Knowing that some task performed the access, we need to
           figure out whether it was T1 or T2.
           If t = 0, then t = T2, otherwise t = T1. *)
        assert (Hd: t = 0 \/ 1 <= t) by omega.
        destruct Hd. {
          (* t = T2 *)
          (* In this case, we can pick any other task, say T1 = 1 *)
          give_up.
        }
        (* t = T1 *)
        (* In this case, we can pick any other task for T1 = 0 *)
        give_up.
      }
      (* Show that all members of hs are in hss *)
      (* We have that the access is in hs, so we must use the IH *)
      
      apply C2.run_decl_inv_in in H2.
      destruct H2 as [(N, _)|(hss, (Hr1, Hx))]. {
        omega.
      }
      rewrite Hr1 in *. (* subst removes this equation, which is needed *)
      rewrite mmember_concat_rw.
      Search (Incl (Either _ _ ) _).
      assert (Hx := Hx _ H3).
      destruct Hx as (hs3, (Hi, (Hmi, [Hz|(n,(Hle,Hx))]))). {
        inversion Hz; subst; clear Hz.
        apply m_in_nil_nil in Hmi.
        contradiction.
      }
      simpl in *.
      remove_eq T1 T1.
      remove_eq T1 T2.
      remove_eq TID TID.
      remove_eq T1 T1.
      Search (C2.Run (C2.Decl _ _ _ _ )).
      apply C2.run_decl_inv_in in Hx.
      destruct Hx as [(Hy,_)|Hy]. {
        omega.
      }
      destruct Hy as (hss2, (Hr2, Hy)).
      subst.
      assert (Hy := Hy _ Hmi).
      destruct Hy as (hs1, (?,(Hmj, Hy))).
      destruct Hy as [N|(?, (Hle2, Hy))]. {
        inversion N; subst; clear N.
        apply m_in_nil_nil in Hmj.
        contradiction.
      }
      simpl in *.
      apply C2.run_acc_inv_in with (a:=x) in Hy; auto.
      destruct Hy  as (hs', (w, (Hs, (?, Hx)))).
      subst.
      clear Hmj.
      destruct Hx as [Hx|Hx]. {
        (* x is in v *)
        apply m_in_prepend_l. {
          give_up.
        }
        apply access_step_subst_1 in Hs; auto.
        - apply Hist.access_step_to_gen_access with (m:=TID_COUNT) in Hs; auto with *.
          destruct Hs as (l, (Hj, Hs2)).
          assert (l = v) by eauto using Hist.gen_access_fun.
          subst.
          clear Hs2.
          apply m_in_to_in_concat.
          eauto using m_in_def.
        - give_up.
        - give_up.
      }
      (* x is in hs *)
      apply m_in_prepend.
      clear H3 Hi.
      clear Hmi.
       {
      }
      rewrite access_subst_subst_trans in Hy. {
        rewrite C2.i_subst_seq in Hy.
        rewrite C2.i_subst_subst_trans in Hy. {
          simpl in *.
          remove_eq TID TID.
          remove_eq T1 T2.
          simpl in *.
          Search access_subst.
          Search (C2.Run (C2.Acc _ _)).
          rewrite access_subst_subst_trans in Hy.
        }
      }
    intros.
    
    
    destruct H1 as [(N, _)|(hss, (?, Hx))]. {
      omega.
    }
    subst.
    assert (Hx := Hx _ H2).
    destruct Hx as (hs2, [(Hx,(Hy,Hz))|(n,Hy)]). {
      inversion Hz; subst; clear Hz.
      apply m_in_nil_nil in Hx.
      contradiction.
    }
    apply C2.run_inv_seq in Hy.
    destruct Hy as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    inversion Hrb; subst; clear Hrb.
    simpl in *.
    destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
    destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
      subst.
      contradiction.
    }
    apply C2.run_decl_inv_in in Hra.
    destruct Hra as [(?, N)|(hss1, (?, Hx))]. {
      assert (n = 0) by omega.
      subst.
      inversion N; subst; clear N.
      omega.
    }
    

    
    destruct H1 as (n1, (n2, (Hn1, (Hn2, Hx)))).
    assert (n1 = 1) by (inversion Hn1; auto); clear Hn1.
    subst.
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    assert (Hz: n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      auto.
    }
    subst.
    clear Hn2 Hz.
    destruct Hx as [(N,Hx)|(hs2_part, (?, Hx))]. {
      Import Omega.
      omega.
    }
    subst.
    assert (Hx := Hx _ H2).
    destruct Hx as (n, (hs, (Hr,Hi))).
    apply C2.run_inv_seq in Hr.
    destruct Hr as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    inversion Hrb; subst; clear Hrb.
    rewrite prod_nil_nil_r in *.
    simpl in *.
    apply C2.run_decl_inv_in in Hra.
    destruct Hra as (n1, (n2, (Hn1, (Hn2, Hx)))).
    inversion Hn1; subst; clear Hn1.
    assert (n2 = n). {
      inversion Hn2; subst; auto.
    }
    subst.
    inversion Hn2; subst; clear Hn2.
    destruct Hx as [(N,Hx)|(hs2_part1, (?, Hx))]. {
      inversion Hx; subst; clear Hx.
      assert (n = 0) by omega.
      subst.
    }


    
    Import Omega.
    assert (x_lt_tc: access_tid x < TID_COUNT) by auto with *.
    assert (Ht: access_tid x = 0 \/ access_tid x > 0)
      by omega.
    destruct Ht as [Ht | Ht]. {
      (* tid x = 0 *)
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= 1 < TID_COUNT) by omega.
      assert (Hx := Hx 1 Ha).
      destruct Hx as (hs, (Hx,Hy)).
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply C2.run_decl_inv in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(hs_1_x, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid x < 1) by omega.
      assert (Hx := Hx _ Hb).
      destruct Hx as (hs, (Hx,Hz)).
      destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
        subst.
        contradiction.
      }
      (* Now we want to handle the seq in Hx *)
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto with *.
      subst.
      inversion H2; subst; clear H2.
      Search List.concat.
      apply m_in_concat in H1.
      apply m_in_to_in_concat in H1.
      assert (MIn x  (prod (Hist.m_proj 1 hs1) (Hist.m_proj (access_tid x) hs1))). {
        apply m_in_prod_r.
        - give_up.
        - apply Hist.in_m_proj; auto.
          Search (MIn _ (Hist.m_proj _ _)).
        Search (MIn _ (prod _ _)).
        apply m_in_prod_inv.
      }
      assert (MIn x (List.concat hs_1_x)). {
        eapply m_in_def; eauto.
        - 
      }
      apply m_in_concat.

      apply in_concat_to_m_in.
      Search List.concat.
      apply in_concat_to_m_in in Hy.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
      apply m_pair_in_prod_2.
      + auto using Hist.in_m_proj.
      + auto using Hist.in_m_proj.
    }

    assert (Ha : 1 <= 1 < TID_COUNT) by auto with *.
    assert (Hx := Hx _ Ha).
    destruct Hx as (hs, (Hx,Hy)).
    apply C2.run_inv_seq in Hx.
    destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
    inversion Hr2; subst; clear Hr2.
    rewrite prod_nil_nil_r in *.
    simpl in *.
    destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
    apply C2.run_decl_inv in Hr1.
    destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* tid(y) = 0 /\ tid(y) > 0 *)
      omega.
    }
    inversion Hn1; subst; clear Hn1.
    inversion Hn2; subst; clear Hn2.
    (* Satisfy the outer forall and unpax the existential in Hx *)
    assert (Hb : 0 <= 0 < 1) by omega.
    assert (Hx := Hx _ Hb).
    destruct Hx as (hs, (Hx,Hz)).
    destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
      subst.
      contradiction.
    }
    (* Now we want to handle the seq in Hx *)
    apply C2.run_inv_seq in Hx.
    destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
    inversion Hr2; subst; clear Hr2.
    rewrite prod_nil_nil_r in *.
    eapply run_do_proj_do_proj in Hr1; eauto.
    subst.
    eapply m_pair_in_concat; eauto.
    eapply m_pair_in_concat; eauto.
    apply m_pair_in_prod_1.
    + auto using Hist.in_m_proj.
    + auto using Hist.in_m_proj.
  Qed.


  Variable tid_ge_2: TID_COUNT > 2.
  Variable in_heap: forall x i hs, C2.Run i hs -> MIn x hs -> access_tid x < TID_COUNT.
  Theorem correctness:
    forall i hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    C2.Run (translate i) hs2 ->
    Hist.MSafe hs1 ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    ~ C1.Var TID i -> 
    Hist.MSafeStrong hs2.
  Proof.
    Import Omega.
    intros.
    rename H2 into T1_nin_i.
    rename H3 into T2_nin_i. 
    rename H4 into TID_nvar_i.
    unfold Hist.MSafeStrong.
    intros.
    unfold translate, do_proj in *.
    apply Exists_exists in H2.
    destruct H2 as (l, (Hi, Hj)).
    (* Check the tids of both accesses. *)
    assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
      by omega.
    destruct Ht as [Ht | Ht]. {
      auto using access_safe_eq_tid.
    }
    assert (Horig := H0).
    (* Get the smallest task *)
    assert (Hx := in_decl_inv _ _ _ _ _ _ H0); clear H0.
    destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
      inversion Hn1; subst; clear Hn1.
      assert (n2 = TID_COUNT). {
        inversion Hn2; subst; clear Hn2.
        reflexivity.
      }
      subst.
      omega.
    }
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    clear Hn2.
    inversion Hn1; subst; clear Hn1.
    subst.
    (* Simplify the expression under Ha *)
    simpl in Ha.
    destruct (Set_VAR.MF.eq_dec T1 T1) as [e|e]; try contradiction; clear e.
    destruct (Set_VAR.MF.eq_dec T1 T2) as [e|e]; try contradiction; clear e.
    destruct Ht. {
      assert (Hlt:  1 <= access_tid y < TID_COUNT). {
        assert (access_tid y < TID_COUNT). {
          eapply in_heap; eauto.
          eapply m_in_def; eauto using pair_in_to_in_r.
        }
        omega.
      }
      assert (Ha := Ha (access_tid y) Hlt).
      destruct Ha as (hs3, (Hinc, Ha)).
      (* We have a run-object, now use in_decl_inv *)
      assert (Hx := in_decl_inv _ _ _ _ _ _ Ha); clear Ha.
      destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid y <= 0 /\ tid y >= 1 -> False *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      assert (Hlt2: 0 <= access_tid x < access_tid y) by omega.
      assert (Ha := Ha (access_tid x) Hlt2).
      destruct Ha as (hs4, (Hinc2, Ha)).
      apply C2.run_inv_seq in Ha.
      destruct Ha as (Ha_hs1, (Ha_hs2, (?, (Ha,Hb)))).
      subst.
      eapply run_proj_proj in Ha; eauto with *.
      subst.
      inversion Hb; subst; clear Hb.
      
    (*
    var tid, [tid] -> var tid, ([tid], tid) 
     *)

  Qed.

  End Defs.

Section Compiler.

Module Examples.
  Import Compiler.
  Import C2.

  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match C2.step s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.

  Fixpoint hists s :=
  match s with
  | Par (Leaf (h, i)) s2 => h :: hists s2
  | _ => []
  end.

  Definition run_h steps s := hists (snd (run steps s)).


  Definition HELLO1 n := Leaf ([],
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    )
    Skip
  ).

  Definition HELLO1_VAL t :=  Par (Leaf ([{| OneDim.tid := t; OneDim.index := 0 |}], Skip))
         (Par (Leaf ([{| OneDim.tid := t; OneDim.index := 1 |}], Skip))
          Empty).

  Goal snd (run 300 (HELLO1 (NNum 9))) = HELLO1_VAL 9.
    auto.
  Qed.

  Definition HELLO2 := Leaf ([],
    Decl (variable "tid") (NNum 0, NNum 2) (
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), (NVar (variable "tid"))) Skip
    ) Skip
    )
    Skip
  ).

  (**
  
    var t \in (0, 2) {
      var x \in (0, 2) {
        [x] by t
      }
    }
  
    *)

  
  Compute run 24 HELLO2.

  Infix "||" := Par.
  Notation "{}" := Empty.
  Notation "x 'by' y" := {| OneDim.tid := y; OneDim.index := x |} (at level 50, left associativity).


  Definition HELLO3 n := Leaf ([],
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    ) (Acc ((NNum 9, BBool true), NNum 9) Skip)
  ).
  
  Compute run 17 (HELLO3 (NNum 10)).


  Definition GOOD1 :=
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.GOOD1.

  Compute GOOD1.

  Definition body x :=
    Decl (variable "x") (NNum 0, NNum 2)
        (Acc (NVar (variable "x"), NRel NEq x (NVar (variable "x")), x) Skip) Skip.

  Compute Conc1.Examples.GOOD1.
  Compute GOOD1.

  Compute run_h 40 (Leaf ([], GOOD1)). (* 39 *)

  (* ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) *)

  Definition GOOD2 :=
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.GOOD2.

  Compute run 10 (Leaf ([], GOOD2)). (* 10 *)

  Definition BAD := 
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.BAD.
(*
  Compute BAD.
*)
  Compute (run_h 36 (Leaf ([], BAD))). (* 35 *)

  Compute hists (snd (run 36 (Leaf ([], BAD)))).
  (*
        [{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}]
  *)

End Examples.