Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Arith.PeanoNat.
Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Access.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Conc.
Require Import RangeList.
Require Import SetTh.
Require Import MultiHist.
Require Import InUtil.

Import ListNotations.

Section Defs.
  Context {A:Access}.

  Inductive inst :=
  | Skip
  | Acc: access_exp * nexp -> inst -> inst
  | Decl : var -> range -> inst -> inst -> inst
  | Branch : var -> list nat -> inst -> inst -> inst.

  Inductive Var (x:var) : inst -> Prop :=
  | var_acc:
    forall p i,
    Var x i ->
    Var x (Acc p i)
  | var_decl_eq:
    forall r i1 i2,
    Var x (Decl x r i1 i2)
  | var_decl_r:
    forall r y i1 i2,
    Var x i2 ->
    Var x (Decl y r i1 i2)
  | var_decl_l:
    forall r i1 i2 y,
    Var x i1 ->
    Var x (Decl y r i1 i2)
  | var_branch_eq:
    forall l i1 i2,
    Var x (Branch x l i1 i2)
  | var_branch_l:
    forall y i1 i2 l,
    Var x i1 ->
    Var x (Branch y l i1 i2)
  | var_branch_r:
    forall y i1 i2 l,
    Var x i2 ->
    Var x (Branch y l i1 i2).

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Acc (a, e) j => Acc (access_subst x v a, n_subst x v e) (i_subst x v j)  
  | Decl y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Decl y (r_subst x v r) i2' (i_subst x v i3)
  | Branch y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Branch y r i2' (i_subst x v i3)
  end.

  Fixpoint seq (i1 i2:inst) :=
  match i1 with
  | Skip => i2
  | Acc e i3 => Acc e (seq i3 i2)
  | Decl x r i3 i4 => Decl x r i3 (seq i4 i2)
  | Branch x r i3 i4 => Branch x r i3 (seq i4 i2)
  end.

  Notation history := (list access_val).

  Inductive Run: inst -> list history -> Prop :=
  | run_skip:
    Run Skip [[]]
  | run_access:
    forall i e v hs,
    access_step e v ->
    Run i hs ->
    Run (Acc e i) (prepend v hs)
  | run_decl:
    forall r l i1 i2 x hs,
    RStep r l ->
    Run (Branch x l i1 i2) hs ->
    Run (Decl x r i1 i2) hs
  | run_branch_cons:
    forall x n l i1 i2 hs1 hs2,
    Run (seq (i_subst x (NNum n) i1) i2) hs1 ->
    Run (Branch x l i1 i2) hs2 ->
    Run (Branch x (n::l) i1 i2) (hs1 ++ hs2)
  | run_branch_nil:
    forall x i1 i2 hs,
    Run i2 hs ->
    Run (Branch x [] i1 i2) hs.

  Inductive DoLoop : var -> list nat -> inst -> inst -> list (list history) -> Prop :=
  | do_loop_nil:
    forall i1 i2 x hs,
    Run i2 hs ->
    DoLoop x [] i1 i2 [hs]
  | do_loop_cons:
    forall x n l i1 i2 hss hs,
    Run (seq (i_subst x (NNum n) i1) i2) hs ->
    DoLoop x l i1 i2 hss ->
    DoLoop x (n::l) i1 i2 (hs::hss).

  Let run_branch_to_do_loop:
    forall x l i1 i2 hs,
    Run (Branch x l i1 i2) hs ->
    exists hss, hs = List.concat hss /\ DoLoop x l i1 i2 hss.
  Proof.
    intros.
    remember (Branch _ _ _ _).
    generalize dependent x.
    generalize dependent i1.
    generalize dependent i2.
    generalize dependent l.
    induction H; intros; inversion Heqi; subst; clear Heqi. {
      assert (IHRun2 := IHRun2 _ _ _ _ eq_refl).
      destruct IHRun2 as (hss, (?, Hd)).
      exists (hs1::hss).
      split. {
        simpl.
        subst.
        auto.
      }
      apply do_loop_cons; auto.
    }
    exists [hs].
    simpl.
    split. {
      auto with *.
    }
    auto using do_loop_nil.
  Qed.

  Let do_loop_inv_1:
    forall x l i1 i2 hss,
    DoLoop x l i1 i2 hss ->
    forall n,
    List.In n l ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      exists hs.
      auto using List.in_eq.
    }
    eapply IHl in H8; eauto.
    destruct H8 as (hs', (Hi,Hj)).
    eauto using in_cons.
  Qed.

  Let do_loop_inv_2:
    forall x l i1 i2 hss,
    DoLoop x l i1 i2 hss ->
    forall a,
    MIn a (List.concat hss) ->
    exists hs,
    MIn a hs /\
    List.In hs hss /\
    (
      Run i2 hs \/
      (exists n, List.In n l /\ Run (seq (i_subst x (NNum n) i1) i2) hs)
    ).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      simpl in H0.
      rewrite app_nil_r in *.
      exists hs.
      split; auto using in_eq.
    }
    inversion H; subst; clear H.
    simpl in *.
    apply m_in_inv_app in H0.
    destruct H0 as [Hx|Hx]. {
      exists hs.
      split; auto.
      split; intuition.
      right.
      eauto.
    }
    eapply IHl in Hx; eauto.
    destruct Hx as (hs', (?, (?,Hx))).
    destruct Hx as [Hx|(n, (?,?))].
    - exists hs'.
      eauto.
    - exists hs'.
      repeat split; auto.
      right.
      exists n.
      split; auto.
  Qed.

  Let run_branch_inv_in:
    forall x l i1 i2 hs,
    Run (Branch x l i1 i2) hs ->
    exists hss, hs = List.concat hss /\
    forall a,
    MIn a (List.concat hss) ->
    exists hs,
    MIn a hs /\
    List.In hs hss /\
    (
      Run i2 hs \/
      (exists n, List.In n l /\ Run (seq (i_subst x (NNum n) i1) i2) hs)
    ).
  Proof.
    intros.
    apply run_branch_to_do_loop in H.
    destruct H as (hss, (?, Ha)).
    eauto.
  Qed.

  Let run_branch_inv:
    forall x l i1 i2 hs,
    Run (Branch x l i1 i2) hs ->
    exists hss, hs = List.concat hss /\
    forall n,
    List.In n l ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss.
  Proof.
    intros.
    apply run_branch_to_do_loop in H.
    destruct H as (hss, (?, Ha)).
    exists hss.
    split; auto.
    intros.
    eapply do_loop_inv_1; eauto.
  Qed.

  Lemma run_decl_inv:
    forall x e1 e2 i1 i2 hs,
    Run (Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\ (
    (n1 >= n2 /\ Run i2 hs)
    \/
    (
    exists hss, hs = List.concat hss /\
    forall n,
    n1 <= n < n2 ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss)
     ).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst.
    exists n1.
    exists n2.
    repeat (split; auto).
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    apply run_branch_inv in H6.
    destruct H6 as (hss, (?, Hc)).
    exists hss.
    split; auto.
    intros.
    apply (Ha n) in H0.
    apply Hc in H0.
    assumption.
  Qed.

  Lemma run_decl_inv_eq:
    forall x n1 n2 i1 i2 hs,
    n1 < n2 ->
    Run (Decl x (NNum n1, NNum n2) i1 i2) hs ->
    exists hss, hs = List.concat hss /\
    forall n,
    n1 <= n < n2 ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss
    .
  Proof.
    intros.
    apply run_decl_inv in H0.
    destruct H0 as (n3, (n4, (Hn3, (Hn4, [(N,_)|(hss, (?, Hx))])))). {
      inversion Hn3; subst.
      inversion Hn4; subst.
      apply Lt.le_not_lt in N.
      contradiction.
    }
    exists hss.
    inversion Hn3; subst; clear Hn3.
    inversion Hn4; subst; clear Hn4.
    split; auto.
  Qed.

  Lemma run_acc_inv_in:
    forall e i hs a,
    Run (Acc e i) hs ->
    MIn a hs ->
    exists hs' v,
    access_step e v /\
    hs = prepend v hs' /\
    ( 
      List.In a v
      \/
      MIn a hs'
    ).
  Proof.
    intros.
    inversion H; subst; clear H.
    exists hs0.
    exists v.
    apply m_in_prepend_inv in H0.
    destruct H0. {
      auto.
    }
    auto.
  Qed.

  Lemma run_decl_inv_in:
    forall x n1 n2 i1 i2 hs,
    Run (Decl x (NNum n1, NNum n2) i1 i2) hs ->
    (
    (n1 >= n2 /\ Run i2 hs)
    \/
    (
    exists hss, hs = List.concat hss /\
    forall a,
    MIn a (List.concat hss) ->
    exists hs1,
    List.In hs1 hss /\
    MIn a hs1 /\
    (
      Run i2 hs1 
      \/
      (exists n, n1 <= n < n2 /\ Run (seq (i_subst x (NNum n) i1) i2) hs1)
    )
  )).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst; clear H5.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    assert (Hy := H6).
    apply run_branch_inv_in in H6.
    destruct H6 as (hss, (Hi, Hx)).
    subst.
    inversion H4; subst; clear H4. {
      left.
      split; auto.
      inversion Hy; subst; clear Hy.
      assumption.
    }
    simpl in *.
    right.
    exists hss.
    split; auto.
    intros.
    apply Hx in H1; clear Hx.
    destruct H1 as (hs, (Hi, (Hii, Hx))).
    destruct Hx as [Hx|(n, (Hj, Hx))].
    - eauto.
    - exists hs.
      repeat split; auto.
      right.
      destruct Hj. {
        subst.
        exists n.
        auto.
      }
      exists n.
      assert (S n0 <= n < n3) by eauto using range_list_inv_in.
      auto with *.
  Qed.

  Lemma seq_inv_skip:
    forall i1 i2,
    seq i1 i2 = Skip ->
    i1 = Skip /\ i2 = Skip.
  Proof.
    intros.
    destruct i1; simpl in *; subst; auto;
    inversion H.
  Qed.

  Lemma seq_seq_rw:
    forall i1 i2 i3,
    seq (seq i1 i2) i3 = (seq i1 (seq i2 i3)).
  Proof.
    induction i1; intros; simpl in *.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite <- IHi1_2.
      reflexivity.
    - rewrite <- IHi1_2.
      reflexivity.
  Qed.

  Lemma seq_nil_rw:
    forall i,
    seq i Skip = i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
  Qed.

  Lemma run_seq:
    forall i1 hs1,
    Run i1 hs1 ->
    forall i2 hs2,
    Run i2 hs2 ->
    Run (seq i1 i2) (prod hs1 hs2).
  Proof.
    intros i1 hs1 H.
    induction H; intros.
    - simpl.
      rewrite prepend_nil.
      rewrite app_nil_r.
      assumption.
    - assert (Hx := IHRun _ _ H1).
      simpl.
      rewrite <- prepend_prod.
      apply run_access; auto.
    - apply IHRun in H1.
      simpl.
      eapply run_decl; eauto.
    - rewrite <- prod_app.
      simpl.
      apply run_branch_cons; eauto.
      remember (i_subst _ _ _).
      assert (Hx := IHRun1 _ _ H1).
      rewrite seq_seq_rw in *.
      assumption.
    - simpl.
      apply run_branch_nil.
      auto.
  Qed.

  Lemma run_fun:
    forall i hs1,
    Run i hs1 ->
    forall hs2, Run i hs2 ->
    hs1 = hs2.
  Proof.
    intros i hs1 H.
    induction H; intros.
    - inversion H; subst; clear H; auto.
    - inversion H1; subst; clear H1.
      erewrite IHRun; eauto.
      assert (v0 = v) by eauto using access_step_fun.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun; eauto.
      subst.
      erewrite IHRun; eauto.
    - inversion H1; subst; clear H1.
      erewrite IHRun1; eauto.
      erewrite IHRun2; eauto.
    - inversion H0; subst; clear H0.
      eauto.
  Qed.

  Ltac run_clean :=
    repeat match goal with
    | [ H: Run [] _ |- _ ] => inversion H; subst; clear H
    | [ H: Hist.Safe [] |- _ ] => clear H
    | [ H: Run [Skip] _ |- _ ] => inversion H; subst; clear H
    | [ H: Run _ _ Skip _ |- _] => inversion H; subst; clear H
    | [ H1: access_step ?e ?v1,
        H2: access_step ?e ?v2 |- _ ] =>
          let H := fresh in
          assert (H: v2 = v1) by eauto using access_step_fun;
          rewrite H in *; clear H;
          clear H1
    | [ H1: RStep ?r ?l1,
        H2:RStep ?r ?l2 |- _ ] =>
          let H := fresh in
          assert (H: l2 = l1) by eauto using r_step_fun;
          rewrite H in *; clear H;
          clear H1
    end.

  Lemma run_inv_seq_1:
    forall i1 hs1,
    Run i1 hs1 ->
    forall i2 hs2 hs,
    Run i2 hs2 ->
    Run (seq i1 i2) hs ->
    hs = prod hs1 hs2.
  Proof.
    intros i1 hs1 H.
    induction H; intros; simpl in *.
    - rewrite prepend_nil.
      rewrite app_nil_r.
      eapply run_fun; eauto.
    - inversion H2; subst; clear H2.
      run_clean.
      apply IHRun with (hs2:=hs2) in H7; auto.
      subst.
      rewrite prepend_prod.
      reflexivity.
    - inversion H2; subst; clear H2.
      run_clean.
      apply IHRun with (hs2:=hs2) in H9; auto.
    - inversion H2; subst; clear H2.
      assert (IHRun2 := IHRun2 _ _ _ H1 H10); subst.
      rewrite <- seq_seq_rw in H9.
      assert (IHRun1 := IHRun1 _ _ _ H1 H9).
      subst.
      rewrite <- prod_app.
      reflexivity.
    - inversion H1; subst; clear H1.
      eapply IHRun in H6; eauto.
  Qed.

  Lemma run_inv_seq_2:
    forall i1 i2 hs,
    Run (seq i1 i2) hs ->
    exists hs1 hs2, Run i1 hs1 /\ Run i2 hs2.
  Proof.
    intros i1 i2 hs H.
    remember (seq _ _) as i.
    generalize dependent i1.
    generalize dependent i2.
    induction H; intros; symmetry in Heqi.
    - apply seq_inv_skip in Heqi.
      destruct Heqi.
      subst.
      exists [[]].
      exists [[]].
      split; auto using run_skip.
    - destruct i1; simpl in *; try inversion Heqi; subst; try clear Heqi.
      + exists [[]].
        exists (prepend v hs).
        split; auto using run_skip, run_access.
      + edestruct IHRun as (hs1, (hs2, (?, ?))); eauto.
        exists (prepend v hs1).
        exists hs2.
        split; auto using run_access.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; eauto using run_skip, run_decl.
      }
      destruct (IHRun i0 (Branch x l i1 i3_2) eq_refl) as (hs1, (hs2, (Hr1, Hr2)));
      clear IHRun.
      exists hs1.
      exists hs2.
      split; eauto using run_decl.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        clear H1.
        exists [[]].
        exists (hs1 ++ hs2).
        split; auto using run_skip.
        apply run_branch_cons; auto.
      }
      remember (i_subst _ _ _).
      destruct (IHRun1 i0 (seq i i3_2)) as (hsa, (hsb, (Hr1, Hr2))). {
        rewrite seq_seq_rw.
        reflexivity.
      }
      clear IHRun1.
      destruct (IHRun2 i0 (Branch x l i1 i3_2) eq_refl) as (hsa1, (hsb1, (Hra, Hrb))).
      assert (hsb = hsb1) by eauto using run_fun.
      clear Hrb.
      exists (hsa ++ hsa1).
      exists hsb.
      subst.
      split; auto using run_branch_cons.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; auto using run_skip, run_branch_nil.
      }
      destruct (IHRun _ _ eq_refl) as (hs1, (hs2, (?, ?))).
      exists hs1.
      exists hs2.
      split; auto using run_branch_nil.
  Qed.

  Lemma run_inv_seq:
    forall i1 i2 hs,
    Run (seq i1 i2) hs ->
    exists hs1 hs2, hs = prod hs1 hs2 /\ Run i1 hs1 /\ Run i2 hs2.
  Proof.
    intros.
    destruct (run_inv_seq_2 i1 i2 hs) as (hs1, (hs2, (Hr1, Hr2))); auto.
    assert (hs = prod hs1 hs2). {
      eauto using run_inv_seq_1.
    }
    subst.
    exists hs1, hs2.
    repeat split; auto.
  Qed.

  Lemma i_subst_seq:
    forall x v i1 i2,
    i_subst x v (seq i1 i2) = seq (i_subst x v i1) (i_subst x v i2).
  Proof.
    induction i1; simpl; intros.
    - reflexivity.
    - destruct p as (a, e).
      simpl.
      rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - destruct p.
      simpl.
      rewrite access_subst_subst_eq.
      rewrite IHi.
      rewrite n_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      rewrite r_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        rewrite IHi2.
        subst.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - destruct p.
      simpl.
      rewrite IHi; auto.
      rewrite n_subst_subst_neq; auto.
      rewrite access_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
      rewrite r_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        destruct (Set_VAR.MF.eq_dec x v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
  Qed.

  Inductive In (x:var) : inst -> Prop :=
  | in_acc_1:
    forall e n i,
    access_in x e ->
    In x (Acc (e, n) i)
  | in_acc_2:
    forall e n i,
    NIn x n ->
    In x (Acc (e, n) i)
  | in_acc_3:
    forall e n i,
    In x i ->
    In x (Acc (e, n) i)
  | in_decl_1:
    forall r i1 i2 y,
    RIn x r ->
    In x (Decl y r i1 i2)
  | in_decl_2:
    forall r i1 i2,
    In x (Decl x r i1 i2)
  | in_decl_3:
    forall r i1 i2 y,
    In x i1 ->
    In x (Decl y r i1 i2)
  | in_decl_4:
    forall r i1 i2 y,
    In x i2 ->
    In x (Decl y r i1 i2)
  | in_branch_1:
    forall l i1 i2,
    In x (Branch x l i1 i2)
  | in_branch_2:
    forall l y i1 i2,
    In x i1 ->
    In x (Branch y l i1 i2)
  | in_branch_3:
    forall l y i1 i2,
    In x i2 ->
    In x (Branch y l i1 i2).

  Lemma not_in_acc:
    forall x a n i,
    ~ In x (Acc (a, n) i) ->
    ~ In x i /\ ~ access_in x a /\ ~ NIn x n.
  Proof.
    intros.
    repeat split; intros N; contradict H;
      auto using in_acc_1, in_acc_2, in_acc_3.
  Qed.

  Lemma not_in_decl:
    forall x y r i1 i2,
    ~ In x (Decl y r i1 i2) ->
    x <> y /\ ~ RIn x r /\ ~ In x i1 /\ ~ In x i2.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst;
      auto using in_decl_1, in_decl_2, in_decl_3, in_decl_4.
  Qed.

  Lemma not_in_branch:
    forall x y r i1 i2,
    ~ In x (Branch y r i1 i2) ->
    x <> y /\ ~ In x i1 /\ ~ In x i2.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst;
      auto using in_branch_1, in_branch_2, in_branch_3.
  Qed.

  Lemma i_subst_not_in:
    forall i x v,
    ~ In x i ->
    i_subst x v i = i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - destruct p.
      apply not_in_acc in H.
      destruct H as (H0, (H1, H2)).
      rewrite access_subst_not_in; auto.
      rewrite n_subst_not_in; auto.
      rewrite IHi; auto.
    - apply not_in_decl in H.
      destruct H as (H, (H1, (H2, H3))).
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      rewrite r_subst_not_in; auto.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - apply not_in_branch in H.
      destruct H as (H, (H1, H2)).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma i_subst_subst_trans:
    forall i x y v,
    ~ In x i ->
    i_subst x v (i_subst y (NVar x) i) =
    i_subst y v i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - destruct p.
      simpl.
      apply not_in_acc in H.
      destruct H as (H1, (H2, H3)).
      rewrite IHi; auto.
      rewrite access_subst_subst_trans; auto.
      rewrite n_subst_subst_trans; auto.
    - apply not_in_decl in H.
      destruct H as (H0, (H1, (H2, H3))).
      rewrite r_subst_subst_trans; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite IHi2; auto.
        rewrite i_subst_not_in; auto.
      }
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - apply not_in_branch in H.
      destruct H as (H, (H1, H2)).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite i_subst_not_in; auto.
        rewrite IHi2; auto.
      }
      rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma in_i_subst_neq:
    forall i x y v,
    In x (i_subst y v i) ->
    x <> y ->
    ~ NIn x v ->
    In x i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - destruct p.
      inversion H; subst; clear H.
      + apply access_in_subst_neq in H3; auto using in_acc_1.
      + apply in_n_subst_neq in H3; auto using in_acc_2.
      + apply IHi in H3; auto using in_acc_3.
    - inversion H; subst; clear H.
      + apply in_r_subst_neq in H3; auto using in_decl_1.
      + auto using in_decl_2.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto using in_decl_3.
        }
        apply IHi1 in H3; auto using in_decl_3.
      + apply IHi2 in H3; auto using in_decl_4.
    - inversion H; subst; clear H.
      + auto using in_branch_1.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto using in_branch_2.
        }
        apply IHi1 in H3; auto using in_branch_2.
      + apply IHi2 in H3; auto using in_branch_3.
  Qed.

  Lemma in_subst_inv_in:
    forall e x y z,
    x <> y ->
    x <> z ->
    In x (i_subst z (NVar y) e) ->
    In x e.
  Proof.
    intros.
    apply in_i_subst_neq in H1; auto.
    intros N.
    inversion N; subst; clear N.
    contradiction.
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
    - 
      apply prepend_inv_nil in Heql.
      auto.
    - apply IHRun in Heql.
      assumption.
    - apply IHRun2.
      destruct hs2. {
        reflexivity.
      }
      destruct hs1;
        inversion Heql.
    - auto.
  Qed.


  (* ------------------------------------------------------------ *)

  Lemma run_branch_seq_skip:
    forall x i1 m1 r,
    Run (Branch x r i1 Skip) m1 ->
    forall i2 m2,
    Run i2 m2 ->
    Run (Branch x r i1 i2) (prod m1 m2).
  Proof.
    intros x i1 m1 r H.
    remember (Branch _ _ _ _).
    generalize dependent Heqi.
    generalize dependent x.
    generalize dependent r.
    generalize dependent i1.
    induction H; intros; inversion Heqi; subst; clear Heqi.
    - rewrite seq_nil_rw in *.
      assert (IHRun2 := IHRun2 _ _ _ eq_refl _ _ H1).
      rewrite <- prod_app.
      apply run_branch_cons.
      + auto using run_seq.
      + eauto.
    - apply run_branch_nil.
      inversion H; subst; clear H.
      rewrite prod_nil_nil_l.
      assumption.
  Qed.

  Lemma run_decl_seq_skip:
    forall x r i1 i2 m1 m2,
    Run (Decl x r i1 Skip) m1 ->
    Run i2 m2 ->
    Run (Decl x r i1 i2) (prod m1 m2).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply run_decl with (l:=l); auto using run_branch_seq_skip.
  Qed.

  Inductive BranchMap x i: list nat -> list (list history) -> Prop :=
  | branch_map_nil:
    BranchMap x i [] []
  | branch_map_cons:
    forall n l hss hs,
    Run (i_subst x (NNum n) i) hs ->
    BranchMap x i l hss ->
    BranchMap x i (n::l) (hs::hss).

  Definition Iter x i n h : Prop :=
    Run (i_subst x (NNum n) i) h.  

  Lemma branch_map_to_map:
    forall x i l m,
    BranchMap x i l m ->
    NoDup l ->
    Map (Iter x i) l m.
  Proof.
    intros x i l m Hb.
    induction Hb; intros. {
      apply map_nil.
    }
    inversion H0; subst; clear H0.
    apply map_cons; auto.
  Qed.

  Lemma map_to_branch_map:
    forall x i l m,
    Map (Iter x i) l m ->
    BranchMap x i l m.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      apply branch_map_nil.
    }
    inversion H; subst; clear H.
    eauto using branch_map_cons.
  Qed.

  Lemma branch_map_in:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n,
    List.In n l ->
    exists h, List.In (n, h) (List.combine l hss).
  Proof.
    induction l; intros. {
      contradiction.
    }
    destruct H0 as [Ha|Hi]; inversion H; subst; clear H. {
      simpl.
      eauto.
    }
    eapply IHl in H4; eauto.
    destruct H4 as (h, Hj).
    eauto using in_cons.
  Qed.

  Lemma branch_map_pair_in_to_run:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n h,
    List.In (n, h) (List.combine l hss) ->
    Run (i_subst x (NNum n) i) h.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H; subst; clear H.
    destruct H0 as [Hx|Hx]. {
      inversion Hx; subst; clear Hx.
      assumption.
    }
    eauto.
  Qed.

  Lemma branch_map_to_run:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n,
    List.In n l ->
    exists hs, Run (i_subst x (NNum n) i) hs.
  Proof.
    intros.
    eapply branch_map_in in H0; eauto.
    destruct H0 as (h, Hi).
    eauto using branch_map_pair_in_to_run.
  Qed.

  Lemma branch_map_def:
    forall x i l f,
    (forall n, List.In n l -> Run (i_subst x (NNum n) i) (f n)) ->
    BranchMap x i l (map f l).
  Proof.
    induction l; intros.
    - apply branch_map_nil.
    - apply branch_map_cons.
      + auto using in_eq.
      + apply IHl; auto using in_cons.
  Qed.

  Definition ProgImpl i j : Prop :=
    forall m1,
    Run i m1 ->
    exists m2,
    Run j m2 /\ MemEquiv m1 m2.

  Lemma prog_impl_def:
    forall i j,
    (forall m1, Run i m1 -> exists m2, Run j m2 /\ MemEquiv m1 m2) ->
    ProgImpl i j.
  Proof.
    intros.
    unfold ProgImpl.
    apply H.
  Qed.

  Lemma prog_impl_refl:
    forall i,
    ProgImpl i i.
  Proof.
    unfold ProgImpl.
    intros.
    exists m1.
    split; auto.
    reflexivity.
  Qed.

  Lemma prog_impl_trans:
    forall i j k,
    ProgImpl i j ->
    ProgImpl j k ->
    ProgImpl i k.
  Proof.
    unfold ProgImpl.
    intros.
    apply H in H1.
    destruct H1 as (m2, (Hj, R1)).
    apply H0 in Hj.
    destruct Hj as (m3, (Hk, R2)).
    exists m3.
    split; auto; etransitivity; eauto.
  Qed.


  (** Register [ProgImpl] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgImpl
    reflexivity proved by prog_impl_refl
    transitivity proved by prog_impl_trans
    as prog_impl_setoid.

  Definition ProgEquiv i j : Prop :=
    ProgImpl i j /\ ProgImpl j i.

  Lemma prog_equiv_def:
    forall i j,
    ProgImpl i j ->
    ProgImpl j i ->
    ProgEquiv i j.
  Proof.
    split; auto.
  Qed.

  Lemma run_prog_equiv_inv_l:
    forall i m1 j,
    Run i m1 ->
    ProgEquiv i j ->
    exists m2, Run j m2 /\ MemEquiv m1 m2.
  Proof.
    intros.
    destruct H0 as (Hr1, Hr2).
    apply Hr1 in H.
    assumption.
  Qed.

  Lemma run_prog_equiv_inv_r:
    forall i m1 j,
    Run j m1 ->
    ProgEquiv i j ->
    exists m2, Run i m2 /\ MemEquiv m1 m2.
  Proof.
    intros.
    destruct H0 as (Hr1, Hr2).
    apply Hr2 in H.
    assumption.
  Qed.

  Lemma prog_equiv_refl:
    forall i,
    ProgEquiv i i.
  Proof.
    intros.
    unfold ProgEquiv.
    auto using prog_impl_refl.
  Qed.

  Lemma prog_equiv_sym:
    forall i j,
    ProgEquiv i j ->
    ProgEquiv j i.
  Proof.
    unfold ProgEquiv.
    intros.
    destruct H.
    split; auto.
  Qed.

  Lemma prog_equiv_trans:
    forall i j k,
    ProgEquiv i j ->
    ProgEquiv j k ->
    ProgEquiv i k.
  Proof.
    unfold ProgEquiv; split.
    - destruct H, H0.
      transitivity j; auto.
    - destruct H, H0.
      transitivity j; auto.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgEquiv
    reflexivity proved by prog_equiv_refl
    symmetry proved by prog_equiv_sym
    transitivity proved by prog_equiv_trans
    as prog_equiv_setoid.

  Lemma branch_map_rw:
    forall l i j x hss,
    (forall n, List.In n l ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    BranchMap x i l hss ->
    exists hss',
    BranchMap x j l hss' /\
    MMEquivStruct hss hss'.
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0.
      exists [].
      split. {
        apply branch_map_nil.
      }
      apply mmequiv_struct_nil.
    }
    inversion H0; subst; clear H0.
    assert (hi: List.In a (a :: l)) by eauto using in_eq.
    assert (Hx := H _ hi); clear hi.
    assert (Hy: forall n : nat,
       List.In n l -> ProgEquiv (i_subst x (NNum n) i) (i_subst x (NNum n) j)) by auto using in_cons.
    assert (IHl := IHl i j x hss0 Hy H5).
    destruct IHl as (m1, (Hb, Hm)).
    unfold ProgEquiv in Hx.
    eapply run_prog_equiv_inv_l in H3; eauto.
    destruct H3 as (ma, (Hr1, R)).
    exists (ma::m1).
    simpl.
    split. {
      apply branch_map_cons; auto.
    }
    apply mmequiv_struct_cons; auto.
  Qed.


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
    intros B n f.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    assert (n <> a). {
      intros N.
      subst.
      contradict H.
      auto using in_eq.
    }
    rewrite add_neq_rw; auto.
    assert (Hi : ~ List.In n l). {
      intros N.
      contradict H.
      auto using in_cons.
    }
    assert (IHl := IHl x Hi).
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma branch_map_inv:
    forall x i l hss,
    BranchMap x i l hss ->
    NoDup l ->
    exists f, hss = map f l /\
    (forall n, List.In n l -> Run (i_subst x (NNum n) i) (f n)).
  Proof.
    intros.
    induction H.
    + exists (fun n => []).
      split; auto.
      intros.
      contradiction.
    + inversion H0; subst; clear H0.
      destruct IHBranchMap as (f, (?, Hf)); auto.
      exists (add f n hs).
      subst.
      simpl.
      split. {
        subst.
        rewrite add_eq_rw.
        rewrite map_add_rw_not_in; auto.
      }
      intros.
      destruct H0. {
        subst.
        rewrite add_eq_rw.
        assumption.
      }
      assert (Hf := Hf _ H0).
      rewrite add_neq_rw; auto.
      intros N.
      subst.
      contradiction.
  Qed.

  Lemma run_branch_map:
    forall l i1 i2 x hs hss hs',
    hs' = prod (List.concat hss) hs ++ hs  ->
    BranchMap x i1 l hss ->
    Run i2 hs ->
    Run (Branch x l i1 i2) hs'.
  Proof.
    induction l; intros; subst; inversion H0; subst; clear H0.
    - apply run_branch_nil; auto.
    - apply IHl with (i2:=i2) (hs:=hs) (hs':=prod (List.concat hss0) hs ++ hs) in H5; eauto.
      simpl.
      rewrite <- prod_app.
      rewrite app_assoc_reverse.
      apply run_branch_cons.
      + apply run_seq; auto using in_eq.
      + eauto using in_cons.
  Qed.

  Lemma run_branch_map_def:
    forall f l i1 i2 x hs hs',
    hs' = prod (List.concat (List.map f l)) hs ++ hs  ->
    (forall n, List.In n l -> Run (i_subst x (NNum n) i1) (f n)) ->
    Run i2 hs ->
    Run (Branch x l i1 i2) hs'.
  Proof.
    intros.
    eapply run_branch_map; eauto using branch_map_def.
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

  Definition DeclMap x i n1 n2 hss := BranchMap x i (range_list n1 n2) hss.

  Lemma decl_map_to_map:
    forall x i n1 n2 hss,
    DeclMap x i n1 n2 hss ->
    Map (Iter x i) (range_list n1 n2) hss.
  Proof.
    unfold DeclMap.
    intros.
    apply branch_map_to_map in H; auto using range_list_no_dup.
  Qed.

  Lemma decl_map_from_map:
    forall x i n1 n2 hss, 
    Map (Iter x i) (range_list n1 n2) hss ->
    DeclMap x i n1 n2 hss.
  Proof.
    intros.
    unfold DeclMap.
    auto using map_to_branch_map.
  Qed.

  Lemma decl_map_iff_map:
    forall x i n1 n2 hss,
    DeclMap x i n1 n2 hss <-> Map (Iter x i) (range_list n1 n2) hss.
  Proof.
    split; auto using decl_map_from_map, decl_map_to_map.
  Qed.

  Lemma decl_map_iter_def:
    forall x i n1 n2,
    (forall n, n1 <= n < n2 -> exists hs, Run (i_subst x (NNum n) i) hs) ->
    exists hss, DeclMap x i n1 n2 hss.
  Proof.
    intros.
    assert (Hm: exists hss, Map (Iter x i) (range_list n1 n2) hss). {
      apply map_def; auto using range_list_no_dup.
      intros.
      unfold Iter.
      auto using range_list_inv_in_2.
    }
    destruct Hm as (m, Hm).
    eauto using decl_map_from_map.
  Qed.

  Lemma run_decl_map:
     forall n1 n2 i1 i2 x hss hs hs',
     hs' = prod (List.concat hss) hs ++ hs  ->
     DeclMap x i1 n1 n2 hss ->
     Run i2 hs ->
     Run (Decl x (NNum n1, NNum n2) i1 i2) hs'.
  Proof.
    intros.
    apply run_decl with (range_list n1 n2).
    - apply r_step_range_list.
    - eapply run_branch_map; eauto.
  Qed.

  Lemma decl_map_def:
    forall x i n1 n2 f,
    (forall n, n1 <= n < n2 -> Run (i_subst x (NNum n) i) (f n)) ->
    DeclMap x i n1 n2 (map f (range_list n1 n2)).
  Proof.
    intros.
    unfold DeclMap.
    auto using branch_map_def, range_list_inv_in_2.
  Qed.

  Lemma decl_map_rw:
    forall n1 n2 i j x hss,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    DeclMap x i n1 n2 hss ->
    exists hss',
    DeclMap x j n1 n2 hss' /\
    MMEquivStruct hss hss'.
  Proof.
    intros.
    unfold DeclMap in *.
    apply branch_map_rw with (j:=j) in H0; auto.
    intros.
    apply range_list_inv_in_2 in H1.
    auto.
  Qed.

  Lemma run_decl_map_def:
     forall f n1 n2 i1 i2 x hs hs',
     hs' = prod (List.concat (map f (range_list n1 n2))) hs ++ hs  ->
     (forall n,
       n1 <= n < n2 ->
       Run (i_subst x (NNum n) i1) (f n)) ->
     Run i2 hs ->
     Run (Decl x (NNum n1, NNum n2) i1 i2) hs'.
  Proof.
    intros.
    eapply run_decl_map; eauto using decl_map_def.
  Qed.

  Lemma run_branch_inv_map:
    forall l i1 i2 x hs',
    Run (Branch x l i1 i2) hs' ->
    NoDup l ->
    exists hss hs,
    hs' = prod (List.concat hss) hs ++ hs  /\
    Run i2 hs /\
    BranchMap x i1 l hss.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      simpl.
      exists ([]).
      exists hs'.
      repeat split; auto.
      apply branch_map_nil.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHl in H8; auto; clear IHl.
    destruct H8 as (hss, (hs3, (Heq,(Hr,Hf)))).
    apply run_inv_seq in H7.
    destruct H7 as (m1, (m2, (?, (Hr1, Hr2)))).
    assert (hs3 = m2) by eauto using run_fun.
    subst.
    exists (m1::hss).
    exists m2.
    repeat split; auto using branch_map_cons.
    simpl.
    rewrite <- prod_app.
    repeat rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma run_decl_inv_map:
    forall n1 n2 i1 i2 x hs',
    Run (Decl x (NNum n1, NNum n2) i1 i2) hs' ->
    exists hss hs,
    hs' = prod (List.concat hss) hs ++ hs /\
    Run i2 hs /\
    DeclMap x i1 n1 n2 hss.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply r_step_to_range_list in H5.
    apply run_branch_inv_map in H6.
    - destruct H6 as (hss, (m1, (?,(Hr,Hf)))).
      subst.
      exists hss.
      exists m1.
      eauto.
    - subst.
      auto using range_list_no_dup.
  Qed.

  Definition branch_iter n1 n2 f :=
    @List.map nat (list history) f (range_list n1 n2).

  Lemma decl_map_inv:
    forall n1 n2 i x hs',
    DeclMap x i n1 n2 hs' ->
    exists f,
    hs' = branch_iter n1 n2 f /\
    (forall n, n1 <= n < n2 -> Run (i_subst x (NNum n) i) (f n)).
  Proof.
    intros.
    unfold DeclMap in H.
    apply branch_map_inv in H; auto using range_list_no_dup.
    destruct H as (f, (?, Hf)).
    subst.
    exists f.
    auto using range_list_in.
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

  Lemma impl_branch_seq_1:
    forall x l i j k,
    ~ In x i ->
    l <> [] ->
    ProgImpl
      (Branch x l (seq i j) k)
      (seq i (Branch x l j k)).
  Proof.
    unfold ProgImpl.
    induction l. {
      intros.
      contradiction.
    }
    intros i j k Hnin _ m1 Hr1.
    destruct l. {
      inversion Hr1; subst; clear Hr1.
      inversion H6; subst; clear H6.
      repeat rewrite i_subst_seq in *.
      apply run_inv_seq in H5.
      destruct H5 as (m1, (m2, (?, (Hr1, Hr2)))).
      assert (m2 = hs2) by eauto using run_fun.
      subst.
      apply run_inv_seq in Hr1.
      destruct Hr1 as (m3, (m4, (?, (Hr1, Hr3)))).
      subst.
      eexists.
      split. {
        apply run_seq. {
          (* eapply run_seq; eauto.*)
          rewrite i_subst_not_in in Hr1; eauto.
        }
        apply run_branch_cons.
        + apply run_seq; eauto.
        + apply run_branch_nil; eauto.
      }
      repeat rewrite <- prod_assoc.
      rewrite app_prod_absorb_1.
      2: {
        eauto using prod_neq_nil, run_not_nil.
      }
      repeat rewrite prod_assoc.
      apply mem_equiv_prod_r.
      - eauto using prod_neq_nil, run_not_nil.
      - assert (Hr: prod m4 hs2 <> []) by eauto using prod_neq_nil, run_not_nil.
        intros N.
        destruct (prod m4 hs2). {
          contradiction.
        }
        inversion N.
      - eauto using run_not_nil.
      - rewrite app_prod_absorb_1; eauto using run_not_nil.
        reflexivity.
    }
    inversion Hr1; subst; clear Hr1.
    assert (Hne2: n :: l <> []). {
      intros N.
      inversion N.
    }
    assert (IHl := IHl i j k Hnin Hne2 hs2 H6).
    destruct IHl as (m2, (Hr1, R)).
    rewrite i_subst_seq in H5.
    rewrite i_subst_not_in in H5; auto.
    apply run_inv_seq in H5.
    destruct H5 as (m1, (m3, (?, (Hr2, Hr3)))). 
    subst.
    apply run_inv_seq in Hr2.
    destruct Hr2 as (m4, (m5, (?, (Hr4, Hr5)))).
    subst.
    apply run_inv_seq in Hr1.
    destruct Hr1 as (m6, (m7, (?, (Hr1, Hr2)))).
    assert (m6 = m4) by eauto using run_fun; subst; clear Hr4.
    eexists.
    split. {
      apply run_seq; eauto.
      apply run_branch_cons; eauto.
      apply run_seq; eauto.
    }
    repeat rewrite prod_assoc.
    rewrite <- prod_app_r.
    rewrite R.
    reflexivity.
  Qed.

  Lemma impl_branch_seq_2:
    forall x l i j k,
    ~ In x i ->
    l <> [] ->
    ProgImpl
      (seq i (Branch x l j k))
      (Branch x l (seq i j) k).
  Proof.
    unfold ProgImpl.
    induction l. {
      intros.
      contradiction.
    }
    intros i j k Hnin _ m1 Hr1.
    apply run_inv_seq in Hr1.
    destruct Hr1 as (m2, (m3, (?, (Hr1, Hr2)))).
    subst.
    inversion Hr2; subst; clear Hr2.
    apply run_inv_seq in H5.
    destruct H5 as (m1, (m3, (?, (Hr2, Hr3)))).
    subst.
    destruct l. {
      clear IHl.
      eexists.
      inversion H6; subst; clear H6.
      assert (m3 = hs2) by eauto using run_fun; subst.
      split. {
        apply run_branch_cons. {
          rewrite i_subst_seq.
          rewrite i_subst_not_in; auto.
          eauto using run_seq.
        }
        eauto using run_branch_nil.
      }
      repeat rewrite prod_assoc.
      rewrite <- prod_app_r.
      assert (Hi: MIncl (prod m2 hs2) (prod m2 (prod m1 hs2))). {
        apply m_incl_prod_3.
        - eauto using prod_neq_nil, run_not_nil.
        - eauto using m_incl_prod_1, run_not_nil.
      }
      rewrite (m_incl_app_r _ _ Hi).
      clear Hi.
      assert (Hi: MIncl hs2 (prod m2 (prod m1 hs2))). {
        assert (Hi: MIncl hs2 (prod m1 hs2)). {
          apply m_incl_prod_1.
          eauto using run_not_nil.
        }
        transitivity (prod m1 hs2); auto.
        apply m_incl_prod_1.
        eauto using run_not_nil.
      }
      rewrite (m_incl_app_r _ _ Hi).
      reflexivity.
    }
    edestruct IHl; eauto; clear IHl.
    - intros N; inversion N.
    - apply run_seq; eauto.
    - destruct H as (Hr4, Hr5).
      eexists.
      split. {
        apply run_branch_cons.
        - rewrite i_subst_seq.
          rewrite i_subst_not_in; auto.
          eauto using run_seq.
        - eauto.
      }
      repeat rewrite prod_assoc.
      rewrite <- prod_app_r.
      rewrite Hr5.
      reflexivity.
  Qed.

  Lemma equiv_i_subst_branch_seq:
    forall i j k l x,
    ~ In x i ->
    l <> [] ->
    ProgEquiv
      (Branch x l (seq i j) k)
      (seq i (Branch x l j k)).
  Proof.
    intros.
    unfold ProgEquiv.
    split; auto using impl_branch_seq_1, impl_branch_seq_2.
  Qed.

  Lemma equiv_i_subst_decl_seq:
    forall i j k n1 n2 x,
    ~ In x i ->
    n1 < n2 ->
    ProgEquiv
      (Decl x (NNum n1, NNum n2) (seq i j) k)
      (seq i (Decl x (NNum n1, NNum n2) j k)).
  Proof.
    intros.
    unfold ProgEquiv.
    split. {
      unfold ProgImpl.
      intros.
      inversion H1.
      subst.
      assert (Hx : ProgEquiv
        (Branch x l (seq i j) k)
        (seq i (Branch x l j k))). {
        apply equiv_i_subst_branch_seq; auto.
        apply r_step_to_range_list in H7.
        subst.
        auto using range_list_not_nil.
      }
      eapply run_prog_equiv_inv_l in Hx; eauto.
      destruct Hx as (m2, (Hr2,?)).
      apply run_inv_seq in Hr2.
      destruct Hr2 as (m3, (m4, (?, (Hra, Hrb)))).
      subst.
      eexists.
      split. {
        apply run_seq; eauto using run_decl.
      }
      assumption.
    }
    unfold ProgImpl.
    intros.
    apply run_inv_seq in H1.
    destruct H1 as (m2, (m3, (?, (Hr1, Hr2)))).
    inversion Hr2; subst; clear Hr2.
    assert (Hx : ProgEquiv
      (Branch x l (seq i j) k)
      (seq i (Branch x l j k))). {
      apply equiv_i_subst_branch_seq; auto.
      apply r_step_to_range_list in H7.
      subst.
      auto using range_list_not_nil.
    }
    assert (Hr: Run (seq i (Branch x l j k)) (prod m2 m3)). {
      apply run_seq; auto.
    }
    eapply run_prog_equiv_inv_r in Hx; eauto.
    destruct Hx as (m4, (Hrb, Hm)).
    eexists.
    split. {
      eapply run_decl; eauto.
    }
    assumption.
  Qed.

  Lemma branch_map_inv_seq:
    forall l x i j ms1, 
    BranchMap x (seq i j) l ms1 ->
    exists ms2 ms3,
    BranchMap x i l ms2 /\ BranchMap x j l ms3 /\ ms1 = map2 prod ms2 ms3.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      eauto using branch_map_nil.
    }
    inversion H; subst; clear H.
    rewrite i_subst_seq in H2.
    apply run_inv_seq in H2.
    destruct H2 as (hs1, (hs2, (?, (Hra, Hrb)))).
    subst.
    apply IHl in H4.
    destruct H4 as (ms2, (ms3, (Hb1, (Hb2, R2)))).
    subst.
    eexists.
    eexists.
    repeat split.
    - eauto using branch_map_cons.
    - eauto using branch_map_cons.
    - reflexivity.
  Qed.

  Lemma branch_map_seq:
    forall l x i j ms1 ms2, 
    BranchMap x i l ms1 ->
    BranchMap x j l ms2 ->
    BranchMap x (seq i j) l (map2 prod ms1 ms2).
  Proof.
    induction l; intros; inversion H; inversion H0; subst; clear H H0. {
      apply branch_map_nil.
    }
    rewrite map2_cons_rw.
    apply branch_map_cons; auto.
    rewrite i_subst_seq.
    auto using run_seq.
  Qed.

  Lemma decl_map_inv_seq:
    forall n1 n2 x i j ms1, 
    DeclMap x (seq i j) n1 n2 ms1 ->
    exists ms2 ms3,
    DeclMap x i n1 n2 ms2 /\ DeclMap x j n1 n2 ms3 /\ ms1 = map2 prod ms2 ms3.
  Proof.
    unfold DeclMap.
    eauto using branch_map_inv_seq.
  Qed.

  Lemma decl_map_seq:
    forall n1 n2 x i j ms1 ms2, 
    DeclMap x i n1 n2 ms1 ->
    DeclMap x j n1 n2 ms2 ->
    DeclMap x (seq i j) n1 n2 (map2 prod ms1 ms2).
  Proof.
    unfold DeclMap;auto using branch_map_seq.
  Qed.


  Lemma decl_map_inv_i_subst_eq:
    forall x y i n1 n2 m1,
    ~ In x i ->
    DeclMap x (i_subst y (NVar x) i) n1 n2 m1 ->
    DeclMap y i n1 n2 m1.
  Proof.
    intros x y i n1 n2 m1 Hn1 Hd.
    apply decl_map_to_map in Hd.
    apply decl_map_from_map.
    apply map_impl with (P:=Iter x (i_subst y (NVar x) i)); auto.
    intros.
    unfold Iter in *.
    rewrite i_subst_subst_trans in H; auto.
  Qed.

  Lemma run_decl_seq:
    forall x n1 n2 i j k m1 m2 m3,
    Run k m1 ->
    DeclMap x i n1 n2 m2 ->
    DeclMap x j n1 n2 m3 ->
    Run (Decl x (NNum n1, NNum n2) (seq i j) k) (prod (List.concat (map2 prod m2 m3)) m1 ++ m1).
  Proof.
    intros.
    eapply run_decl_map; eauto.
    apply decl_map_seq; auto.
  Qed.

  Let i_subst_not_in_decl_rw:
    forall x n1 y n2 i j hs,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    Run (i_subst x (NNum n2) (Decl y (NNum n1, NVar x) i j)) hs ->
    Run (Decl y (NNum n1, NNum n2) i j) hs.
  Proof.
    intros.
    match goal with
    | [ H: Run _ _ |- _ ] => rename H into Hr
    end.
    simpl in Hr.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?].
    2: { contradiction. }
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]. { contradiction. }
    rewrite i_subst_not_in in Hr; auto.
    rewrite i_subst_not_in in Hr; auto.
  Qed.

  Lemma branch_map_inv_decl_not_in:
    forall l n1 i j ms x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    l <> [] ->
    BranchMap x (Decl y (NNum n1, NVar x) i j) l ms ->
    NoDup l ->
    exists (m:list history) (hs:list (list (list history))),
    ms = (map (fun x => (prod (@List.concat history x) m) ++ m) hs) /\
    Run j m /\
    Map (DeclMap y i n1) l hs.
  Proof.
    induction l; intros n i j ms x y Hn1 Hn2 Hneq Hnil Hb Hd. {
      contradiction.
    }
    clear Hnil.
    destruct l; inversion Hb; subst; clear Hb. {
      match goal with
      | [ H: Run _ _ |- _ ] => rename H into Hr
      end.
      apply i_subst_not_in_decl_rw in Hr; auto.
      apply run_decl_inv_map in Hr.
      destruct Hr as (ms1, (m2, (?, (Hr, Hm)))).
      inversion H3; clear H3.
      subst.
      exists m2.
      simpl.
      unfold plus.
      exists [ms1].
      simpl.
      repeat split; auto using map_cons, map_nil.
    }
    match goal with
    | [ H: Run _ _ |- _ ] => rename H into Hr
    end.
    apply i_subst_not_in_decl_rw in Hr; auto.
    apply run_decl_inv_map in Hr.
    destruct Hr as (ms1, (m2, (?, (Hr, Hm)))).
    subst.
    inversion Hd; subst; clear Hd.
    apply IHl in H3; auto; clear IHl.
    2: { intros N; inversion N. }
    destruct H3 as (m, (hs, (?, (Hr2, Hmap)))).
    subst.
    assert (m2 = m) by eauto using run_fun; subst. 
    exists m.
    exists (ms1::hs).
    repeat split; auto using map_cons.
  Qed.

  Lemma decl_map_inv_decl_not_in:
    forall n1 n2 n3 i j ms x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 ms ->

    exists (m:list history) (hs:list (list (list history))),
    ms = (map (fun x => (prod (@List.concat history x) m) ++ m) hs) /\
    Run j m /\
    Map (DeclMap y i n1) (range_list n2 n3) hs.
  Proof.
    intros.
    apply branch_map_inv_decl_not_in in H3; auto using range_list_no_dup, range_list_not_nil.
  Qed.

  Lemma branch_map_decl:
    forall l n1 i j m hs x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    l <> [] ->
    NoDup l ->
    Run j m ->
    Map (DeclMap y i n1) l hs ->
    BranchMap x (Decl y (NNum n1, NVar x) i j) l (map (fun x => (prod (@List.concat history x) m) ++ m) hs).
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H3; subst; clear H3.
    inversion H5; subst; clear H5.
    destruct l. {
      inversion H12; subst; clear H12.
      apply branch_map_cons; auto using branch_map_nil.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    }
    apply branch_map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    - apply IHl; auto.
      intros N; inversion N.
  Qed.

  Lemma decl_map_decl:
    forall n1 n2 n3 i j hs m x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    Run j m ->
    Map (DeclMap y i n1) (range_list n2 n3) hs ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 (map (fun x => (prod (@List.concat history x) m) ++ m) hs) .
  Proof.
    intros.
    apply branch_map_decl; auto using range_list_no_dup, range_list_not_nil.
  Qed.


  Lemma branch_map_inv_acc:
    forall l x e i ms,
    BranchMap x (Acc e i) l ms ->
    exists ms1 ms2,
    ms = map2 prod ms1 ms2 /\
    BranchMap x (Acc e Skip) l ms1 /\
    BranchMap x i l ms2.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      exists [].
      exists [].
      repeat split; auto using branch_map_nil.
    }
    inversion H; subst; clear H.
    apply IHl in H4; clear IHl.
    destruct H4 as (ms1, (ms2, (?, (Hb1, Hb2)))).
    subst.
    simpl in H2.
    destruct e as (ac, e).
    inversion H2; subst; clear H2.
    assert (Hra: Run (Acc (access_subst x (NNum a) ac, n_subst x (NNum a) e) Skip) (prepend v [[]])). {
      auto using run_access, run_skip.
    }
    eapply branch_map_cons in Hb1; eauto; clear Hra.
    exists (prepend v [[]] :: ms1).
    eapply branch_map_cons in Hb2; eauto.
    exists (hs0 :: ms2).
    simpl in *.
    rewrite app_nil_r in *.
    rewrite map2_cons_rw.
    rewrite prepend_rw.
    auto.
  Qed.

  Lemma decl_map_inv_acc:
    forall x e i n1 n2 ms,
    DeclMap x (Acc e i) n1 n2 ms ->
    exists ms1 ms2,
    ms = map2 prod ms1 ms2 /\
    DeclMap x (Acc e Skip) n1 n2 ms1 /\
    DeclMap x i n1 n2 ms2.
  Proof.
    intros.
    unfold DeclMap in *.
    apply branch_map_inv_acc in H.
    destruct H as (ms1, (ms2, (?, (Hb1, Hb2)))).
    eauto.
  Qed.

  Lemma impl_branch_nil_1:
    forall x i j,
    ProgImpl
      (Branch x [] i j)
      j.
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    inversion H; subst; clear H.
    exists m1.
    split; auto; reflexivity.
  Qed.

  Lemma impl_branch_nil_2:
    forall x i j,
    ProgImpl
      j
      (Branch x [] i j).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    exists m1.
    split; auto using run_branch_nil; reflexivity.
  Qed.

  Lemma p_eq_branch_nil:
    forall x i j,
    ProgEquiv (Branch x [] i j) j.
  Proof.
    intros.
    auto using prog_equiv_def, impl_branch_nil_1, impl_branch_nil_2.
  Qed.

  Import Morphisms.

  Lemma p_eq_seq_impl:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgImpl (seq i1 j1) (seq i2 j2).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    apply run_inv_seq in H1.
    destruct H1 as (hs1, (hs2, (?, (Hr1, Hr2)))).
    subst.
    assert (hs1 <> []) by eauto using run_not_nil.
    assert (hs2 <> []) by eauto using run_not_nil.
    eapply run_prog_equiv_inv_l in Hr1; eauto.
    destruct Hr1 as (m2, (Hr_i2, ?)).
    eapply run_prog_equiv_inv_l in Hr2; eauto.
    destruct Hr2 as (m3, (Hr_j2, ?)).
    exists (prod m2 m3).
    split; auto using run_seq.
    rewrite mem_equiv_prod_l with (m4:=m2); eauto using run_not_nil.
    rewrite mem_equiv_prod_r with (m4:=m3); eauto using run_not_nil.
    reflexivity.
  Qed.

  Lemma p_eq_seq:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgEquiv (seq i1 j1) (seq i2 j2).
  Proof.
    intros.
    apply prog_equiv_def.
    - auto using p_eq_seq_impl.
    - symmetry in H.
      symmetry in H0.
      auto using p_eq_seq_impl.
  Qed.

  Global Instance seq_p_equiv_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgEquiv) seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq.
  Qed.

  Global Instance seq_p_impl_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgImpl) seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq_impl.
  Qed.

  Global Instance proper_prog_impl_2: Proper (ProgEquiv ==> ProgEquiv ==> Basics.flip Basics.impl) ProgImpl.
  Proof.
    unfold Proper, respectful.
    intros.
    unfold Basics.flip.
    unfold Basics.impl.
    intros.
    rename x into i1.
    rename y into i2.
    rename x0 into j1.
    rename y0 into j2.
    destruct H.
    destruct H0.
    transitivity i2; auto.
    transitivity j2; auto.
  Qed.

  Lemma impl_branch_branch_seq_1:
    forall x l i1 i2 j1 j2,
    ProgImpl
      (Branch x l (seq i1 i2) (seq j1 j2))
      (seq (Branch x l i1 j1) (Branch x l i2 j2)).
  Proof.
    induction l; intros. {
      rewrite p_eq_branch_nil.
      rewrite p_eq_branch_nil.
      rewrite p_eq_branch_nil.
      reflexivity.
    }
  Qed.

  Lemma impl_branch_seq_2:
    forall x l i j k,
    ProgImpl
      (seq (Branch x l i k) (Branch x l j k))
      (Branch x l (seq i j) k).
  Proof.
  Qed.
End Defs.

Module C2Notations.
  Infix "==" := MemEquiv (at level 40).
End C2Notations.