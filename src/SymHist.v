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

(*
  Lemma run_decl_inv_map_f:
    forall n1 n2 i1 i2 x hs',
    Run (Decl x (NNum n1, NNum n2) i1 i2) hs' ->
    exists f hs,
    hs' = prod (branch_iter n1 n2 f) hs ++ hs /\
    Run i2 hs /\
    (forall n, n1 <= n < n2 -> Run (i_subst x (NNum n) i1) (f n)).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply r_step_to_range_list in H5.
    apply run_branch_inv_map in H6.
    - destruct H6 as (f, (m1, (?,(Hr,Hf)))).
      subst.
      unfold branch_iter.
      subst.
      exists f.
      exists m1.
      repeat split; auto using range_list_in.
    - subst.
      auto using range_list_no_dup.
  Qed.
*)
End Defs.

Module C2Notations.
  Infix "==" := MemEquiv (at level 40).
End C2Notations.