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
Require Import MExp.
Import ListNotations.
Import MHistNotations.

Section Defs.
  Context {A:Access}.
  Class AccessInst := {
  access_inst_type: Type;
  access_inst_subst: var -> nexp -> access_inst_type -> access_inst_type;
  access_inst_step: access_inst_type -> list access_val -> Prop;
  access_inst_in: var -> access_inst_type -> Prop;

  access_inst_step_fun:
    forall e h1 h2,
    access_inst_step e h1 -> access_inst_step e h2 -> h1 = h2;
  access_inst_subst_subst_eq:
    forall x n1 n2 a,
    access_inst_subst x (NNum n1) (access_inst_subst x (NNum n2) a) =
    access_inst_subst x (NNum n2) a;

  access_inst_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    access_inst_subst x (NNum n1) (access_inst_subst y (NNum n2) a) =
    access_inst_subst y (NNum n2) (access_inst_subst x (NNum n1) a)
  ;
  access_inst_subst_subst_neq_2:
    forall x y z n i,
    x <> z ->
    y <> z ->
    access_inst_subst x (NVar y) (access_inst_subst z (NNum n) i) =
    access_inst_subst z (NNum n) (access_inst_subst x (NVar y) i)
  ;
  access_inst_subst_not_in:
    forall x e v,
    ~ access_inst_in x e -> access_inst_subst x v e = e
  ;
  access_inst_subst_subst_trans:
    forall e x v y,
    ~ access_inst_in x e ->
    access_inst_subst x v (access_inst_subst y (NVar x) e) =
    access_inst_subst y v e
  ;
  access_inst_in_subst_neq:
    forall e x y v,
    access_inst_in x (access_inst_subst y v e) ->
    ~ NIn x v ->
    access_inst_in x e
  ;
  }.

  Context {I:AccessInst}.
  Inductive inst :=
  | Skip
  | MemAcc: access_inst_type -> inst -> inst
  | Decl : var -> range -> inst -> inst -> inst
  | Branch : var -> list nat -> inst -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | MemAcc e j => MemAcc (access_inst_subst x v e) (i_subst x v j)  
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
  | MemAcc e i3 => MemAcc e (seq i3 i2)
  | Decl x r i3 i4 => Decl x r i3 (seq i4 i2)
  | Branch x r i3 i4 => Branch x r i3 (seq i4 i2)
  end.

  Notation history := (list access_val).

  Inductive Run: inst -> list history -> Prop :=
  | run_skip:
    Run Skip [[]]
  | run_access:
    forall i e v hs,
    access_inst_step e v ->
    Run i hs ->
    Run (MemAcc e i) (prepend v hs)
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

  Lemma run_inv_nil:
    forall i,
    ~ Run i [].
  Proof.
    intros i H.
    remember ([]).
    generalize dependent Heql.
    induction H; intros.
    - inversion Heql.
    - apply prepend_inv_nil in Heql.
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

  Let run_inv_branch_in:
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

  Let run_inv_branch:
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

  Lemma run_inv_decl:
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
    apply run_inv_branch in H6.
    destruct H6 as (hss, (?, Hc)).
    exists hss.
    split; auto.
    intros.
    apply (Ha n) in H0.
    apply Hc in H0.
    assumption.
  Qed.

  Lemma run_inv_decl_eq:
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
    apply run_inv_decl in H0.
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

  Lemma run_inv_acc_in:
    forall e i hs a,
    Run (MemAcc e i) hs ->
    MIn a hs ->
    exists hs' v,
    access_inst_step e v /\
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

  Lemma run_inv_decl_in:
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
    apply run_inv_branch_in in H6.
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
      assert (v0 = v) by eauto using access_inst_step_fun.
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
    | [ H1: access_inst_step ?e ?v1,
        H2: access_inst_step ?e ?v2 |- _ ] =>
          let H := fresh in
          assert (H: v2 = v1) by eauto using access_inst_step_fun;
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
    - rewrite IHi1.
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
    - rewrite access_inst_subst_subst_eq.
      rewrite IHi.
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
    - rewrite IHi; auto.
      rewrite access_inst_subst_subst_neq; auto.
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

  Lemma i_subst_subst_neq_2:
    forall x y z n i,
    y <> z ->
    x <> z ->
    i_subst x (NVar y) (i_subst z (NNum n) i)
    =
    i_subst z (NNum n) (i_subst x (NVar y) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite access_inst_subst_subst_neq_2; auto.
      rewrite IHi; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec z v). {
        subst.
        rewrite r_subst_subst_neq_2; auto.
      }
      rewrite r_subst_subst_neq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHi1; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        auto.
      }
      destruct (Set_VAR.MF.eq_dec z v). {
        subst.
        auto.
      }
      rewrite IHi1; auto.
  Qed.

  (* ------------------------------- In ----------------------------- *)

  Inductive In (x:var) : inst -> Prop :=
  | in_acc_1:
    forall e i,
    access_inst_in x e ->
    In x (MemAcc e i)
  | in_acc_2:
    forall e i,
    In x i ->
    In x (MemAcc e i)
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
    forall x e i,
    ~ In x (MemAcc e i) ->
    ~ In x i /\ ~ access_inst_in x e.
  Proof.
    intros.
    repeat split; intros N; contradict H;
      auto using in_acc_1, in_acc_2.
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


  Lemma in_branch_to_decl:
    forall x y i j l r,
    In x (Branch y l i j) ->
    In x (Decl y r i j).
  Proof.
    intros.
    inversion H; subst; clear H;
      auto using
        in_decl_1,
        in_decl_2,
        in_decl_3,
        in_decl_4.
  Qed.

  Lemma in_inv_seq:
    forall x i j,
    In x (seq i j) ->
    In x i \/ In x j.
  Proof.
    induction i; simpl; intros.
    - auto.
    - inversion H; subst; clear H.
      + auto using in_acc_1.
      + apply IHi in H1.
        destruct H1; auto.
        auto using in_acc_2.
    - inversion H; subst; clear H;
        auto using in_decl_1, in_decl_2, in_decl_3.
      apply IHi2 in H1.
      destruct H1; auto using in_decl_4.
    - inversion H; subst; clear H;
        auto using in_branch_1, in_branch_2.
      apply IHi2 in H1.
      destruct H1; auto using in_branch_3.
  Qed.

  Lemma in_branch_cons:
    forall x y l i j n,
    In x (Branch y l i j) ->
    In x (Branch y (n::l) i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    - auto using in_branch_1.
    - auto using in_branch_2.
    - auto using in_branch_3.
  Qed.


  (* ------------------ i_subst + In ------------------------------ *)

  Lemma i_subst_not_in:
    forall i x v,
    ~ In x i ->
    i_subst x v i = i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - apply not_in_acc in H.
      destruct H as (Ha, Hb).
      rewrite access_inst_subst_not_in; auto.
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
    - apply not_in_acc in H.
      destruct H as (Ha, Hb).
      rewrite IHi; auto.
      rewrite access_inst_subst_subst_trans; auto.
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
    - inversion H; subst; clear H.
      + apply access_inst_in_subst_neq in H3; auto using in_acc_1.
      + apply IHi in H3; auto using in_acc_2.
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

  Lemma in_inv_subst_in:
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

  Lemma in_inv_subst_1:
    forall y x n i,
    In y (i_subst x (NNum n) i) ->
    In y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      + apply access_inst_in_subst_neq in H1; auto using in_acc_1.
        intros N.
        inversion N.
      + auto using in_acc_2.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H;
          auto using
            in_decl_1, in_decl_2, in_decl_3, in_decl_4.
      + apply in_r_subst_neq in H1; auto using in_decl_1.
        intros N.
        inversion N.
      + apply in_r_subst_neq in H1; auto using in_decl_1.
        intros N.
        inversion N.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H;
          auto using in_branch_1, in_branch_2, in_branch_3.
  Qed.

  (* --------------------------------- VAR ------------------------- *)

  Inductive Var (x:var) : inst -> Prop :=
  | var_acc:
    forall p i,
    Var x i ->
    Var x (MemAcc p i)
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

  Lemma var_not_in_acc:
    forall x e i,
    ~ Var x (MemAcc e i) ->
    ~ Var x i.
  Proof.
    intros.
    intros N.
    contradict H.
    auto using var_acc.
  Qed.

  Lemma var_not_in_branch:
    forall x y l i j,
    ~ Var x (Branch y l i j) ->
    x <> y /\ ~ Var x i /\ ~ Var x j.
  Proof.
    intros.
    repeat split; intros N; subst; contradict H;
      auto using var_branch_eq, var_branch_l, var_branch_r.
  Qed.

  Lemma var_branch_to_decl:
    forall x y i1 i2 l r,
    Var x (Branch y l i1 i2) ->
    Var x (Decl y r i1 i2).
  Proof.
    intros.
    inversion H; subst; clear H; auto using var_decl_eq, var_decl_l, var_decl_r.
  Qed.

  Lemma var_branch_cons:
    forall x y l i j n,
    Var x (Branch y l i j) ->
    Var x (Branch y (n :: l) i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    - auto using var_branch_eq.
    - auto using var_branch_l.
    - auto using var_branch_r.
  Qed.

  Lemma var_seq_inv:
    forall x i j,
    Var x (seq i j) ->
    Var x i \/ Var x j.
  Proof.
    induction i; simpl; intros.
    - auto.
    - inversion H; subst; clear H.
      apply IHi in H1.
      destruct H1; auto using var_acc.
    - inversion H; subst; clear H; auto using var_decl_eq, var_decl_r, var_decl_l.
      apply IHi2 in H1.
      destruct H1; auto using var_decl_r.
    - inversion H; subst; clear H; auto using var_branch_eq, var_branch_r, var_branch_l.
      apply IHi2 in H1.
      destruct H1; auto using var_branch_r.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      apply IHi in H1.
      auto using var_acc.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H; auto using var_decl_eq, var_decl_l, var_decl_r.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H;
        auto using var_branch_eq, var_branch_l, var_branch_r.
  Qed.


  Lemma var_iter_branch:
    forall x y n i1 i2 l,
    Var y (seq (i_subst x (NNum n) i1) i2) ->
    Var y (Branch x l i1 i2).
  Proof.
    intros.
    apply var_seq_inv in H.
    destruct H as [N|N]. {
      apply var_subst_inv_1 in N.
      auto using var_branch_l.
    }
    auto using var_branch_r.
  Qed.

  (* -------------------------------- InRange -------------------------- *)


  Inductive InRange x : inst -> Prop := 
  | in_range_access:
    forall e i,
    InRange x i ->
    InRange x (MemAcc e i)
  | in_range_decl_eq:
    forall y r i1 i2,
    RIn x r ->
    InRange x (Decl y r i1 i2)
  | in_range_decl_l:
    forall r y i1 i2,
    InRange x i1 ->
    InRange x (Decl y r i1 i2)
  | in_range_decl_r:
    forall r i1 i2 y,
    InRange x i2 ->
    InRange x (Decl y r i1 i2)
  | in_range_branch_l:
    forall y l i1 i2,
    InRange x i1 ->
    InRange x (Branch y l i1 i2)
  | in_range_branch_r:
    forall y i1 i2 l,
    InRange x i2 ->
    InRange x (Branch y l i1 i2).

  Lemma in_range_branch_to_decl:
    forall x y i j l r,
    InRange x (Branch y l i j) ->
    InRange x (Decl y r i j).
  Proof.
    intros.
    inversion H; subst; clear H;
      auto using
        in_range_decl_eq,
        in_range_decl_l,
        in_range_decl_r.
  Qed.

  Lemma in_range_inv_seq:
    forall x i j,
    InRange x (seq i j) ->
    InRange x i \/ InRange x j.
  Proof.
    induction i; simpl; intros; auto.
    - inversion H; subst; clear H.
      apply IHi in H1.
      destruct H1; auto using in_range_access.
    - inversion H; subst; clear H;
        eauto using in_range_decl_eq, in_range_decl_l.
      apply IHi2 in H1.
      destruct H1; auto using in_range_decl_r.
    - inversion H; subst; clear H; auto using in_range_branch_l.
      apply IHi2 in H1.
      destruct H1; auto using in_range_branch_r.
  Qed.

  Lemma in_range_inv_subst_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - inversion H; subst; clear H.
      apply IHi in H1.
      auto using in_range_access.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H;
          auto using in_range_decl_l, in_range_decl_r.
        + apply in_r_subst_neq in H1; auto using in_range_decl_eq.
          intros N.
          inversion N.
        + apply in_r_subst_neq in H1; auto using in_range_decl_eq.
          intros N.
          inversion N.
    - destruct (Set_VAR.MF.eq_dec x v);
        inversion H; subst; clear H;
          auto using in_range_branch_l, in_range_branch_r.
  Qed.

  Lemma in_range_branch_cons:
    forall x y l i j n,
    InRange x (Branch y l i j) ->
    InRange x (Branch y (n :: l) i j).
  Proof.
    intros.
    inversion H; subst; clear H;
      auto using in_range_branch_l, in_range_branch_r.
  Qed.

End Defs.

