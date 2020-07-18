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
Require Import AccExp.
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
  | Seq: inst -> inst -> inst
  | If: bexp -> inst -> inst -> inst
  | MemAcc: access_inst_type -> inst
  | Decl : var -> range -> inst -> inst
  | Branch : var -> list nat -> inst -> inst
  | Fork : inst -> inst -> inst
  .

  Fixpoint i_subst x v i :=
    match i with
    | Skip => Skip
    | MemAcc e => MemAcc (access_inst_subst x v e)  
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | If b i j => If (b_subst x v b) (i_subst x v i) (i_subst x v j)
    | Decl y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      Decl y (r_subst x v r) i'
    | Branch y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      Branch y r i'
    | Fork i j => Fork (i_subst x v i) (i_subst x v j)
    end
  .

  (* --------------------------- SEQ --------------------------------- *)
(*
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
    - rewrite IHi1_1; clear IHi1_1.
      rewrite IHi1_2; clear IHi1_2.
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
    - rewrite IHi1.
      rewrite IHi2.
      reflexivity.
  Qed.

  Lemma seq_branch_rw:
    forall x l i j,
    Branch x l i j = seq (Branch x l i Skip) j.
  Proof.
    intros.
    reflexivity.
  Qed.
*)
  (* ---------------------------------- RUN ------------------------- *)
  
  Notation history := (list access_val).

  Inductive Run: inst -> list history -> Prop :=
  | run_skip:
    Run Skip [[]]
  | run_seq:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Seq i j) (prod hs1 hs2)
  | run_if_true:
    forall b i j hs,
    BStep b true ->
    Run i hs ->
    Run (If b i j) hs
  | run_if_false:
    forall b i j hs,
    BStep b false ->
    Run j hs ->
    Run (If b i j) hs
  | run_access:
    forall e v,
    access_inst_step e v ->
    Run (MemAcc e) [v]
  | run_decl:
    forall r l i x hs,
    RStep r l ->
    Run (Branch x l i) hs ->
    Run (Decl x r i) hs
  | run_branch_cons:
    forall x n l i hs1 hs2,
    Run (i_subst x (NNum n) i) hs1 ->
    Run (Branch x l i) hs2 ->
    Run (Branch x (n::l) i) (hs1 ++ hs2)
  | run_branch_nil:
    forall x i,
    Run (Branch x [] i) [[]]
  | run_fork:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Fork i j) (hs1 ++ hs2).

  Lemma prod_inv_nil:
    forall A hs1 hs2,
    @prod A hs1 hs2 = [] ->
    hs1 = [] \/ hs2 = [].
  Proof.
    intros.
    destruct hs1. { auto. }
    destruct hs2. { auto. }
    inversion H.
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
    - apply prod_inv_nil in Heql.
      destruct Heql; auto.
    - contradiction.
    - contradiction.
    - inversion Heql.
    - auto.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
    - inversion Heql.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
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
(*
  Inductive DoLoop : var -> list nat -> inst -> list (list history) -> Prop :=
  | do_loop_nil:
    forall i x,
    DoLoop x [] i []
  | do_loop_cons:
    forall x n l i hss hs,
    Run (i_subst x (NNum n) i) hs ->
    DoLoop x l i hss ->
    DoLoop x (n::l) i (hs::hss).

  Let run_branch_to_do_loop:
    forall x l i hs,
    Run (Branch x l i) hs ->
    exists hss, hs = List.concat hss /\ DoLoop x l i hss.
  Proof.
    intros.
    remember (Branch _ _ _) as j.
    generalize dependent x.
    generalize dependent i.
    generalize dependent l.
    induction H; intros; inversion Heqj; subst; clear Heqj. {
      assert (IHRun2 := IHRun2 _ _ _ eq_refl).
      destruct IHRun2 as (hss, (?, Hd)).
      exists (hs1::hss).
      split. {
        simpl.
        subst.
        auto.
      }
      apply do_loop_cons; auto.
    }
    exists [].
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
    - rewrite <- prod_app.
      simpl.
      apply run_fork; eauto.
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
    - inversion H1; subst; clear H1.
      erewrite IHRun1; eauto.
      erewrite IHRun2; eauto.
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
    - inversion H2; subst; clear H2.
      rewrite <- prod_app.
      eapply IHRun1 in H5; eauto.
      eapply IHRun2 in H7; eauto.
      subst.
      reflexivity.
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
      auto using run_branch_cons.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        eauto using run_skip, run_branch_nil.
      }
      destruct (IHRun _ _ eq_refl) as (hs1, (hs2, (?, ?))).
      eauto using run_branch_nil.
    - destruct i1; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        eauto using run_skip, run_fork.
      }
      destruct (IHRun1 _ _ eq_refl) as (hsa, (hsb, (?, ?))).
      destruct (IHRun2 _ _ eq_refl) as (hsc, (hsd, (?, ?))).
      assert (hsb = hsd) by eauto using run_fun; subst.
      eauto using run_fork.
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
    - rewrite IHi1_1.
      rewrite IHi1_2.
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
    - rewrite IHi1.
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
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
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
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.
*)
  (* ------------------------------- In ----------------------------- *)

  Fixpoint In x (i:inst) : Prop :=
  match i with
  | MemAcc i => access_inst_in x i
  | Skip => False
  | Seq i j => In x i \/ In x j
  | If b i j => BIn x b \/ In x i \/ In x j
  | Decl y r i => x = y \/ RIn x r \/ In x i 
  | Branch y l i => x = y \/ In x i
  | Fork i j => In x i \/ In x j
  end.

  Lemma not_in_acc:
    forall x e,
    ~ In x (MemAcc e) ->
    ~ access_inst_in x e.
  Proof.
    intros.
    auto.
  Qed.

  Lemma not_in_decl:
    forall x y r i,
    ~ In x (Decl y r i) ->
    x <> y /\ ~ RIn x r /\ ~ In x i.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst; simpl; auto.
  Qed.

  Lemma not_in_branch:
    forall x y r i,
    ~ In x (Branch y r i) ->
    x <> y /\ ~ In x i.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst; simpl; auto.
  Qed.


  Lemma in_branch_to_decl:
    forall x y i l r,
    In x (Branch y l i) ->
    In x (Decl y r i).
  Proof.
    intros.
    inversion H; subst; clear H; simpl; auto.
  Qed.

  Lemma in_branch_cons:
    forall x y l i n,
    In x (Branch y l i) ->
    In x (Branch y (n::l) i).
  Proof.
    intros.
    simpl; auto.
  Qed.


  (* ------------------ i_subst + In ------------------------------ *)

  Lemma not_in_fork:
    forall x i j,
    ~ In x (Fork i j) ->
    ~ In x i /\ ~ In x j.
  Proof.
    intros.
    simpl in *.
    auto.
  Qed.

  Lemma not_in_seq:
    forall x i j,
    ~ In x (Seq i j) ->
    ~ In x i /\ ~ In x j.
  Proof.
    intros.
    simpl in *.
    auto.
  Qed.

  Lemma i_subst_not_in:
    forall i x v,
    ~ In x i ->
    i_subst x v i = i.
  Proof.
    induction i; intros; simpl in *.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_not_in; auto.
    - rewrite access_inst_subst_not_in; auto.
    - apply not_in_decl in H.
      destruct H as (H, (H1, H2)).
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      rewrite r_subst_not_in; auto.
      rewrite IHi; auto.
    - apply not_in_branch in H; auto.
      destruct H as (H, H1).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      rewrite IHi; auto.
    - apply not_in_fork in H.
      destruct H.
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
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_trans; auto.
    - rewrite access_inst_subst_subst_trans; auto.
    - apply not_in_decl in H.
      destruct H as (H0, (H1, H2)).
      rewrite r_subst_subst_trans; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite i_subst_not_in; auto.
      }
      rewrite IHi; auto.
    - apply not_in_branch in H; auto.
      destruct H as (H, H1).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite i_subst_not_in; auto.
      }
      rewrite IHi; auto.
    - apply not_in_fork in H.
      destruct H.
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
    induction i;
      simpl;
      intros.
    - assumption.
    - destruct H; eauto.
    - destruct H as [H|[H|H]]; eauto using in_b_subst_neq.
    - apply access_inst_in_subst_neq in H; auto.
    - destruct H as [H|[H|H]]; auto.
      + eauto using in_r_subst_neq.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto.
        }
        eauto.
    - destruct H as [H|H]; auto.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        auto.
      }
      eauto.
    - destruct H; eauto.
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
    - destruct H; auto.
    - destruct H as [H|[H|H]]; auto.
      left.
      eapply in_b_subst_neq; eauto.
      intros N.
      inversion N.
    - eapply access_inst_in_subst_neq; eauto.
      intros N.
      inversion N.
    - destruct H as [H|[H|H]]; auto.
      + apply in_r_subst_neq in H; auto.
        intros N.
        inversion N.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
    - destruct H; auto.
      destruct (Set_VAR.MF.eq_dec x v); auto.
    - destruct H; auto.
  Qed.

  (* --------------------------------- VAR ------------------------- *)

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j | Fork i j => Var x i \/ Var x j
  | Decl y _ i | Branch y _ i => x = y \/ Var x i
  end.


  Lemma var_not_in_branch:
    forall x y l i,
    ~ Var x (Branch y l i) ->
    x <> y /\ ~ Var x i.
  Proof.
    intros.
    repeat split; intros N; subst; contradict H; simpl; auto.
  Qed.

  Lemma var_not_in_fork:
    forall x i j,
    ~ Var x (Fork i j) ->
    ~ Var x i /\ ~ Var x j.
  Proof.
    intros.
    split;
    intros N;
    contradict H;
    simpl; auto.
  Qed.

  Lemma var_branch_to_decl:
    forall x y i l r,
    Var x (Branch y l i) ->
    Var x (Decl y r i).
  Proof.
    intros.
    inversion H; subst; clear H; simpl; auto.
  Qed.

  Lemma var_branch_cons:
    forall x y l i n,
    Var x (Branch y l i) ->
    Var x (Branch y (n :: l) i).
  Proof.
    intros.
    simpl in *; auto.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros;
    destruct H; auto;
    destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (*
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
  *)
  (* -------------------------------- InRange -------------------------- *)

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j | Fork i j => InRange x i \/ InRange x j
  | Decl _ r i => RIn x r \/ InRange x i
  | Branch _ _ i => InRange x i
  end.

  Lemma in_range_branch_to_decl:
    forall x y i l r,
    InRange x (Branch y l i) ->
    InRange x (Decl y r i).
  Proof.
    intros.
    simpl; auto.
  Qed.

  Lemma in_range_inv_subst_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; simpl; try destruct H; auto.
    - apply in_r_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct (Set_VAR.MF.eq_dec x v);
      auto.
    - destruct (Set_VAR.MF.eq_dec x v);
      auto.
  Qed.

  Lemma in_range_branch_cons:
    forall x y l i n,
    InRange x (Branch y l i) ->
    InRange x (Branch y (n :: l) i).
  Proof.
    intros.
    simpl; auto.
  Qed.

  Lemma not_in_range_fork:
    forall x i j,
    ~ InRange x (Fork i j) ->
    ~ InRange x i /\ ~ InRange x j.
  Proof.
    intros.
    split;
    intros N;
    contradict H; simpl; auto.
  Qed.

End Defs.

