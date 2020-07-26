Require Import Coq.Lists.List.

Require Import Var.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import MultiHist.
Require Import InUtil.
Require Import PairInUtil.

Require Tasks.

Import ListNotations.

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
    | Fork i j => Fork (i_subst x v i) (i_subst x v j)
    end
  .

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
  | run_if:
    forall e b i j hsi hsj,
    BStep e b ->
    Run i hsi ->
    Run j hsj ->
    Run (If e i j) (if b then hsi else hsj)
  | run_access:
    forall e v,
    access_inst_step e v ->
    Run (MemAcc e) [v]
  | run_fork:
    forall i j hs1 hs2,
    Run i hs1 ->
    Run j hs2 ->
    Run (Fork i j) (hs1 ++ hs2)
  | run_decl_cons:
    forall e1 e2 n1 n2 i x hs1 hs2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) hs1 ->
    Run (Decl x (NNum (S n1), NNum n2) i) hs2 ->
    Run (Decl x (e1, e2) i) (hs1 ++ hs2)
  | run_decl_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run (Decl x (e1, e2) i) [[]]
  .

  Lemma run_if_true:
    forall e i j hi hj,
    BStep e true ->
    Run i hi ->
    Run j hj ->
    Run (If e i j) hi.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma run_if_false:
    forall e i j hi hj,
    BStep e false ->
    Run i hi ->
    Run j hj ->
    Run (If e i j) hj.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
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
    - destruct b; auto.
    - inversion Heql.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
    - destruct hs1. { contradiction. }
      destruct hs2. { contradiction. }
      inversion Heql.
    - inversion Heql.
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
*)

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_eq; auto.
    - rewrite access_inst_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi; auto.
      rewrite r_subst_subst_eq.
      reflexivity.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_neq; auto.
    - rewrite access_inst_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite r_subst_subst_neq; auto.
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_subst_neq_2:
    forall x y z n i,
    y <> z ->
    x <> z ->
    i_subst x (NVar y) (i_subst z (NNum n) i)
    =
    i_subst z (NNum n) (i_subst x (NVar y) i).
  Proof.
    induction i; intros; simpl;
      try (rewrite IHi; auto; clear IHi);
      try (rewrite IHi1; auto; clear IHi1);
      try (rewrite IHi2; auto; clear IHi2);
      try reflexivity
    .
    - rewrite b_subst_subst_neq_2; auto.
    - rewrite access_inst_subst_subst_neq_2; auto.
    - destruct (Set_VAR.MF.eq_dec z v). {
        subst.
        rewrite r_subst_subst_neq_2; auto.
      }
      rewrite r_subst_subst_neq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHi; auto.
  Qed.

  (* ------------------------------- In ----------------------------- *)

  Fixpoint In x (i:inst) : Prop :=
  match i with
  | MemAcc i => access_inst_in x i
  | Skip => False
  | Seq i j => In x i \/ In x j
  | If b i j => BIn x b \/ In x i \/ In x j
  | Decl y r i => x = y \/ RIn x r \/ In x i 
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
  Qed.

  (* --------------------------------- VAR ------------------------- *)

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j | Fork i j => Var x i \/ Var x j
  | Decl y _ i (* | Branch y _ i*) => x = y \/ Var x i
  end.

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

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros;
    destruct H; auto;
    destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (* -------------------------------- InRange -------------------------- *)

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j | Fork i j => InRange x i \/ InRange x j
  | Decl _ r i => RIn x r \/ InRange x i
  end.

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

  (* --------------------- PAIR-IN INSTRUCTION ---------------------- *)

  Inductive IIn (a:access_val) : inst -> Prop :=
  | i_in_access:
    forall e v,
    access_inst_step e v ->
    List.In a v ->
    IIn a (MemAcc e)
  | i_in_seq_l:
    forall i j,
    IIn a i ->
    IIn a (Seq i j)
  | i_in_seq_r:
    forall i j,
    IIn a j ->
    IIn a (Seq i j)
  | i_in_if_true:
    forall b i j,
    BStep b true ->
    IIn a i ->
    IIn a (If b i j)
  | i_in_if_false:
    forall b i j,
    BStep b false ->
    IIn a j ->
    IIn a (If b i j)
  | i_in_fork_l:
    forall i j,
    IIn a i ->
    IIn a (Fork i j)
  | i_in_fork_r:
    forall i j,
    IIn a j ->
    IIn a (Fork i j)
  | i_in_decl:
    forall e1 e2 n1 n n2 x i,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (Decl x (e1, e2) i)
  .

  Lemma run_m_in_to_i_in:
    forall i h,
    Run i h ->
    forall a,
    MIn a h ->
    IIn a i.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi.
    - apply m_in_nil_nil in Hi.
      contradiction.
    - apply m_in_prod_inv in Hi.
      destruct Hi; auto using i_in_seq_l, i_in_seq_r.
    - destruct b. {
        eauto using i_in_if_true.
      }
      eauto using i_in_if_false.
    - apply m_in_inv_cons_nil in Hi.
      eapply i_in_access; eauto.
    - apply m_in_inv_app in Hi.
      destruct Hi; auto using i_in_fork_l, i_in_fork_r.
    - apply m_in_inv_app in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_in_decl; eauto.
      }
      apply IHHr2 in Hi.
      inversion Hi; subst; clear Hi.
      assert (S n1 = n0) by eauto using n_step_fun, n_step_num.
      assert (n3 = n2) by eauto using n_step_fun, n_step_num.
      subst.
      eapply i_in_decl with (n:=n); eauto.
      auto with *.
    - apply m_in_nil_nil in Hi.
      contradiction.
  Qed.

  Lemma run_i_in_to_m_in:
    forall i h,
    Run i h ->
    forall a,
    IIn a i ->
    MIn a h.
  Proof.
    intros i h Hr.
    induction Hr; intros a Hi; inversion Hi; subst; clear Hi.
    - apply m_in_prod_l; eauto using run_not_nil.
    - apply m_in_prod_r; eauto using run_not_nil.
    - assert (b = true) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun; eauto.
      subst.
      eauto.
    - assert (v0 = v) by eauto using access_inst_step_fun.
      subst.
      auto using m_in_eq.
    - auto using m_in_app_l.
    - auto using m_in_app_r.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. apply m_in_app_l. eauto. }
      apply m_in_app_r.
      apply IHHr2.
      eapply i_in_decl with (n1:=S n1) (n2:=n2); eauto using n_step_num.
      auto with *.
    - assert (n0 = n1) by eauto using n_step_fun; subst.
      assert (n2 = n3) by eauto using n_step_fun; subst.
      subst.
      Import Omega.
      omega.
  Qed.

  Lemma i_in_iff:
    forall i h,
    Run i h ->
    forall a,
    IIn a i <-> MIn a h.
  Proof.
    intros.
    split; eauto using run_m_in_to_i_in, run_i_in_to_m_in.
  Qed.

  (* --------------------------- SUBST IN --------------------------------- *)
  Section Props.
  Import Tasks.
  Context `{T:Tasks}.
  Inductive SIn (a:access_val) (n:nat) : inst -> Prop :=
  | s_in_access:
    forall e v,
    access_inst_step (access_inst_subst TID (NNum n) e) v ->
    List.In a v ->
    SIn a n (MemAcc e)
  | s_in_seq_l:
    forall i j,
    SIn a n i ->
    SIn a n (Seq i j)
  | s_in_seq_r:
    forall i j,
    SIn a n j ->
    SIn a n (Seq i j)
  | s_in_if_true:
    forall b i j,
    BData n b true ->
    SIn a n i ->
    SIn a n (If b i j)
  | s_in_if_false:
    forall b i j,
    BData n b false ->
    SIn a n j ->
    SIn a n (If b i j)
  | s_in_fork_l:
    forall i j,
    SIn a n i ->
    SIn a n (Fork i j)
  | s_in_fork_r:
    forall i j,
    SIn a n j ->
    SIn a n (Fork i j)
  | s_in_decl:
    forall e1 e2 n1 n' n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 <= n' < n2 ->
    SIn a n (i_subst x (NNum n') i) ->
    SIn a n (Decl x (e1, e2) i)
  .

  Lemma i_in_to_s_in:
    forall i,
    ~ Var TID i ->
    forall a n,
    IIn a (i_subst TID (NNum n) i) ->
    SIn a n i.
  Proof.
    intros i Hv a n Hi.
    remember (i_subst _ _ _) as j.
    generalize dependent i.
    generalize dependent n.
    induction Hi; intros n' i' Hv Heq.
    - destruct i'; inversion Heq; subst; clear Heq.
      eapply s_in_access; eauto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_seq_l; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_seq_r; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_if_true; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_if_false; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_fork_l; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      apply s_in_fork_r; auto.
    - destruct i'; inversion Heq; subst; clear Heq.
      simpl in *.
      assert (TID <> v) by auto.
      remove_eq TID v.
      destruct r as (r1, r2).
      inversion H4; subst; clear H4.
      eapply s_in_decl; eauto.
      apply IHHi.
      + intros N.
        apply var_subst_inv_1 in N.
        auto.
      + rewrite i_subst_subst_neq; auto.
  Qed.

  Lemma s_in_to_i_in:
    forall i,
    ~ Var TID i ->
    forall a n,
    SIn a n i ->
    IIn a (i_subst TID (NNum n) i).
  Proof.
    intros i Hv a n Hi.
    generalize dependent Hv.
    induction Hi; intros Hv; simpl in Hv.
    - eapply i_in_access; eauto.
    - apply i_in_seq_l; auto.
    - apply i_in_seq_r; auto.
    - apply i_in_if_true; auto.
    - apply i_in_if_false; auto.
    - apply i_in_fork_l; auto.
    - apply i_in_fork_r; auto.
    - simpl.
      assert (TID <> x) by auto.
      remove_eq TID x.
      eapply i_in_decl; eauto.
      rewrite i_subst_subst_neq; auto.
      apply IHHi.
      intros N.
      apply var_subst_inv_1 in N.
      auto.
  Qed.
  End Props.

  (* ------------------------ PAIR IN ------------------------------------- *)

  Definition IOneOf (p:access_val*access_val) i j :=
    let (v1, v2) := p in
    (IIn v1 i /\ IIn v2 j)
    \/
    (IIn v2 i /\ IIn v1 j).

  Inductive IPairIn p : inst -> Prop :=
  | i_pair_in_access e v:
    access_inst_step e v ->
    PairIn p v ->
    IPairIn p (MemAcc e)
  | i_pair_in_seq_l i j:
    IPairIn p i ->
    IPairIn p (Seq i j)
  | i_pair_in_seq_r i j:
    IPairIn p j ->
    IPairIn p (Seq i j)
  | i_pair_in_seq_both i j:
    IOneOf p i j ->
    IPairIn p (Seq i j)
  | i_pair_in_if_true b i j:
    BStep b true ->
    IPairIn p i ->
    IPairIn p (If b i j)
  | i_pair_in_if_false b i j:
    BStep b false ->
    IPairIn p j ->
    IPairIn p (If b i j)
  | i_pair_in_fork_l i j:
    IPairIn p i ->
    IPairIn p (Fork i j)
  | i_pair_in_fork_r i j:
    IPairIn p j ->
    IPairIn p (Fork i j)
  | i_pair_in_decl:
    forall n e1 e2 n1 n2 i x,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IPairIn p (i_subst x (NNum n) i) ->
    IPairIn p (Decl x (e1, e2) i).

  Lemma run_i_pair_in_to_m_pair_in:
    forall i h,
    Run i h ->
    forall p,
    IPairIn p i ->
    MPairIn p h.
  Proof.
    intros i h Hr.
    induction Hr; intros p Hi;
      inversion Hi; subst; clear Hi.
    - eauto using m_pair_in_prod_l, run_not_nil.
    - eauto using m_pair_in_prod_r, run_not_nil.
    - destruct p as (v1, v2).
      destruct H0 as [(Ha,Hb)|(Ha,Hb)];
        eapply run_i_in_to_m_in in Ha; eauto;
        eapply run_i_in_to_m_in in Hb;
        eauto using m_pair_in_prod_2, m_pair_in_prod_1.
    - assert (b = true) by eauto using b_step_fun; subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun; subst; eauto.
    - assert (v0 = v) by eauto using access_inst_step_fun; subst.
      auto using m_pair_in_eq.
    - auto using m_pair_in_app_l.
    - auto using m_pair_in_app_r.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. apply m_pair_in_app_l. eauto. }
      apply m_pair_in_app_r.
      apply IHHr2.
      eapply i_pair_in_decl with (n1:=S n1) (n2:=n2); eauto using n_step_num.
      auto with *.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n2 = n3) by eauto using n_step_fun.
      subst.
      omega.
  Qed.

  Lemma run_m_pair_in_to_i_pair_in:
    forall i h,
    Run i h ->
    forall p,
    MPairIn p h ->
    IPairIn p i.
  Proof.
    intros i h Hr.
    induction Hr; intros p Hi.
    - apply m_pair_in_nil_nil in Hi.
      contradiction.
    - apply m_pair_in_inv_prod in Hi.
      destruct Hi as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]];
        auto using i_pair_in_seq_l, i_pair_in_seq_r;
        apply i_pair_in_seq_both;
        destruct p as (v1, v2);
        simpl in *;
        eapply run_m_in_to_i_in in Ha; eauto;
        eapply run_m_in_to_i_in in Hb; eauto.
    - destruct b. {
        apply i_pair_in_if_true; auto.
      }
      apply i_pair_in_if_false; auto.
    - apply m_pair_in_inv in Hi.
      destruct Hi. {
        eauto using i_pair_in_access.
      }
      apply m_pair_in_nil in H0.
      contradiction.
    - apply m_pair_in_app_or in Hi.
      destruct Hi; auto using i_pair_in_fork_l, i_pair_in_fork_r.
    - apply m_pair_in_app_or in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply i_pair_in_decl; eauto.
      }
      apply IHHr2 in Hi.
      inversion Hi; subst; clear Hi.
      assert (S n1 = n0) by eauto using n_step_fun, n_step_num.
      assert (n3 = n2) by eauto using n_step_fun, n_step_num.
      subst.
      eapply i_pair_in_decl with (n:=n); eauto.
      auto with *.
    - apply m_pair_in_nil_nil in Hi.
      contradiction.
  Qed.


  Lemma i_pair_in_to_i_in:
    forall v1 v2 i,
    IPairIn (v1, v2) i ->
    IIn v1 i /\ IIn v2 i.
  Proof.
    intros v1 v2 i Hi.
    remember (v1, v2) as p.
    generalize dependent v1.
    generalize dependent v2.
    induction Hi; intros; subst.
    - inversion H0; subst; clear H0.
      eauto using i_in_access.
    - edestruct IHHi; eauto.
      auto using i_in_seq_l.
    - edestruct IHHi; eauto.
      auto using i_in_seq_r.
    - destruct H as [(?,?)|(?,?)]; auto using i_in_seq_l, i_in_seq_r.
    - edestruct IHHi; eauto.
      auto using i_in_if_true.
    - edestruct IHHi; eauto.
      auto using i_in_if_false.
    - edestruct IHHi; eauto.
      auto using i_in_fork_l.
    - edestruct IHHi; eauto.
      auto using i_in_fork_r.
    - edestruct IHHi; eauto.
      eauto using i_in_decl.
  Qed.

(*
  Lemma i_in_decl_seq_l:
    forall x r i a,
    IIn a (Decl x r i) ->
    forall j,
    IIn a (Decl x r (Seq i j)).
  Proof.
    intros x r i a Hi.
    remember (Decl _ _ _) as k.
    generalize dependent r.
    generalize dependent i.
    generalize dependent x.
    induction Hi; intros; inversion Heqk; subst; clear Heqk.
    - eapply i_in_decl_l; eauto.
      simpl.
      eauto using i_in_seq_l.
    - eapply i_in_decl_r; eauto.
  Qed.

  Lemma i_in_decl_seq_r:
    forall x r j a,
    IIn a (Decl x r j) ->
    forall i,
    IIn a (Decl x r (Seq i j)).
  Proof.
    intros x r i a Hi.
    remember (Decl _ _ _) as k.
    generalize dependent r.
    generalize dependent i.
    generalize dependent x.
    induction Hi; intros; inversion Heqk; subst; clear Heqk.
    - eapply i_in_decl_l; eauto.
      simpl.
      eauto using i_in_seq_r.
    - eapply i_in_decl_r; eauto.
  Qed.

  Lemma i_in_decl_if_true:
    forall n1 n n2 b i j x a,
    n1 <= n < n2 ->
    BStep (b_subst x (NNum n) b) true ->
    IIn a (Decl x (NNum n1, NNum n2) i) ->
    IIn a (Decl x (NNum n1, NNum n2) (If b i j)).
  Proof.
    intros.
    remember (Decl _ _ _) as k.
    generalize dependent b.
    generalize dependent n1.
    generalize dependent n2.
    generalize dependent n.
    generalize dependent x.
    generalize dependent i.
    generalize dependent j.
    induction H1; intros; inversion Heqk; subst; clear Heqk.
    - assert (n3 = n1) by eauto using n_step_fun, n_step_num.
      assert (n0 = n2) by eauto using n_step_fun, n_step_num.
      subst.
      eapply IHIIn in H4; eauto.
    assert (NStep (NNum n3) n3) by eauto using n_step_num.
      
  Qed.

  Lemma i_in_decl_eq:
    forall i x a n n1 n2,
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (Decl x (NNum n1, NNum n2) i).
  Proof.
    induction i; intros.
    - simpl in *.
      inversion H0.
    - simpl in *.
      inversion H0; subst; clear H0.
      + apply i_in_decl_seq_l; eauto.
      + apply i_in_decl_seq_r; eauto.
    - inversion H0; subst; clear H0.
      + eapply IHi1 in H5; eauto.
      eapply IHi1; eauto.
      inversion H0; subst; clear H0.
      + 
  Qed.
  *)
End Defs.

