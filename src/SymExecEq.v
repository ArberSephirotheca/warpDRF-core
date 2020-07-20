Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import AccExp.
Require Import Exp.
Require Import MExp.
Require Import MultiHist.
Require Import SymExec2.
Require Import SymExecMRun.

Import ListNotations.
Import MHistNotations.

(*

  Module that allows reasoning in terms of program equivalence
  (according to point-wise pairs).
  
 *) 

Section Defs.
  Context {A:Access}.
  Context {I:AccessInst}.
  Notation history := (list access_val).


  Definition ProgImpl i j : Prop :=
    forall m,
    FRun i m ->
    FRun j m.

  Lemma prog_impl_def:
    forall i j,
    (forall m, FRun i m -> FRun j m) ->
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
    auto.
  Qed.

  Lemma prog_impl_trans:
    forall i j k,
    ProgImpl i j ->
    ProgImpl j k ->
    ProgImpl i k.
  Proof.
    unfold ProgImpl.
    intros.
    eauto.
  Qed.

  (** Register [ProgImpl] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgImpl
    reflexivity proved by prog_impl_refl
    transitivity proved by prog_impl_trans
    as prog_impl_setoid.

  Definition ProgEquiv i j : Prop :=
    forall m, FRun i m <-> FRun j m.

  Infix "~>" := ProgImpl (at level 40).
  Infix "~~" := ProgEquiv (at level 40).

  Lemma prog_equiv_def:
    forall i j,
    ProgImpl i j ->
    ProgImpl j i ->
    ProgEquiv i j.
  Proof.
    split; auto.
  Qed.

  Lemma prog_equiv_inv_l:
    forall i m j,
    FRun i m ->
    ProgEquiv i j ->
    FRun j m.
  Proof.
    intros.
    apply H0 in H.
    assumption.
  Qed.

  Lemma prog_equiv_inv_r:
    forall i m j,
    FRun j m ->
    ProgEquiv i j ->
    FRun i m.
  Proof.
    intros.
    apply H0 in H.
    auto.
  Qed.

  Lemma prog_equiv_refl:
    forall i,
    ProgEquiv i i.
  Proof.
    intros.
    unfold ProgEquiv.
    intuition.
  Qed.

  Lemma prog_equiv_sym:
    forall i j,
    ProgEquiv i j ->
    ProgEquiv j i.
  Proof.
    unfold ProgEquiv.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma prog_equiv_trans:
    forall i j k,
    ProgEquiv i j ->
    ProgEquiv j k ->
    ProgEquiv i k.
  Proof.
    unfold ProgEquiv.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgEquiv
    reflexivity proved by prog_equiv_refl
    symmetry proved by prog_equiv_sym
    transitivity proved by prog_equiv_trans
    as prog_equiv_setoid.

  Import Morphisms.

  Global Instance f_run_proper_2: Proper (ProgEquiv ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - rewrite H0 in H1.
      apply H in H1.
      assumption.
    - rewrite <- H0 in H1.
      apply H in H1.
      assumption.
  Qed.


(*
  Lemma impl_branch_seq_1:
    forall x l i j k,
    ~ In x i ->
    l <> [] ->
    ProgImpl
      (Branch x l (Seq i j))
      (Seq i (Branch x l j)).
  Proof.
    unfold ProgImpl.
    induction l. {
      intros.
      contradiction.
    }
    intros i j k Hnin _ m1 Hr1.
    destruct l. {
      clear IHl.
      apply f_run_inv_branch_cons in Hr1.
      destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
      rewrite R1; clear R1.
      apply f_run_inv_branch_nil in Hr2.
      repeat rewrite i_subst_seq in Hr1.
      rewrite i_subst_not_in in Hr1; eauto.
      apply f_run_inv_seq in Hr1.
      destruct Hr1 as (m4, (m5, (R1, (Hr1, Hr3)))).
      rewrite R1; clear R1.
      assert (R1: m5 == m3) by eauto using f_run_fun.
      rewrite R1 in *; clear R1 Hr3.
      clear m1 m2 m5.
      apply f_run_inv_seq in Hr1.
      destruct Hr1 as (m1, (m2, (R, (Hr3, Hr4)))).
      rewrite R; clear R.
      assert (Hb: Branch x [a] j k // (m2 * m3)). {
        assert (i_subst x (NNum a) j ;; k // (m2 * m3)) by eauto using f_run_seq_eq.
        eapply f_run_branch_cons; eauto using f_run_branch_nil.
        rewrite e_prod_plus_absorb_rw.
        reflexivity.
      }
      rewrite e_prod_plus_absorb_rw.
      rewrite e_prod_assoc.
      auto using f_run_seq_eq.
    }
    apply f_run_inv_branch_cons in Hr1.
    destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
    rewrite R1; clear R1 m1.
    assert (Hne2: n :: l <> []). {
      intros N.
      inversion N.
    }
    apply IHl in Hr2; eauto; clear IHl Hne2.
    repeat rewrite i_subst_seq in Hr1.
    rewrite i_subst_not_in in Hr1; eauto.
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m1, (m4, (R, (Hr1, Hr3)))).
    rewrite R; clear R m2.
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m2, (m5, (R, (Hr1, Hr4)))).
    rewrite R; clear R m1.
    apply f_run_inv_seq in Hr2.
    destruct Hr2 as (m1, (m6, (R, (Hr2, Hr5)))).
    rewrite R; clear R m3.
    assert (R: m2 == m1) by eauto using f_run_fun.
    rewrite R in *; clear R m2 Hr2.
    rewrite e_prod_assoc.
    rewrite e_prod_plus_r.
    apply f_run_seq_eq; auto.
    apply f_run_branch_cons_eq; auto.
    apply f_run_seq_eq; auto.
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
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
    rewrite R1; clear R1 m1.
    apply f_run_inv_branch_cons in Hr2.
    destruct Hr2 as (m1, (m4, (R, (Hr2, Hr3)))).
    rewrite R; clear R m3.
    apply f_run_inv_seq in Hr2.
    destruct Hr2 as (m3, (m5, (R, (Hr2, Hr4)))).
    rewrite R; clear R m1.
    destruct l. {
      clear IHl.
      apply f_run_inv_branch_nil in Hr3.
      assert (R: m4 == m5) by eauto using f_run_fun.
      rewrite R in *; clear R m4 Hr4.
      rewrite e_prod_plus_absorb_rw.
      apply f_run_branch_cons with (m1:=m2 * m3 * m5) (m2:=m5).
      + rewrite i_subst_seq.
        rewrite i_subst_not_in; auto.
        auto using f_run_seq_eq.
      + auto using f_run_branch_nil.
      + rewrite e_prod_plus_absorb_rw.
        rewrite e_prod_assoc.
        reflexivity.
    }
    assert (Hr: i ;; Branch x (n :: l) j k // m2 * m4)
      by auto using f_run_seq_eq.
    clear Hr3.
    assert (Hne: n :: l <> []) by (intros N; inversion N).
    apply IHl in Hr; auto; clear Hne IHl.
    apply f_run_branch_cons with (m1:=m2*m3*m5) (m2 := m2 * m4); auto.
    + rewrite i_subst_seq.
      rewrite i_subst_not_in; auto using f_run_seq_eq.
    + rewrite e_prod_assoc.
      rewrite e_prod_plus_r.
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
    auto using prog_equiv_def, impl_branch_seq_1, impl_branch_seq_2.
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
    apply prog_equiv_def; apply prog_impl_def; intros. {
      apply f_run_inv_decl in H1.
      destruct H1 as (l, (Hr, Hb)).
      assert (Hrs := Hr).
      apply r_step_to_range_list in Hr; subst.
      apply equiv_i_subst_branch_seq in Hb; auto using range_list_not_nil.
      apply f_run_inv_seq in Hb.
      destruct Hb as (m1, (m2, (R, (Hr1, Hr2)))).
      rewrite R; clear R m.
      eapply f_run_decl in Hr2; eauto.
      apply f_run_seq_eq; eauto using f_run_decl.
    }
    apply f_run_inv_seq in H1.
    destruct H1 as (m1, (m2, (R, (Hr1, Hr2)))).
    rewrite R; clear R m.
    apply f_run_inv_decl in Hr2.
    destruct Hr2 as (l, (Hrs, Hb)).
    assert (Hr := Hrs).
    apply r_step_to_range_list in Hr; subst.
    apply f_run_seq_eq with (i1:=i) (m1:=m1) in Hb; auto.
    apply equiv_i_subst_branch_seq in Hb; auto using range_list_not_nil.
    eapply f_run_decl in Hb; eauto.
  Qed.
*)

  Lemma p_eq_branch_nil:
    forall x i r,
    RPred (ge) r -> 
    ProgEquiv (Decl x r i) Skip.
  Proof.
    split; intros.
    - intros.
      apply f_run_inv_decl_nil in H0; auto.
      auto using f_run_skip.
    - inversion H0; subst; clear H0.
      auto using f_run_decl_r_pred_ge.
  Qed.

  Import Morphisms.

  Lemma p_eq_seq_impl:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgImpl (Seq i1 j1) (Seq i2 j2).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    inversion H1; subst; clear H1.
    rewrite H7.
    rewrite H in *.
    rewrite H0 in *.
    auto using f_run_seq_eq.
  Qed.

  Lemma p_eq_seq:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgEquiv (Seq i1 j1) (Seq i2 j2).
  Proof.
    intros.
    apply prog_equiv_def.
    - auto using p_eq_seq_impl.
    - symmetry in H.
      symmetry in H0.
      auto using p_eq_seq_impl.
  Qed.

  Global Instance seq_p_equiv_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgEquiv) Seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq.
  Qed.

  Global Instance seq_p_impl_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgImpl) Seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq_impl.
  Qed.

  Lemma prog_equiv_split:
    forall i j,
    i ~~ j ->
    i ~> j /\ j ~> i.
  Proof.
    intros.
    unfold ProgEquiv, ProgImpl in *.
    intuition.
    - apply H.
      assumption.
    - apply H.
      assumption.
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
    apply prog_equiv_split in H.
    destruct H.
    apply prog_equiv_split in H0.
    destruct H0.
    transitivity i2; auto.
    transitivity j2; auto.
  Qed.

  (* -------------------------------- FORK ----------------------- *)

  Lemma p_eq_fork:
    forall i i' j j' m,
    ProgEquiv i i' ->
    ProgEquiv j j' ->
    FRun (Fork i j) m ->
    FRun (Fork i' j') m.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    rewrite H7.
    rewrite H in *.
    rewrite H0 in *.
    apply f_run_fork_eq; auto.
  Qed.

  Global Instance fork_p_eq_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgEquiv) Fork.
  Proof.
    unfold Proper, respectful.
    split; intros.
    - eauto using p_eq_fork.
    - symmetry in H.
      symmetry in H0.
      eauto using p_eq_fork.
  Qed.

  Lemma p_eq_fork_assoc:
    forall i j k,
    ProgEquiv (Fork i (Fork j k))
              (Fork (Fork i j) k).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite H5; clear H5 m.
      inversion H3; subst; clear H3.
      rewrite H6 in *; clear H6 m2.
      rewrite e_plus_assoc.
      auto using f_run_fork_eq.
    - inversion H; subst; clear H.
      rewrite H5; clear H5 m.
      inversion H2; subst; clear H2.
      rewrite H6; clear H6 m1.
      rewrite <- e_plus_assoc.
      auto using f_run_fork_eq.
  Qed.

  Lemma p_eq_fork_sym:
    forall i j,
    ProgEquiv (Fork i j) (Fork j i).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite H5; clear H5.
      rewrite e_plus_sym.
      auto using f_run_fork_eq.
    - inversion H; subst; clear H.
      rewrite H5; clear H5.
      rewrite e_plus_sym.
      auto using f_run_fork_eq.
  Qed.

  Lemma p_eq_fork_skip_l:
    forall i,
    ProgEquiv (Fork Skip i) i.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite H5; clear H5 m.
      inversion H2; subst; clear H2.
      rewrite H.
      rewrite e_plus_nil_l.
      assumption.
    - apply f_run_fork with (m1:=One []) (m2:=m); auto using f_run_skip_eq.
      rewrite e_plus_nil_l.
      reflexivity.
  Qed.

  Lemma p_eq_fork_skip_r:
    forall i,
    ProgEquiv (Fork i Skip) i.
  Proof.
    intros.
    rewrite p_eq_fork_sym.
    rewrite p_eq_fork_skip_l.
    reflexivity.
  Qed.

  (* ---------------------------- SEQ ---------------------------- *)

  Lemma p_eq_seq_skip_l:
    forall i,
    ProgEquiv (Seq i Skip) i.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite H5.
      inversion H3; subst; clear H3.
      rewrite H in *.
      rewrite e_prod_nil_r.
      assumption.
    - apply f_run_seq with (m1:=m) (m2:=One []); auto using f_run_skip_eq.
      rewrite e_prod_nil_r.
      reflexivity.
  Qed.

  Lemma p_eq_seq_skip_r:
    forall i,
    ProgEquiv (Seq Skip i) i.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      rewrite H5; clear H5.
      inversion H2; subst; clear H2.
      rewrite H; subst; clear H.
      rewrite e_prod_nil_l.
      assumption.
    - eapply f_run_seq; eauto using f_run_skip_eq.
      rewrite e_prod_nil_l.
      reflexivity.
  Qed.

  (* ------------------------ DECL --------------------------- *)

(*
  Lemma p_eq_branch_cons:
    forall x n l i,
    RPred (lt) r ->
    ProgEquiv (Decl x r i)
              (Fork (i_subst x (NNum n) i) (Branch x l i)).
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      eapply f_run_fork; eauto.
    - inversion H; subst; clear H.
      eauto using f_run_branch_cons.
  Qed.
*)
(*
  Lemma p_eq_branch_app:
    forall x l1 l2 i,
    ProgEquiv (Branch x (l1 ++ l2) i)
              (Fork (Branch x l1 i) (Branch x l2 i)).
  Proof.
    split; intros.
    - generalize dependent l2.
      generalize dependent i.
      generalize dependent x.
      generalize dependent m.
      induction l1; intros. {
        rewrite p_eq_branch_nil.
        simpl in *.
        rewrite p_eq_fork_skip_l.
        assumption.
      }
      simpl in *.
      rewrite p_eq_branch_cons in *.
      inversion H; subst; clear H.
      rewrite H5; clear H5 m.
      apply IHl1 in H3.
      inversion H3; subst; clear H3.
      rewrite H6; clear H6.
      rewrite e_plus_assoc.
      auto using f_run_fork_eq.

    - generalize dependent l2.
      generalize dependent i.
      generalize dependent x.
      generalize dependent m.
      induction l1; intros. {
        simpl in *.
        rewrite p_eq_branch_nil in *.
        rewrite p_eq_fork_skip_l in *.
        assumption.
      }
      simpl.
      rewrite p_eq_branch_cons in *.
      inversion H; subst; clear H.
      rewrite H5; clear H5.
      inversion H2; subst; clear H2.
      rewrite H6.
      rewrite <- e_plus_assoc.
      eauto using f_run_fork_eq.
  Qed.

  Lemma p_eq_decl_branch:
    forall x r i l,
    RStep r l ->
    ProgEquiv (Decl x r i) (Branch x l i).
  Proof.
    split; intros.
    - inversion H0; subst; clear H0.
      assert (l0 = l) by eauto using r_step_fun.
      subst.
      assumption.
    - eauto using f_run_decl.
  Qed.
(*
  Lemma p_eq_decl_plus:
    forall x ub1 ub2 lb i n_lb n_ub1,
    NStep lb n_lb ->
    NStep ub1 n_ub1 ->
    n_lb < n_ub1 ->
    ProgEquiv (Decl x (lb, (NBin NPlus ub1 ub2)) i)
              (Fork (Decl x (lb, ub1) i) (Decl x (ub1, (NBin NPlus ub1 ub2)) i)).
  Proof.
    split; intros.
    - apply f_run_inv_decl in H2.
      destruct H2 as (l1, (Hr1, Hb)).
      inversion Hr1; subst; clear Hr1.
      match goal with
        H: NStep (NBin _ _ _) _ |- _ =>
          apply n_step_inv_plus in H;
          destruct H as (n_ub1', (n_ub2, (?, (H_ub1, H_ub2))))
      end.
      assert (n_ub1' = n_ub1) by eauto using n_step_fun.
      assert (n1 = n_lb) by eauto using n_step_fun.
      subst.
      match goal with
        H : RangeList _ _ _ |- _ =>
        apply range_list_inv_plus_l_1 in H; auto with *;
        destruct H as (l1_1, (l1_2, (?, (Hr1, Hr2))))
      end.
      subst.
      assert (RStep (lb, ub1) l1_1) by eauto using r_step_def.
      assert (RStep (ub1, NBin NPlus ub1 ub2) l1_2) by
        eauto using n_step_add, r_step_def.
      erewrite rw_decl_branch; eauto.
      erewrite rw_decl_branch; eauto.
      apply rw_branch_app; assumption.
    - apply f_run_inv_fork in H2.
      destruct H2 as (m_lb_ub1, (m_ub1_ub2, (R, (Hd1, Hd2)))).
      rewrite R; clear R m.
      apply f_run_inv_decl in Hd1.
      apply f_run_inv_decl in Hd2.
      destruct Hd1 as (l1, (Hr_l1, Hb_l1)).
      destruct Hd2 as (l2, (Hr_l2, Hb_l2)).
      eapply f_run_decl.
      2: {
        apply rw_branch_app.
        apply f_run_fork_eq; eauto.
      }
      inversion Hr_l2; subst; clear Hr_l2.
      assert (n1 = n_ub1) by eauto using n_step_fun; subst.
      eapply r_step_def; eauto.
      apply n_step_inv_plus in H5.
      destruct H5 as (n_ub1', (n_ub2, (?, (Hn1', Hn2')))).
      assert (n_ub1' = n_ub1) by eauto using n_step_fun.
      subst.
      apply range_list_plus_l_1; auto.
      inversion Hr_l1; subst; clear Hr_l1.
      assert (n1 = n_lb) by eauto using n_step_fun.
      assert (n2 = n_ub1) by eauto using n_step_fun.
      subst.
      assumption.
  Qed.
*)
*)
End Defs.