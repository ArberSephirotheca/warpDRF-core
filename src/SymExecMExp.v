Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import AccExp.
Require Import Exp.
Require Import MExp.
Require Import MultiHist.
Require Import SymExec.

Import ListNotations.
Import MHistNotations.

Section Defs.
  Context {A:Access}.
  Context {I:AccessInst}.
  Notation history := (list access_val).

  Inductive ERun: inst -> mexp -> Prop :=
  | e_run_skip:
    ERun Skip (One [])
  | e_run_access:
    forall i e v hs,
    access_inst_step e v ->
    ERun i hs ->
    ERun (MemAcc e i) (Prod (One v) hs)
  | e_run_decl:
    forall r l i1 i2 x hs,
    RStep r l ->
    ERun (Branch x l i1 i2) hs ->
    ERun (Decl x r i1 i2) hs
  | e_run_branch_cons:
    forall x n l i1 i2 hs1 hs2,
    ERun (seq (i_subst x (NNum n) i1) i2) hs1 ->
    ERun (Branch x l i1 i2) hs2 ->
    ERun (Branch x (n::l) i1 i2) (Plus hs1 hs2)
  | e_run_branch_nil:
    forall x i1 i2 hs,
    ERun i2 hs ->
    ERun (Branch x [] i1 i2) hs
  | e_run_fork:
    forall i j m1 m2,
    ERun i m1 ->
    ERun j m2 ->
    ERun (Fork i j) (Plus m1 m2)
  .

  Definition FRun i m :=
    exists m', EEq m m' /\ ERun i m'.

  Infix "//" := FRun (at level 50).
  Infix ";;" := seq (at level 30).

  Lemma f_run_def:
    forall i m m',
    EEq m m' ->
    ERun i m' ->
    FRun i m.
  Proof.
    unfold FRun.
    eauto.
  Qed.

  Lemma f_run_eq:
    forall i m,
    ERun i m ->
    FRun i m.
  Proof.
    intros.
    assert (m == m) by reflexivity.
    unfold FRun; eauto.
  Qed.

  Lemma e_run_1:
    forall i e,
    ERun i e ->
    Run i (to_mem e).
  Proof.
    intros i e H.
    induction H; simpl.
    - auto using run_skip.
    - rewrite app_nil_r.
      auto using run_access.
    - eauto using run_decl.
    - eauto using run_branch_cons.
    - eauto using run_branch_nil.
    - eauto using run_fork.
  Qed.


  Lemma e_run_2:
    forall i h,
    Run i h ->
    exists e, ERun i e /\ MemEquiv h (to_mem e).
  Proof.
    intros i h H.
    induction H.
    - exists (One []).
      split.
      + apply e_run_skip.
      + simpl.
        reflexivity.
    - destruct IHRun as (e1, (Hr, R)).
      exists (Prod (One v) e1).
      split; auto using e_run_access.
      simpl.
      rewrite app_nil_r.
      repeat rewrite prepend_rw.
      apply mem_equiv_prod_r; eauto using run_not_nil, to_mem_not_nil.
      intros N.
      inversion N.
    - destruct IHRun as (e1, (Hr, R)).
      eauto using e_run_decl.
    - destruct IHRun1 as (e1, (Hr1, R1)).
      destruct IHRun2 as (e2, (Hr2, R2)).
      eexists.
      split.
      + apply e_run_branch_cons; eauto.
      + rewrite R1.
        rewrite R2.
        reflexivity.
    - destruct IHRun as (e1, (Hr1, R1)).
      eauto using e_run_branch_nil.
    - destruct IHRun1 as (m1, (Hr1, R1)).
      destruct IHRun2 as (m2, (Hr2, R2)).
      eexists.
      split.
      + eauto using e_run_fork.
      + simpl.
        rewrite R1.
        rewrite R2.
        reflexivity.
  Qed.

  Lemma e_run_inv_seq:
    forall i1 i2 m,
    ERun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ ERun i1 m1 /\ ERun i2 m2.
  Proof.
    intros.
    apply e_run_1 in H.
    apply run_inv_seq in H.
    destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
    assert (m1 <> []) by eauto using run_not_nil.
    assert (m2 <> []) by eauto using run_not_nil.
    apply e_run_2 in Hr1.
    apply e_run_2 in Hr2.
    destruct Hr1 as (m3, (Hr3, R3)).
    destruct Hr2 as (m4, (Hr4, R4)).
    exists m3.
    exists m4.
    split; auto.
    apply e_eq_iff_m_equiv.
    rewrite R1.
    simpl.
    apply mem_equiv_prod; auto using to_mem_not_nil.
  Qed.

  Lemma f_run_inv_seq:
    forall i1 i2 m,
    FRun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ FRun i1 m1 /\ FRun i2 m2.
  Proof.
    intros.
    destruct H as (m', (R1, Hr1)).
    apply e_run_inv_seq in Hr1.
    destruct Hr1 as (m1, (m2, (R2, (Hr1, Hr2)))).
    apply f_run_eq in Hr1.
    apply f_run_eq in Hr2.
    rewrite <- R1 in R2.
    eauto.
  Qed.

  Lemma f_run_1:
    forall i e,
    FRun i e ->
    exists e', e == e' /\ Run i (to_mem e').
  Proof.
    intros.
    destruct H as (m, (R, Hr)).
    apply e_run_1 in Hr.
    eauto.
  Qed.

  Lemma f_run_2: forall (i : inst) (h : list history),
    Run i h ->
    exists e, MemEquiv h (to_mem e) /\ FRun i e.
  Proof.
    intros.
    apply e_run_2 in H.
    destruct H as (e, (Hr, Hm)).
    eauto using f_run_eq.
  Qed.

  Lemma e_run_seq:
    forall i1 m1,
    ERun i1 m1 ->
    forall i2 m2,
    ERun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    apply e_run_1 in H.
    apply e_run_1 in H0.
    assert (Hr: Run (seq i1 i2) (prod (to_mem m1) (to_mem m2))) by eauto using run_seq.
    apply e_run_2 in Hr.
    destruct Hr as (e, (Hr1, Hm2)).
    apply f_run_def with (m':=e); auto.
    apply e_eq_iff_m_equiv.
    simpl.
    assumption.
  Qed.

  Import Morphisms.

  Global Instance f_run_proper_1: Proper (eq ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite H0 in R1.
      eauto using f_run_def.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite <- H0 in R1.
      eauto using f_run_def.
  Qed.

  Lemma f_run_seq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2 m3,
    FRun i2 m2 ->
    m3 == (Prod m1 m2) ->
    FRun (seq i1 i2) m3.
  Proof.
    intros.
    rewrite H1.
    destruct H as (m1', (R1, Hr1)).
    destruct H0 as (m2', (R2, Hr2)).
    rewrite R1.
    rewrite R2.
    eauto using e_run_seq.
  Qed.

  Lemma f_run_seq_eq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2,
    FRun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    eapply f_run_seq; eauto.
    reflexivity.
  Qed.

  Lemma e_run_fun:
    forall i e1,
    ERun i e1 ->
    forall e2,
    ERun i e2 ->
    e1 = e2.
  Proof.
    intros i e1 H.
    induction H; intros.
    - inversion H; subst; auto.
    - inversion H1; subst; clear H1.
      assert (v0 = v) by eauto using access_inst_step_fun.
      subst.
      apply IHERun in H6.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun.
      subst.
      eauto.
    - inversion H1; subst; clear H1.
      apply IHERun1 in H8.
      apply IHERun2 in H9.
      subst.
      reflexivity.
    - inversion H0; subst; clear H0.
      eauto.
    - inversion H1; subst; clear H1.
      erewrite IHERun1; eauto.
      erewrite IHERun2; eauto.
  Qed.

  Lemma f_run_fun:
    forall i e1,
    FRun i e1 ->
    forall e2,
    FRun i e2 ->
    e1 == e2.
  Proof.
    intros.
    destruct H as (m1, (R1, Hr1)).
    destruct H0 as (m2, (R2, Hr2)).
    transitivity m1; auto.
    assert (m2 = m1) by eauto using e_run_fun.
    subst.
    symmetry.
    assumption.
  Qed.

  Lemma f_run_branch_cons:
    forall x n l i1 i2 m1 m2 m3,
    FRun (seq (i_subst x (NNum n) i1) i2) m1 ->
    FRun (Branch x l i1 i2) m2 ->
    EEq m3 (m1 + m2) ->
    FRun (Branch x (n :: l) i1 i2) m3.
  Proof.
    intros.
    destruct H as (m1', (R1, Hr1)).
    destruct H0 as (m2', (R2, Hr2)).
    rewrite H1.
    rewrite R1.
    rewrite R2.
    eauto using f_run_eq, e_run_branch_cons. 
  Qed.

  Lemma f_run_branch_cons_eq:
    forall x n l i1 i2 m1 m2,
    FRun (seq (i_subst x (NNum n) i1) i2) m1 ->
    FRun (Branch x l i1 i2) m2 ->
    FRun (Branch x (n :: l) i1 i2) (m1 + m2).
  Proof.
    intros.
    apply f_run_branch_cons with (m1:=m1) (m2:=m2); auto.
    reflexivity.
  Qed.

  Lemma f_run_branch_nil:
    forall x i1 i2 m,
    FRun i2 m ->
    FRun (Branch x [] i1 i2) m.
  Proof.
    intros.
    destruct H as (m', (R1, Hr1)).
    rewrite R1.
    eauto using e_run_branch_nil, f_run_eq.
  Qed.

  Lemma f_run_decl:
    forall r l i1 i2 x m,
    RStep r l ->
    FRun (Branch x l i1 i2) m ->
    FRun (Decl x r i1 i2) m.
  Proof.
    intros.
    destruct H0 as (m', (Hr, R)).
    rewrite Hr.
    eauto using e_run_decl, f_run_eq.
  Qed.

  Lemma e_run_branch_seq_skip:
    forall x i1 m1 r,
    ERun (Branch x r i1 Skip) m1 ->
    forall i2 m2,
    ERun i2 m2 ->
    FRun (Branch x r i1 i2) (Prod m1 m2).
  Proof.
    intros x i1 m1 r H.
    remember (Branch _ _ _ _).
    generalize dependent Heqi.
    generalize dependent x.
    generalize dependent r.
    generalize dependent i1.
    induction H; intros; inversion Heqi; subst; clear Heqi.
    - rewrite seq_nil_rw in H.
      rewrite <- e_prod_plus_l.
      apply f_run_branch_cons_eq; eauto.
      apply f_run_seq_eq; auto using f_run_eq.
    - inversion H; subst; clear H.
      rewrite e_prod_nil_l.
      eauto using f_run_branch_nil, f_run_eq.
  Qed.

  Lemma e_run_decl_seq_skip:
    forall x r i1 i2 m1 m2,
    ERun (Decl x r i1 Skip) m1 ->
    ERun i2 m2 ->
    FRun (Decl x r i1 i2) (Prod m1 m2).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using e_run_branch_seq_skip, f_run_decl.
  Qed.

  Notation Iter x i := (fun n=> FRun (i_subst x (NNum n) i)).  
  Notation BranchMap x i l m := (Map (Iter x i) l m).
  Definition DeclMap x i n1 n2 m := BranchMap x i (range_list n1 n2) m.

  Transparent DeclMap.

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

  Lemma f_run_inv_fork:
    forall i j m,
    FRun (Fork i j) m ->
    exists m1 m2,
    m == m1 + m2 /\
    FRun i m1 /\
    FRun j m2.
  Proof.
    intros.
    destruct H as (m', (R1, Hf)).
    inversion Hf; subst; clear Hf.
    exists m1, m2.
    auto using f_run_eq.
  Qed.

  Lemma branch_map_rw:
    forall l i j x hss,
    (forall n, List.In n l ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    BranchMap x i l hss ->
    BranchMap x j l hss.
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0.
      auto using map_nil.
    }
    inversion H0; subst; clear H0.
    assert (hi: List.In a (a :: l)) by eauto using in_eq.
    assert (Hx := H _ hi); clear hi.
    assert (Hy: forall n : nat,
       List.In n l -> ProgEquiv (i_subst x (NNum n) i) (i_subst x (NNum n) j)) by auto using in_cons.
    assert (IHl := IHl i j x vs Hy H6).
    apply map_cons; auto.
    eapply prog_equiv_inv_l in H3; eauto.
  Qed.

  Lemma f_run_branch_map:
    forall l i1 i2 x m ml,
    BranchMap x i1 l ml ->
    FRun i2 m ->
    FRun (Branch x l i1 i2) (Prod (summation ml) m).
  Proof.
    induction l; intros; subst; inversion H; subst; clear H.
    - simpl.
      rewrite e_prod_nil_l.
      auto using f_run_branch_nil.
    - apply IHl with (i2:=i2) (m:=m) in H6; auto; clear IHl.
      apply f_run_seq_eq with (i1:=(i_subst x (NNum a) i1)) (m1:=v) in H0; auto.
      simpl.
      rewrite <- e_prod_plus_l.
      apply f_run_branch_cons_eq; auto.
  Qed.

  Lemma f_run_decl_map:
     forall n1 n2 i1 i2 x lm m,
     DeclMap x i1 n1 n2 lm ->
     FRun i2 m ->
     FRun (Decl x (NNum n1, NNum n2) i1 i2) (Prod (summation lm) m).
  Proof.
    eauto using f_run_branch_map, f_run_decl, r_step_range_list.
  Qed.

  Lemma decl_map_rw:
    forall n1 n2 i j x l,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    DeclMap x i n1 n2 l ->
    DeclMap x j n1 n2 l.
  Proof.
    intros.
    apply branch_map_rw with (j:=j) in H0; auto.
    intros.
    apply range_list_inv_in_2 in H1.
    auto.
  Qed.

  Lemma f_run_inv_branch_nil:
    forall x i1 i2 m,
    FRun (Branch x [] i1 i2) m ->
    FRun i2 m.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    rewrite R.
    eauto using f_run_eq.
  Qed.

  Lemma f_run_inv_branch_cons:
    forall x n l i1 i2 m,
    FRun (Branch x (n :: l) i1 i2) m ->
    exists m1 m2,
    m == (m1 + m2) /\
    FRun (seq (i_subst x (NNum n) i1) i2) m1 /\
    FRun (Branch x l i1 i2) m2.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists hs1.
    exists hs2.
    split; auto.
    split; auto using f_run_eq.
  Qed.

  Lemma f_run_branch_inv_map:
    forall l i1 i2 x m,
    FRun (Branch x l i1 i2) m ->
    NoDup l ->
    exists lm m',
    EEq m (Prod (summation lm) m')  /\
    FRun i2 m' /\ BranchMap x i1 l lm.
  Proof.
    induction l; intros. {
      apply f_run_inv_branch_nil in H.
      exists [].
      exists m.
      simpl.
      rewrite e_prod_nil_l.
      split. { reflexivity. }
      split; auto using map_nil.
    }
    apply f_run_inv_branch_cons in H.
    destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
    inversion H0; subst; clear H0.
    apply IHl in Hr2; auto; clear IHl.
    destruct Hr2 as (hss, (hs3, (R2,(Hr,Hf)))).
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m3, (m4, (R3, (Hr1, Hr2)))).
    eapply map_cons in Hf; eauto.
    exists (m3::hss).
    exists m4.
    split; auto.
    rewrite R3 in *; clear R3.
    rewrite R1 in *; clear R1.
    assert (R4: hs3 == m4) by eauto using f_run_fun.
    simpl.
    rewrite R2; clear R2.
    rewrite R4; clear R4.
    rewrite e_prod_plus_l.
    reflexivity.
  Qed.

  Lemma f_run_inv_decl:
    forall x r i1 i2 m,
    FRun (Decl x r i1 i2) m ->
    exists l,
    RStep r l /\ FRun (Branch x l i1 i2) m.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists l.
    rewrite R.
    eauto using f_run_eq.
  Qed.

  Lemma f_run_inv_decl_range:
    forall e1 e2 x i j m,
    FRun (Decl x (e1, e2) i j) m ->
    exists n1 n2,
    NStep e1 n1 /\ NStep e2 n2 /\ FRun (Decl x (NNum n1, NNum n2) i j) m.
  Proof.
    intros.
    apply f_run_inv_decl in H.
    destruct H as (l, (Hr, Hb)).
    inversion Hr; subst; clear Hr.
    exists n1, n2.
    split; auto.
    split; auto.
    eapply f_run_decl; eauto.
    eapply r_step_def; eauto using n_step_num.
  Qed.

  Lemma f_run_inv_decl_map:
    forall n1 n2 i1 i2 x m',
    FRun (Decl x (NNum n1, NNum n2) i1 i2) m' ->
    exists lm m,
    EEq m' (Prod (summation lm) m) /\
    FRun i2 m /\
    DeclMap x i1 n1 n2 lm.
  Proof.
    intros.
    apply f_run_inv_decl in H.
    destruct H as (l, (Hr, Hb)).
    apply r_step_to_range_list in Hr.
    subst.
    eauto using f_run_branch_inv_map, range_list_no_dup.
  Qed.

  Lemma f_run_decl_impl_rw:
    forall n1 n2 i j k x,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    ProgEquiv (Decl x (NNum n1, NNum n2) i k) (Decl x (NNum n1, NNum n2) j k).
  Proof.
    intros.
    split; intros.
    - apply f_run_inv_decl_map in H0.
      destruct H0 as (lm, (m', (R, (Hr1, Hr2)))).
      rewrite R; clear R m.
      eauto using decl_map_rw, f_run_decl_map. 
    - apply f_run_inv_decl_map in H0.
      destruct H0 as (lm, (m', (R, (Hr1, Hr2)))).
      rewrite R; clear R m.
      apply decl_map_rw with (j:=i) in Hr2; auto using f_run_decl_map.
      intros.
      rewrite H; auto.
      reflexivity.
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

  Lemma branch_map_inv_seq:
    forall l x i j ms1, 
    BranchMap x (seq i j) l ms1 ->
    exists ms2 ms3,
    BranchMap x i l ms2 /\ BranchMap x j l ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      eauto using map_nil, e_eq_list_nil.
    }
    inversion H; subst; clear H.
    rewrite i_subst_seq in H2.
    apply f_run_inv_seq in H2.
    destruct H2 as (hs1, (hs2, (R, (Hra, Hrb)))).
    apply IHl in H5.
    destruct H5 as (ms2, (ms3, (Hb1, (Hb2, R2)))).
    eexists.
    eexists.
    repeat split.
    - eauto using map_cons.
    - eauto using map_cons.
    - rewrite map2_cons_rw.
      auto using e_eq_list_cons.
  Qed.

  Lemma branch_map_seq:
    forall l x i j ms1 ms2, 
    BranchMap x i l ms1 ->
    BranchMap x j l ms2 ->
    BranchMap x (seq i j) l (map2 Prod ms1 ms2).
  Proof.
    induction l; intros; inversion H; inversion H0; subst; clear H H0. {
      apply map_nil.
    }
    rewrite map2_cons_rw.
    apply map_cons; auto.
    rewrite i_subst_seq.
    auto using f_run_seq_eq.
  Qed.

  Lemma decl_map_inv_seq:
    forall n1 n2 x i j ms1, 
    DeclMap x (seq i j) n1 n2 ms1 ->
    exists ms2 ms3,
    DeclMap x i n1 n2 ms2 /\ DeclMap x j n1 n2 ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    eauto using branch_map_inv_seq.
  Qed.

  Lemma decl_map_seq:
    forall n1 n2 x i j ms1 ms2, 
    DeclMap x i n1 n2 ms1 ->
    DeclMap x j n1 n2 ms2 ->
    DeclMap x (seq i j) n1 n2 (map2 Prod ms1 ms2).
  Proof.
    unfold DeclMap.
    eauto using branch_map_seq.
  Qed.

  Lemma decl_map_inv_i_subst_eq:
    forall x y i n1 n2 m1,
    ~ In x i ->
    DeclMap x (i_subst y (NVar x) i) n1 n2 m1 ->
    DeclMap y i n1 n2 m1.
  Proof.
    unfold DeclMap.
    intros x y i n1 n2 m1 Hn1 Hd.
    apply map_impl with (P:=Iter x (i_subst y (NVar x) i)); auto.
    intros.
    rewrite i_subst_subst_trans in H; auto.
  Qed.

  Lemma run_decl_seq:
    forall x n1 n2 i j k m1 m2 m3,
    FRun k m1 ->
    DeclMap x i n1 n2 m2 ->
    DeclMap x j n1 n2 m3 ->
    FRun (Decl x (NNum n1, NNum n2) (seq i j) k) (Prod (summation (map2 Prod m2 m3)) m1).
  Proof.
    intros.
    eapply f_run_decl_map; eauto.
    apply decl_map_seq; auto.
  Qed.

  Let i_subst_not_in_decl_rw:
    forall x n1 y n2 i j hs,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    FRun (i_subst x (NNum n2) (Decl y (NNum n1, NVar x) i j)) hs ->
    FRun (Decl y (NNum n1, NNum n2) i j) hs.
  Proof.
    intros.
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
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
    exists m hs,
    EEqList ms (map (fun x => (Prod (summation x) m)) hs) /\
    FRun j m /\
    Map (DeclMap y i n1) l hs.
  Proof.
    induction l; intros n i j ms x y Hn1 Hn2 Hneq Hnil Hb Hd. {
      contradiction.
    }
    clear Hnil.
    destruct l; inversion Hb; subst; clear Hb. {
      match goal with
      | [ H: FRun _ _ |- _ ] => rename H into Hr
      end.
      apply i_subst_not_in_decl_rw in Hr; auto.
      apply f_run_inv_decl_map in Hr.
      destruct Hr as (ms1, (m2, (R, (Hr, Hm)))).
      inversion H4; clear H4.
      subst.
      exists m2.
      simpl.
      exists [ms1].
      simpl.
      rewrite R.
      repeat split; auto using map_cons, map_nil.
      reflexivity.
    }
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
    end.
    apply i_subst_not_in_decl_rw in Hr; auto.
    apply f_run_inv_decl_map in Hr.
    destruct Hr as (ms1, (m2, (R, (Hr, Hm)))).
    subst.
    inversion Hd; subst; clear Hd.
    apply IHl in H4; auto; clear IHl.
    2: { intros N; inversion N. }
    destruct H4 as (m, (hs, (R1, (Hr2, Hmap)))).
    assert (m2 == m) by eauto using f_run_fun; subst. 
    exists m.
    exists (ms1::hs).
    repeat split; auto using map_cons.
    simpl.
    rewrite <- R1.
    rewrite R.
    rewrite H.
    reflexivity.
  Qed.

  Lemma decl_map_inv_decl_not_in:
    forall n1 n2 n3 i j ms x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 ms ->

    exists m hs,
    EEqList ms (map (fun x => Prod (summation x) m) hs) /\
    FRun j m /\
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
    FRun j m ->
    Map (DeclMap y i n1) l hs ->
    BranchMap x (Decl y (NNum n1, NVar x) i j) l (map (fun x => (Prod (summation x) m)) hs).
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H3; subst; clear H3.
    inversion H5; subst; clear H5.
    destruct l. {
      inversion H12; subst; clear H12.
      apply map_cons; auto using map_nil.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply f_run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    }
    apply map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply f_run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    - assumption.
    - apply IHl; auto.
      intros N; inversion N.
  Qed.

  Lemma decl_map_decl:
    forall n1 n2 n3 i j hs m x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    FRun j m ->
    Map (DeclMap y i n1) (range_list n2 n3) hs ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 (map (fun x => (Prod (summation x) m)) hs).
  Proof.
    intros.
    apply branch_map_decl; auto using range_list_no_dup, range_list_not_nil.
  Qed.

  Lemma f_run_inv_access: forall i e m,
    FRun (MemAcc e i) m ->
    exists v m', m == One v * m' /\
    access_inst_step e v /\
    FRun i m'.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists v.
    exists hs.
    eauto using f_run_eq.
  Qed.

  Lemma f_run_access:
    forall i e v m1 m2,
    access_inst_step e v ->
    FRun i m1 ->
    m2 == One v * m1 ->
    FRun (MemAcc e i) m2.
  Proof.
    intros.
    destruct H0 as (m, (R, Hr)).
    rewrite H1.
    rewrite R.
    eauto using f_run_eq, e_run_access.
  Qed.

  Lemma f_run_access_eq:
    forall i e v m,
    access_inst_step e v ->
    FRun i m ->
    FRun (MemAcc e i) (One v * m).
  Proof.
    intros.
    eapply f_run_access; eauto.
    reflexivity.
  Qed.

  Lemma f_run_skip:
    forall m,
    m == One [] ->
    FRun Skip m.
  Proof.
    intros.
    rewrite H.
    eauto using e_run_skip, f_run_eq.
  Qed.

  Lemma f_run_skip_eq:
    FRun Skip (One []).
  Proof.
    intros.
    apply f_run_skip.
    reflexivity.
  Qed.

  Lemma f_run_fork:
    forall m m1 m2 i j,
    m == m1 + m2 ->
    i // m1 ->
    j // m2 ->
    Fork i j // m.
  Proof.
    intros.
    destruct H0 as (m_i, (R_i, Hr_i)).
    destruct H1 as (m_j, (R_j, Hr_j)).
    rewrite H.
    rewrite R_i.
    rewrite R_j.
    auto using f_run_eq, e_run_fork.
  Qed.

  Lemma f_run_fork_eq:
    forall m1 m2 i j,
    i // m1 ->
    j // m2 ->
    Fork i j // (m1 + m2).
  Proof.
    intros.
    eapply f_run_fork; eauto; reflexivity.
  Qed.

  Lemma branch_map_inv_acc:
    forall l x e i ms,
    BranchMap x (MemAcc e i) l ms ->
    exists ms1 ms2,
    EEqList ms (map2 Prod ms1 ms2) /\
    BranchMap x (MemAcc e Skip) l ms1 /\
    BranchMap x i l ms2.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      exists [].
      exists [].
      split; auto using map_nil.
      apply e_eq_list_nil.
    }
    inversion H; subst; clear H.
    apply IHl in H5; clear IHl.
    destruct H5 as (ms1, (ms2, (R, (Hb1, Hb2)))).
    simpl in H2.
    apply f_run_inv_access in H2.
    destruct H2 as (v2, (m1, (R2, (Hr1, Hr2)))).
    assert (Hra: FRun (MemAcc (access_inst_subst x (NNum a) e) Skip) (One v2)). {
      eapply f_run_access with (m2:=One v2); eauto using f_run_skip_eq.
      rewrite e_prod_nil_r.
      reflexivity.
    }
    eapply map_cons in Hb1; eauto; clear Hra.
    exists (One v2 :: ms1).
    eapply map_cons in Hb2; eauto.
    exists (m1 :: ms2).
    rewrite map2_cons_rw.
    rewrite R.
    rewrite <- R2.
    split. { reflexivity. }
    auto using map_cons.
  Qed.

  Lemma decl_map_inv_acc:
    forall x e i n1 n2 ms,
    DeclMap x (MemAcc e i) n1 n2 ms ->
    exists ms1 ms2,
    EEqList ms (map2 Prod ms1 ms2) /\
    DeclMap x (MemAcc e Skip) n1 n2 ms1 /\
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
    apply f_run_inv_branch_nil in H.
    assumption.
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
    auto using f_run_branch_nil.
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
    apply f_run_inv_seq in H1.
    destruct H1 as (hs1, (hs2, (R, (Hr1, Hr2)))).
    rewrite R.
    rewrite H in *.
    rewrite H0 in *.
    auto using f_run_seq_eq.
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

  Lemma p_eq_fork:
    forall i i' j j' m,
    ProgEquiv i i' ->
    ProgEquiv j j' ->
    FRun (Fork i j) m ->
    FRun (Fork i' j') m.
  Proof.
    intros.
    apply f_run_inv_fork in H1.
    destruct H1 as (m1, (m2, (R1, (Hf1, Hf2)))).
    rewrite R1.
    rewrite H in *.
    rewrite H0 in *.
    auto using f_run_fork_eq.
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

  Lemma impl_seq_skip_1:
    forall i,
    ProgImpl i (seq i Skip).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    apply f_run_seq with (m1:=m) (m2:=One []); auto using f_run_skip_eq.
    rewrite e_prod_nil_r.
    reflexivity.
  Qed.

  Lemma f_run_inv_skip:
    forall m,
    FRun Skip m ->
    EEq m (One []). 
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    rewrite R.
    inversion Hr; subst; clear Hr.
    reflexivity.
  Qed.

  Lemma impl_seq_skip_2:
    forall i,
    ProgImpl (seq i Skip) i.
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    apply f_run_inv_seq in H.
    destruct H as (m1, (m2, (R, (Hr1, Hr2)))).
    apply f_run_inv_skip in Hr2.
    rewrite Hr2 in *; clear Hr2.
    rewrite e_prod_nil_r in R.
    rewrite R.
    assumption.
  Qed.

  Lemma prog_equiv_seq_skip:
    forall i,
    ProgEquiv (seq i Skip) i.
  Proof.
    auto using prog_equiv_def, impl_seq_skip_1, impl_seq_skip_2.
  Qed.

  Lemma prog_equiv_branch_skip:
    forall l,
    NoDup l ->
    forall x i,
    ProgEquiv (Branch x l Skip i) i.
  Proof.
    intros.
    apply prog_equiv_def; apply prog_impl_def; intros.
    - induction l; intros. {
        apply f_run_inv_branch_nil in H0.
        assumption.
      }
      apply f_run_inv_branch_cons in H0.
      destruct H0 as (m1, (m2, (R, (Hr1, Hr2)))).
      inversion H; subst; clear H.
      rewrite R in *; clear R.
      apply f_run_inv_seq in Hr1.
      destruct Hr1 as (m3, (m4, (R, (Hr3, Hr4)))).
      simpl in *.
      apply f_run_inv_skip in Hr3.
      rewrite Hr3 in *; clear Hr3.
      rewrite e_prod_nil_l in R.
      rewrite R in *.
      clear R m1.
      assert (Hb := Hr2).
      apply f_run_branch_inv_map in Hb; auto.
      destruct Hb as (lm, (m', (Hr1, (Hri, Hrb)))).
      rewrite Hr1 in *.
      assert (R : m' == m4) by eauto using f_run_fun.
      rewrite R in *; clear R m'.
      rewrite e_plus_sym in *.
      rewrite e_prod_plus_absorb_rw in *.
      apply IHl in Hr2; clear IHl; auto.
    - induction l; intros. {
        apply f_run_branch_nil; auto.
      }
      inversion H; subst; clear H.
      apply IHl in H4.
      apply f_run_branch_cons with (m1:=m) (m2:=m); auto.
      symmetry.
      apply e_plus_absorb_rw.
  Qed.

  Lemma prog_equiv_decl_skip:
    forall n1 n2 x i,
    ProgEquiv (Decl x (NNum n1, NNum n2) Skip i) i.
  Proof.  
    intros.
    apply prog_equiv_def; apply prog_impl_def; intros.
    - apply f_run_inv_decl in H.
      destruct H as (l, (Hr, Hb)).
      rewrite prog_equiv_branch_skip in Hb; eauto using r_step_no_dup.
    - apply f_run_decl with (l:=range_list n1 n2); auto using r_step_range_list.
      rewrite prog_equiv_branch_skip; auto using range_list_no_dup.
  Qed.


  Definition range_list_2d_inner n : list (nat*nat) :=
    List.map (pair n) (range_list 0 n).

  Definition range_list_2d n1 n2 :=
    List.flat_map range_list_2d_inner (range_list n1 n2).

  Definition Iter2d x y i (p:nat*nat) :=
    let (nx,ny) := p in
    FRun
      (i_subst y (NNum ny)
        (i_subst x (NNum nx) i))
  .

  Lemma f_run_branch_map_2d_inner:
    forall ks vs x y i n,
    Map (Iter2d x y i) (map (pair n) ks) vs ->
    FRun
      (Branch y ks (i_subst x (NNum n) i) Skip)
      (summation vs).
  Proof.
    induction ks; intros. {
      inversion H; subst; clear H.
      apply f_run_branch_nil.
      apply f_run_skip_eq.
    }
    inversion H; subst; clear H.
    simpl in *.
    apply IHks in H5.
    apply f_run_branch_cons_eq; auto.
    rewrite prog_equiv_seq_skip.
    assumption.
  Qed.

  Lemma f_run_inv_branch_map_2d_inner:
    forall ks x y i n m,
    NoDup ks ->
    FRun
      (Branch y ks (i_subst x (NNum n) i) Skip)
      m ->
    exists vs,
    m == summation vs /\
    Map (Iter2d x y i) (map (pair n) ks) vs.
  Proof.
    induction ks; intros. {
      simpl.
      apply f_run_inv_branch_nil in H0.
      apply f_run_inv_skip in H0.
      exists [].
      rewrite H0.
      split; auto using map_nil.
      reflexivity.
    }
    apply f_run_inv_branch_cons in H0.
    destruct H0 as (m1, (m2, (Hr1, (Hr2, Hr3)))).
    apply IHks in Hr3.
    destruct Hr3 as (vs, (R3, Hm)).
    exists (m1 :: vs).
    rewrite Hr1; clear Hr1.
    rewrite R3; clear R3.
    split. { reflexivity. }
    simpl.
    apply map_cons; auto.
    - unfold Iter2d.
      rewrite prog_equiv_seq_skip in Hr2.
      assumption.
    - intros N.
      inversion H; subst; clear H.
      contradict H2.
      apply in_map_iff in N.
      destruct N as (m', (R, Hi)).
      inversion R; subst; clear R.
      assumption.
    - inversion H; subst; auto.
  Qed.

  Lemma f_run_inv_decl_map_2d_inner:
    forall x y i n m,
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i) Skip) m ->
    exists l,
    m == summation l /\
    Map (Iter2d x y i) (range_list_2d_inner n) l.
  Proof.
    intros.
    apply f_run_inv_decl in H.
    destruct H as (lm, (Hr, Hb)).
    apply r_step_to_range_list in Hr.
    subst.
    apply f_run_inv_branch_map_2d_inner in Hb;
      auto using range_list_no_dup.
  Qed.

  Lemma f_run_decl_map_2d_inner:
    forall x y i n l,
    Map (Iter2d x y i) (range_list_2d_inner n) l ->
    FRun (Decl y (NNum 0, NNum n) (i_subst x (NNum n) i) Skip) (summation l).
  Proof.
    intros.
    apply f_run_decl with (l:=range_list 0 n); auto using r_step_range_list.
    unfold range_list_2d_inner in H.
    auto using f_run_branch_map_2d_inner.
  Qed.


  Lemma f_run_branch_map_2d:
    forall ks x y i l,
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l ->
    x <> y ->
    FRun (Branch x ks (Decl y (NNum 0, NVar x) i Skip) Skip) (summation l).
  Proof.
    induction ks; intros. {
      simpl in *.
      inversion H; subst; clear H.
      apply f_run_branch_nil.
      apply f_run_skip_eq.
    }
    simpl in *.
    apply map_inv_app in H.
    destruct H as (l1', (l2', (?, (Hm1, Hm2)))).
    subst.
    apply IHks in Hm2.
    eapply f_run_branch_cons; eauto.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      apply f_run_decl_map_2d_inner; eauto.
    - rewrite e_summation_app.
      reflexivity.
    - assumption.
  Qed.

  Lemma no_dup_flat_map_range_2d_inner:
    forall l,
    NoDup l ->
    NoDup (flat_map range_list_2d_inner l).
  Proof.
    induction l; intros. {
      simpl.
      apply NoDup_nil.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl in H3; clear IHl.
    unfold range_list_2d_inner.
    apply no_dup_app; auto using range_list_no_dup, no_dup_map_pair.
    intros.
    apply in_map_iff in H.
    destruct H as (m, (R, Hi)).
    subst.
    apply in_flat_map in H0.
    destruct H0 as (y, (Hj, Hk)).
    apply in_map_iff in Hk.
    destruct Hk as (z, (R, Hk)).
    inversion R; subst; clear R.
    contradiction.
  Qed.

  Lemma f_run_inv_branch_map_2d:
    forall ks x y i m,
    FRun (Branch x ks (Decl y (NNum 0, NVar x) i Skip) Skip) m ->
    x <> y ->
    NoDup ks ->
    exists l,
    EEq m (summation l) /\
    Map (Iter2d x y i) (flat_map range_list_2d_inner ks) l.
  Proof.
    induction ks; intros. {
      apply f_run_inv_branch_nil in H.
      apply f_run_inv_skip in H.
      exists [].
      rewrite H.
      split. { reflexivity. }
      simpl.
      apply map_nil.
    }
    apply f_run_inv_branch_cons in H.
    inversion H1; subst; clear H1.
    destruct H as (m1, (m2, (R1, (Ha, Hb)))).
    rewrite prog_equiv_seq_skip in Ha.
    apply IHks in Hb; auto.
    destruct Hb as (lm2, (R2, Hm2)).
    simpl in Ha.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
    apply f_run_inv_decl_map_2d_inner in Ha.
    destruct Ha as (lm1, (R3, Hm1)).
    exists (lm1 ++ lm2).
    split. {
      rewrite R1.
      rewrite R2.
      rewrite R3.
      rewrite e_summation_app.
      reflexivity.
    }
    remember (flat_map range_list_2d_inner (a :: ks)) as fl.
    rewrite Heqfl.
    simpl.
    apply map_app; auto.
    assert (R: range_list_2d_inner a ++ flat_map range_list_2d_inner ks
      = fl). {
      subst.
      reflexivity.
    }
    rewrite R.
    rewrite Heqfl.
    auto using no_dup_flat_map_range_2d_inner, NoDup_cons.
  Qed.

  Lemma f_run_decl_map_2d:
    forall x y i n1 n2 l,
    x <> y ->
    Map (Iter2d x y i) (range_list_2d n1 n2) l ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i Skip) Skip)
      (summation l).
  Proof.
    intros.
    apply f_run_decl with (l:=range_list n1 n2).
    - auto using r_step_range_list.
    - unfold range_list_2d in H.
      auto using f_run_branch_map_2d.
  Qed.

  Lemma f_run_inv_decl_map_2d:
    forall x y i n1 n2 m,
    x <> y ->
    FRun (Decl x (NNum n1, NNum n2) (Decl y (NNum 0, NVar x) i Skip) Skip)
      m ->
    exists l,
    EEq m (summation l) /\
    Map (Iter2d x y i) (range_list_2d n1 n2) l.
  Proof.
    intros.
    apply f_run_inv_decl in H0.
    destruct H0 as (l, (Hr, Hb)).
    unfold range_list_2d.
    apply r_step_to_range_list in Hr.
    subst.
    apply f_run_inv_branch_map_2d in Hb; auto using range_list_no_dup.
  Qed.


  Lemma rw_branch_cons:
    forall x n l i j,
    ProgEquiv (Branch x (n::l) i j)
              (Fork (seq (i_subst x (NNum n) i) j) (Branch x l i j)).
  Proof.
    split; intros.
    - apply f_run_inv_branch_cons in H.
      destruct H as (m1, (m2, (R, (Hr1, Hr2)))).
      eapply f_run_fork; eauto.
    - apply f_run_inv_fork in H.
      destruct H as (m1, (m2, (R, (Hr1, Hr2)))).
      eauto using f_run_branch_cons.
  Qed.

  Lemma rw_fork_assoc:
    forall i j k,
    ProgEquiv (Fork i (Fork j k))
              (Fork (Fork i j) k).
  Proof.
    split; intros.
    - apply f_run_inv_fork in H.
      destruct H as (mi, (m2, (R1, (Hr1, Hr2)))).
      rewrite R1; clear m R1.
      apply f_run_inv_fork in Hr2.
      destruct Hr2 as (mj, (mk, (R1, (Hr3, Hr4)))).
      rewrite R1; clear R1 m2.
      eapply f_run_fork with (m1:=mi + mj); eauto.
      { apply e_plus_assoc. }
      auto using f_run_fork_eq.
    - apply f_run_inv_fork in H.
      destruct H as (mi_mj, (mk, (R1, (Hr1, Hr2)))).
      rewrite R1; clear m R1.
      apply f_run_inv_fork in Hr1.
      destruct Hr1 as (mi, (mj, (R1, (Hr3, Hr4)))).
      rewrite R1; clear R1 mi_mj.
      eapply f_run_fork with (m2:=mj + mk); eauto.
      { rewrite e_plus_assoc. reflexivity. }
      auto using f_run_fork_eq.
  Qed.

  Lemma p_eq_fork_branch:
    forall x l i j,
    ProgEquiv (Fork j (Branch x l i j))
              (Branch x l i j).
  Proof.
    split; intros.
    + apply f_run_inv_fork in H.
      destruct H as (mj, (mb, (R, (Hr1, Hr2)))).
      rewrite R; clear R m.
      rewrite seq_branch_rw in Hr2.
      assert (Hb := Hr2).
      apply f_run_inv_seq in Hr2.
      destruct Hr2 as (mi, (mj', (R, (Hr2, Hr3)))).
      rewrite R in *; clear R mb.
      assert (R: mj' == mj) by eauto using f_run_fun.
      rewrite R in *; clear R mj'.
      rewrite e_plus_sym.
      rewrite e_prod_plus_absorb_rw.
      assumption.
    + rewrite seq_branch_rw in H.
      assert (Hb := H).
      apply f_run_inv_seq in H.
      destruct H as (mi, (mj, (R, (Hr1, Hr2)))).
      rewrite R in *; clear R m.
      apply f_run_fork with (m1:=mj) (m2:=mi*mj); auto.
      rewrite e_plus_sym.
      rewrite e_prod_plus_absorb_rw.
      reflexivity.
  Qed.

  Lemma rw_branch_app:
    forall x l1 l2 i j,
    ProgEquiv (Branch x (l1 ++ l2) i j)
              (Fork (Branch x l1 i j) (Branch x l2 i j)).
  Proof.
    split; intros.
    - generalize dependent l2.
      generalize dependent i.
      generalize dependent j.
      generalize dependent x.
      generalize dependent m.
      induction l1; intros. {
        rewrite p_eq_branch_nil.
        simpl in *.
        rewrite p_eq_fork_branch.
        assumption.
      }
      simpl in *.
      apply f_run_inv_branch_cons in H.
      destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
      apply IHl1 in Hr2; clear IHl1.
      rewrite rw_branch_cons.
      rewrite R1; clear R1 m.
      assert
        (FRun (Fork (i_subst x (NNum a) i;; j)  (Fork (Branch x l1 i j) (Branch x l2 i j))) (m1 + m2)). {
        auto using f_run_fork_eq.
      }
      apply rw_fork_assoc.
      assumption.
    - generalize dependent l2.
      generalize dependent i.
      generalize dependent j.
      generalize dependent x.
      generalize dependent m.
      induction l1; intros. {
        simpl in *.
        rewrite p_eq_branch_nil in *.
        rewrite p_eq_fork_branch in H.
        assumption.
      }
      simpl.
      apply f_run_inv_fork in H.
      destruct H as (mb1, (m2, (R, (Hb1, Hb2)))).
      rewrite R in *.
      clear R m.
      apply f_run_inv_branch_cons in Hb1.
      destruct Hb1 as (mi, (mb2, (R, (Hri, Hrb2)))).
      rewrite R; clear R mb1.
      assert (Hf := f_run_fork_eq _ _ _ _ Hrb2 Hb2); clear Hrb2 Hb2.
      apply IHl1 in Hf; clear IHl1.
      rewrite <- e_plus_assoc.
      apply f_run_branch_cons_eq; auto.
  Qed.

  Lemma rw_decl_branch:
    forall x r i j l,
    RStep r l ->
    ProgEquiv (Decl x r i j) (Branch x l i j).
  Proof.
    split; intros.
    - apply f_run_inv_decl in H0.
      destruct H0 as (l', (Hr1, Hb)).
      assert (l' = l) by eauto using r_step_fun.
      subst.
      assumption.
    - eauto using f_run_decl.
  Qed.

  Lemma rw_decl_plus:
    forall x ub1 ub2 lb i j n_lb n_ub1,
    NStep lb n_lb ->
    NStep ub1 n_ub1 ->
    n_lb < n_ub1 ->
    ProgEquiv (Decl x (lb, (NBin NPlus ub1 ub2)) i j)
              (Fork (Decl x (lb, ub1) i j) (Decl x (ub1, (NBin NPlus ub1 ub2)) i j)).
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

End Defs.