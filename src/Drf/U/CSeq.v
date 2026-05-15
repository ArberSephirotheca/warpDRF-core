From Faial.Core Require Import Var.
From Faial.Core Require Import AVal.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Util.
From Faial.Core Require Import PairInUtil.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Hist.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Pure.N.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.
From Faial.Drf.U Require Import Free.
From Faial.Drf.U Require Import Run.
From Faial.Drf.U Require Import IIn.
From Faial.Drf.U Require Import CIn.

Section Defs.
  Context `{T:Tasks}.

  Fixpoint c_seq (c1:inst) (c2:inst) :=
    match c1 with
    | Skip
    | If _ _ _
    | MemAcc _
    | For _ _ _
      => Seq c1 c2
    | Seq c1 c3 => c_seq c1 (c_seq c3 c2)
    end.

  Definition is_seq c :=
    match c with
    | Skip
    | If _ _ _
    | MemAcc _
    | For _ _ _
      => false
    | Seq _ _ => true
    end.

  Inductive CSeq : inst -> inst -> inst -> Prop :=
  | c_seq_1:
    forall c1 c2,
    is_seq c1 = false ->
    CSeq c1 c2 (Seq c1 c2)
  | c_seq_2:
    forall c1 c2 c3 c3_c2 c1_c3_c2,
    CSeq c3 c2 c3_c2 ->
    CSeq c1 c3_c2 c1_c3_c2 ->
    CSeq (Seq c1 c3) c2 c1_c3_c2.

  Lemma c_seq_to_prop:
    forall c1 c2 c3,
    c_seq c1 c2 = c3 ->
    CSeq c1 c2 c3.
  Proof.
    induction c1; intros; simpl in *; subst; try (apply c_seq_1; auto; fail).
    eapply c_seq_2; eauto.
  Qed.

  Lemma c_seq_from_prop:
    forall c1 c2 c3,
    CSeq c1 c2 c3 ->
    c_seq c1 c2 = c3.
  Proof.
    intros c1 c2 c3 H.
    induction H; simpl in *.
    - destruct c1; simpl in *; auto.
      inversion H.
    - rewrite IHCSeq1.
      rewrite IHCSeq2.
      reflexivity.
  Qed.

  Lemma c_seq_seq:
    forall c1 c2 c3,
    c_seq (c_seq c1 c2) c3 = c_seq c1 (c_seq c2 c3).
  Proof.
    induction c1; intros; simpl; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    auto.
  Qed.

  Lemma c_in_c_seq_r:
    forall a c1 c2,
    CIn a c2 ->
    CIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_in_seq_r.
  Qed.

  Lemma c_in_c_seq_l:
    forall a c1,
    CIn a c1 ->
    forall c2,
    CIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_in_seq_l.
    apply c_in_inv_seq in H.
    destruct H as [H|H].
    - auto using IHc1_1.
    - eapply IHc1_2 with (c2:=c2) in H; eauto using c_in_c_seq_r.
  Qed.

  Lemma c_seq_eq_seq:
    forall c1 c2,
    exists c1' c2', c_seq c1 c2 = Seq c1' c2'.
  Proof.
    induction c1; intros; simpl; eauto.
  Qed.

  Lemma c_seq_neq_mem_acc:
    forall e c1 c2,
    MemAcc e <> c_seq c1 c2.
  Proof.
    intros.
    intros N.
    destruct (c_seq_eq_seq c1 c2) as (c1', (c2', r1)).
    rewrite r1 in N.
    inversion N.
  Qed.

  Lemma c_seq_neq_if:
    forall b c1 c2 c3 c4,
    If b c1 c2 <> c_seq c3 c4.
  Proof.
    intros.
    intros N.
    destruct (c_seq_eq_seq c3 c4) as (c1', (c2', r1)).
    rewrite r1 in N.
    inversion N.
  Qed.

  Lemma i_in_inv_c_seq_l:
    forall a c1 c2 i j,
    IIn a i ->
    c_seq c1 c2 = Seq i j ->
    IIn a c1.
  Proof.
    induction c1; simpl; intros; try (inversion H0; subst; clear H0; assumption; fail).
    eauto using i_in_seq_l.
  Qed.

  Lemma c_seq_inv_if_2:
    forall c1 c2 c3 c4 b,
    ~ CSeq c1 c2 (If b c3 c4).
  Proof.
    induction c1; intros; intros N; inversion N.
    subst.
    apply IHc1_1 in H4.
    assumption.
  Qed.

  Lemma i_in_inv_c_seq_0:
    forall c1 c2 c3,
    CSeq c1 c2 c3 ->
    forall a,
    IIn a c3 ->
    IIn a c1 \/ IIn a c2.
  Proof.
    intros c1 c2 c3 H.
    induction H; intros.
    - inversion H0; auto.
    - apply IHCSeq2 in H1.
      destruct H1; auto using i_in_seq_l.
      apply IHCSeq1 in H1.
      destruct H1; auto using i_in_seq_r.
  Qed.

  Lemma i_in_inv_c_seq:
    forall c1 c2,
    forall a,
    IIn a (c_seq c1 c2) ->
    IIn a c1 \/ IIn a c2.
  Proof.
    intros.
    remember (c_seq c1 c2) as c3.
    symmetry in Heqc3.
    apply c_seq_to_prop in Heqc3.
    eapply i_in_inv_c_seq_0 in Heqc3; eauto.
  Qed.

  Lemma c_in_inv_c_seq:
    forall a c1 c2,
    CIn a (c_seq c1 c2) ->
    CIn a c1 \/ CIn a c2.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply i_in_inv_c_seq in H1.
    destruct H1 as [Hi|Hi]; eauto using c_in_def.
  Qed.

  Definition OneOf a c1 c2 :=
    CIn a c1 \/ CIn a c2.

  Lemma c_pair_in_inv_c_seq:
    forall p c1 c2,
    CPairIn p (c_seq c1 c2) ->
    let (a1, a2) := p in
    OneOf a1 c1 c2 /\
    OneOf a2 c1 c2.
  Proof.
    intros.
    invc H.
    apply c_in_inv_c_seq in H0.
    apply c_in_inv_c_seq in H1.
    unfold OneOf.
    simpl.
    intuition.
  Qed.

  Lemma c_pair_in_c_seq_l:
    forall a c1 c2,
    CPairIn a c1 ->
    CPairIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_pair_in_seq_l.
    invc H.
    apply c_in_inv_seq in H0.
    apply c_in_inv_seq in H1.
    intuition; auto using c_pair_in_def, c_in_c_seq_l, c_in_c_seq_r.
  Qed.

  Lemma c_pair_in_c_seq_r:
    forall a c1 c2,
    CPairIn a c2 ->
    CPairIn a (c_seq c1 c2).
  Proof.
    induction c1; intros; simpl; auto using c_pair_in_seq_r.
  Qed.

  Lemma c_pair_in_to_pair_in:
    forall c h,
    RunAll TID_COUNT c h ->
    forall p,
    CPairIn p c ->
    PairIn p h.
  Proof.
    intros.
    invc H0.
    apply pair_in_def; auto;
    eapply c_in_2; eauto.
  Qed.

  Lemma c_pair_in_subst:
    forall p x e1 c,
    CPairIn p (i_subst x (N.Exp.from_pure e1) c) ->
    forall n,
    Pure.N.Exp.NStep e1 n ->
    forall e2,
    Pure.N.Exp.NStep e2 n ->
    CPairIn p (i_subst x (N.Exp.from_pure e2) c).
  Proof.
    intros.
    invc H.
    rename_hyp (CIn a1 _) as Hc1.
    rename_hyp (CIn a2 _) as Hc2.
    eapply c_in_subst in Hc1; eauto.
    eapply c_in_subst in Hc2; eauto.
    eauto using c_pair_in_def.
  Qed.

  Lemma c_seq_subst:
    forall x v c1 c2,
    i_subst x v (c_seq c1 c2) = c_seq (i_subst x v c1) (i_subst x v c2).
  Proof.
    induction c1; intros; simpl; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    reflexivity.
  Qed.

  Lemma eq_c_seq_def:
    forall c1 c2 c1' c2',
    c1 = c1' ->
    c2 = c2' ->
    c_seq c1 c2 = c_seq c1' c2'.
  Proof.
    intros; subst.
    reflexivity.
  Qed.

  Lemma i_subst_c_seq:
    forall x v c1 c2,
    i_subst x v (c_seq c1 c2)
    = c_seq (i_subst x v c1) (i_subst x v c2).
  Proof.
    induction c1; simpl; intros; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    auto.
  Qed.

  Lemma var_inv_c_seq:
    forall x c1 c2,
    Var x (c_seq c1 c2) ->
    Var x c1 \/ Var x c2.
  Proof.
    induction c1; simpl; intros; try (intuition; fail).
    apply IHc1_1 in H.
    intuition.
    apply IHc1_2 in H0.
    intuition.
  Qed.

  Lemma occurs_inv_c_seq:
    forall x c1 c2,
    Occurs x (c_seq c1 c2) ->
    Occurs x c1 \/ Occurs x c2.
  Proof.
    induction c1; simpl; intros; try (intuition; fail).
    apply IHc1_1 in H.
    intuition.
    apply IHc1_2 in H0.
    intuition.
  Qed.
End Defs.
