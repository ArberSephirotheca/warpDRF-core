From Stdlib Require Import Lists.List.
From Faial.Core Require Import Var.
From Faial.Core Require Import AVal.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Hist.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Expr Require Pure.N.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.
From Faial.Drf.U Require Import Run.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.

  Inductive IIn (a:access_val) : t -> Prop :=
  | i_in_access:
    forall e,
    AStep (av_owner a) e a ->
    IIn a (MemAcc e)
  | i_in_if_true:
    forall b i j,
    BStep (av_owner a) b true ->
    IIn a i ->
    IIn a (If b i j)
  | i_in_if_false:
    forall b i j,
    BStep (av_owner a) b false ->
    IIn a j ->
    IIn a (If b i j)
  | i_in_seq_l:
    forall i j,
    IIn a i ->
    IIn a (Seq i j)
  | i_in_seq_r:
    forall i j,
    IIn a j ->
    IIn a (Seq i j)
  | i_in_for:
    forall i r x n,
    RPick (av_owner a) r n ->
    IIn a (f x (NNum n) i) ->
    IIn a (For x r i)
  | i_in_decl:
    forall i x,
    IIn a i ->
    IIn a (Decl x i)
  .

  Section S_IIn.
  Variable x:var.
  Variable v:nexp.

  Inductive S_IIn (a:access_val) : t -> Prop :=
  | s_i_in_access:
    forall e,
    AStep (av_owner a) (a_subst x v e) a ->
    S_IIn a (MemAcc e)
  | s_i_in_if_true:
    forall b i j,
    BStep (av_owner a) (b_subst x v b) true ->
    S_IIn a i ->
    S_IIn a (If b i j)
  | s_i_in_if_false:
    forall b i j,
    BStep (av_owner a) (b_subst x v b) false ->
    S_IIn a j ->
    S_IIn a (If b i j)
  | s_i_in_seq_l:
    forall i j,
    S_IIn a i ->
    S_IIn a (Seq i j)
  | s_i_in_seq_r:
    forall i j,
    S_IIn a j ->
    S_IIn a (Seq i j)
  | s_i_in_for_eq:
    forall i r n,
    RPick (av_owner a) (r_subst x v r) n ->
    IIn a (f x (NNum n) i) ->
    S_IIn a (For x r i)
  | s_i_in_for_neq:
    forall i r y n,
    x <> y ->
    RPick (av_owner a) (r_subst x v r) n ->
    S_IIn a (f y (NNum n) i) ->
    S_IIn a (For y r i)
  | s_i_in_decl_eq:
    forall i,
    IIn a i ->
    S_IIn a (Decl x i)
  | s_i_in_decl_neq:
    forall i y,
    x <> y ->
    S_IIn a i ->
    S_IIn a (Decl y i)
  .
  End S_IIn.

  Lemma s_i_in_to_i_in:
    forall x v a i,
    S_IIn x v a i ->
    forall n, NStep (av_owner a) v n ->
    IIn a (f x v i).
  Proof.
    intros x v a i H.
    induction H; simpl; intros.
    - constructor; auto.
    - constructor; eauto.
    - apply i_in_if_false; eauto.
    - constructor; eauto.
    - apply i_in_seq_r; eauto.
    - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      econstructor; eauto.
   - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
     econstructor; eauto.
     assert (~ NFree x (NNum n)) by auto using n_free_num.
     assert (~ NFree y v) by eauto using n_step_to_not_free.
     rewrite subst_subst_neq_3; eauto.
   - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
     econstructor; eauto.
   - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
     econstructor; eauto.
  Qed.

  Lemma i_in_to_s_i_in:
    forall x v a i,
    IIn a (f x v i) ->
    forall n, NStep (av_owner a) v n ->
    S_IIn x v a i.
  Proof.
    intros x v a i Hi.
    remember (f _ _ _) as j.
    generalize dependent x.
    generalize dependent v.
    generalize dependent i.
    induction Hi;
      intros i_src v y Heq m Hn;
      destruct i_src;
      inversion Heq; subst; clear Heq.
    - constructor.
      auto.
    - assert (IHHi := IHHi _ _ _ eq_refl _ Hn).
      apply s_i_in_if_true; auto.
    - assert (IHHi := IHHi _ _ _ eq_refl _ Hn).
      apply s_i_in_if_false; auto.
    - constructor; eauto.
    - apply s_i_in_seq_r; eauto.
    - rename v0 into x.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        eapply s_i_in_for_eq; eauto.
      }
      assert (r1: f x (NNum n) (f y v i_src) = f y v (f x (NNum n) i_src)). {
        rewrite subst_subst_neq_3; eauto using n_step_to_not_free.
      }
      eapply IHHi in r1; eauto.
      eapply s_i_in_for_neq; eauto.
    - rename v0 into x.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        eapply s_i_in_decl_eq; eauto.
      }
      eapply s_i_in_decl_neq; eauto.
  Qed.

  Lemma i_in_subst:
    forall x a i v v' n,
    Pure.N.Exp.NStep v n ->
    Pure.N.Exp.NStep v' n ->
    IIn a (f x (from_pure v) i) ->
    IIn a (f x (from_pure v') i).
  Proof.
    intros.
    apply n_step_pure with (tid:=av_owner a) in H.
    apply n_step_pure with (tid:=av_owner a) in H0.
    eapply i_in_to_s_i_in in H1; eauto.
    eapply s_i_in_to_i_in; eauto.
    generalize dependent v'.
    generalize dependent n.
    induction H1; intros; assert (r1: NEq (av_owner a) (from_pure v) (from_pure v')) by eauto using n_eq_def.
    - constructor.
      eapply a_step_proper; eauto.
      apply eq_subst_proper.
      assumption.
    - apply s_i_in_if_true; eauto using b_eq_proper_6.
    - apply s_i_in_if_false; eauto using b_eq_proper_6.
    - constructor; eauto.
    - eapply s_i_in_seq_r; eauto.
    - eapply s_i_in_for_eq; eauto.
      rewrite <- r1.
      assumption.
    - eapply s_i_in_for_neq; eauto.
      rewrite <- r1.
      assumption.
    - eapply s_i_in_decl_eq; eauto.
    - eapply s_i_in_decl_neq; eauto.
  Qed.

  Lemma run_in_to_i_in:
    forall m i h,
    Run m i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros m i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - apply i_in_access.
      simpl in *.
      intuition.
      subst.
      erewrite a_step_inv_tid; eauto using n_step_num.
    - apply in_app_iff in Hi.
      destruct Hi; eauto using i_in_seq_l, i_in_seq_r.
    - destruct b.
      + apply i_in_if_true; auto.
        erewrite run_inv_in_eq with (i:=i); eauto.
      + apply i_in_if_false; auto.
        erewrite run_inv_in_eq with (i:=j); eauto.
    - apply in_app_iff in Hi.
      destruct Hi.
      + apply i_in_for with (n:=n); auto.
        assert (R: av_owner a = m). { eauto using run_inv_in_eq. }
        rewrite R.
        eauto using r_step_to_pick.
      + rename_hyp (In a _) as ha.
        assert (Hi := ha).
        apply IHHr2 in ha.
        invc ha.
        apply i_in_for with (n:=n0); eauto with *.
        apply r_step_pick_rev with (n':=n) (r':=r'); auto.
        assert (R: av_owner a = m). { eauto using run_inv_in_eq. }
        rewrite R.
        assumption.
    - contradiction.
    - apply i_in_decl. auto.
  Qed.

  Lemma run_all_in_to_i_in:
    forall n i h,
    RunAll n i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros.
    eapply run_all_inv_in in H0; eauto.
    destruct H0 as (m, (h', (Hi, (Hm, (Hinc,Hj))))).
    eauto using run_in_to_i_in.
  Qed.

  Lemma run_i_in_to_in:
    forall m i h,
    Run m i h ->
    forall a,
    av_owner a = m ->
    IIn a i ->
    List.In a h.
  Proof.
    intros m i h Hr.
    induction Hr; intros a He Hi; inversion Hi; subst; clear Hi.
    - assert (a = v) by eauto using a_step_fun.
      subst.
      auto using in_eq.
    - apply in_app_iff.
      auto.
    - apply in_app_iff.
      auto.
    - assert (b = true) by eauto using b_step_fun.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun.
      subst.
      eauto.
    - apply in_app_iff.
      rename_hyp (RPick _ _ _) as hr.
      apply r_step_pick_advance with (n:=n) (r':=r') in hr; auto.
      destruct hr. { subst. eauto. }
      eauto using i_in_for.
    - rename_hyp (REmpty _ _) as he.
      contradict he.
      eauto using r_pick_to_empty.
    - eauto.
  Qed.

  Lemma run_i_in_iff:
    forall m i h,
    Run m i h ->
    forall a,
    av_owner a = m ->
    IIn a i <-> List.In a h.
  Proof.
    intros.
    split; eauto using run_i_in_to_in, run_in_to_i_in.
  Qed.

  Lemma run_all_i_in_to_in:
    forall n i h,
    RunAll n i h ->
    forall a,
    av_owner a < n ->
    IIn a i ->
    List.In a h.
  Proof.
    intros.
    eapply run_all_inv_run in H; eauto.
    destruct H as (h', (Hr, Hinc)).
    apply Hinc; clear Hinc.
    eapply run_i_in_to_in; eauto.
  Qed.
End Defs.
