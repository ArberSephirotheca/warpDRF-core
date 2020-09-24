Require Import Coq.Lists.List.
Require Import VHist.
Require Import Tasks.
Require Import ALang.
Require Import NExp.
Require Import RExp.
Require Import Var.
Require Import AccExp.
Require Import Lia.
Require Import PairInUtil.

Require Conc.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.

  Notation history := (list access_val).
  Notation mhistory := (list history).


  Inductive access_sym :=
  | Block: Conc.inst -> access_sym
  | Decl: var -> range -> access_sym -> access_sym
  .

  Fixpoint d_subst x v d :=
    match d with
    | Block c => Block (Conc.i_subst x v c)
    | Decl y r d1 =>
      let d1' := if VAR.eq_dec x y then d1 else d_subst x v d1 in
      Decl y (r_subst x v r) d1'
    end.

  Inductive Run : access_sym -> mhistory -> Prop :=
  | run_base:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) [h]
  | run_decl_cons:
    forall e1 e2 n1 n2 d x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (d_subst x (NNum n1) d) m1 ->
    Run (Decl x (NNum (S n1), NNum n2) d) m2 ->
    m1 ++ m2 = m3 ->
    Run (Decl x (e1, e2) d) m3
  | run_decl_nil:
    forall x i e1 e2 n1 n2 m,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    m = [] ->
    Run (Decl x (e1, e2) i) m.

  Inductive IPairIn: access_val * access_val -> access_sym -> Prop :=
  | i_pair_in_block:
    forall a1 a2 c,
    access_tid a1 < TID_COUNT ->
    access_tid a2 < TID_COUNT ->
    Conc.IIn a1 c ->
    Conc.IIn a2 c ->
    IPairIn (a1, a2) (Block c)
  | i_pair_in_decl:
    forall e1 e2 n1 n2 n d x p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    IPairIn p (d_subst x (NNum n) d) ->
    IPairIn p (Decl x (e1, e2) d)
    .

  Fixpoint Var x i :=
    match i with
    | Block c => Conc.Var x c
    | Decl y _ i => x = y \/ Var x i
    end.

  Lemma var_subst_inv_1:
    forall y x n d,
    Var y (d_subst x (NNum n) d) ->
    Var y d.
  Proof.
    induction d; intros. {
      simpl in *.
      eauto using Conc.var_subst_inv_1.
    }
    simpl in *.
    destruct (Set_VAR.MF.eq_dec x v). {
      auto.
    }
    destruct H; auto.
  Qed.

  Lemma i_pair_in_1:
    forall s m,
    Run s m ->
    ~ Var TID s ->
    forall a1 a2,
    IPairIn (a1, a2) s ->
    MPairIn (a1, a2) m.
  Proof.
    intros s m H.
    induction H; intros.
    - simpl in *.
      match goal with
        H: IPairIn _ _ |- _ => inversion H; subst; clear H
      end.
      eauto using m_pair_in_eq, pair_in_def, Conc.run_all_i_in_to_in.
    - match goal with
        H: IPairIn _ _ |- _ => inversion H; subst; clear H
      end.
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hx: n1 = n \/ n1 < n) by lia.
      destruct Hx as [?|Hx]. {
        subst.
        apply m_pair_in_app_l.
        apply IHRun1; auto.
        intros N.
        apply var_subst_inv_1 in N.
        simpl in *.
        contradict H5.
        auto.
      }
      apply m_pair_in_app_r.
      apply IHRun2; auto.
      apply i_pair_in_decl with (n1:=S n1) (n:=n) (n2:=n2); auto using n_step_num.
      lia.
    - subst.
      simpl in *.
      match goal with
        H: IPairIn _ _ |- _ => inversion H; subst; clear H
      end.
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      lia.
  Qed.

  Lemma i_pair_in_2:
    forall s m,
    Run s m ->
    ~ Var TID s ->
    forall a1 a2,
    MPairIn (a1, a2) m ->
    IPairIn (a1, a2) s.
  Proof.
    intros s m H.
    induction H; intros.
    - apply m_pair_in_inv in H1.
      destruct H1 as [Hp|N]. {
        inversion Hp; subst; clear Hp.
        apply i_pair_in_block.
        + eauto using Conc.run_all_inv_in_eq.
        + eauto using Conc.run_all_inv_in_eq.
        + eapply Conc.run_all_to_i_in; eauto.
        + eapply Conc.run_all_to_i_in; eauto.
      }
      apply m_pair_in_nil in N.
      contradiction.
    - subst.
      apply m_pair_in_app_or in H6.
      destruct H6 as [Hi|Hi]. {
        apply IHRun1 in Hi. {
          eapply i_pair_in_decl; eauto.
        }
        intros N.
        simpl in *.
        apply var_subst_inv_1 in N.
        intuition.
      }
      apply IHRun2 in Hi. {
        inversion Hi; subst; clear Hi.
        assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
        assert (n3 = n2) by eauto using n_step_num, n_step_fun.
        subst.
        apply i_pair_in_decl with (n1:=n1) (n:=n) (n2:=n2); auto.
        lia.
      }
      intros N.
      simpl in *.
      intuition.
    - subst.
      apply m_pair_in_nil in H4.
      contradiction.
  Qed.

End Defs.