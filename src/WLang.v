Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationPairs.


Require Import Var.
Require Import Tid.
Require Import Pure.NExp.
Require SIMT.NExp.
Require Import Pure.RExp.
Require Import Pure.BExp.
Require Import SIMT.AExp.
Require Import AVal.
Require Import Tasks.
Require Import InUtil.
Require Import PairInUtil.
Require Import VHist.
Require Import ULang.
Require Import Tictac.

Require Import Lia.

Import ListNotations.
Require ULang.

Section Defs.

  Notation history := (list access_val).

  Notation mhistory := (list history).

  Notation histpair := (mhistory * history) % type.

  Context `{T:Tasks}.

  Open Scope vhist_scope.

(* -------------------- RUN --------------------------- *)


  Inductive w_inst :=
    (* code ; sync *)
  | WSync: ULang.inst -> w_inst 
    (* P ;  Q *)
  | WSeq: w_inst -> w_inst -> w_inst
    (* c; for { P; c } *)
  | WFor : ULang.inst -> var -> range -> w_inst -> ULang.inst -> w_inst.

  Fixpoint w_subst (x:var) (v:nexp) P :=
    match P with
    | WSync c => WSync (ULang.i_subst x (SIMT.NExp.from_pure v) c)
    | WSeq P Q => WSeq (w_subst x v P) (w_subst x v Q)
    | WFor c1 y r P c2 =>
      let (P', c2') := if VAR.eq_dec x y
        then (P, c2)
        else (w_subst x v P, ULang.i_subst x (SIMT.NExp.from_pure v) c2)
      in
      WFor (ULang.i_subst x (SIMT.NExp.from_pure v) c1) y (r_subst x v r) P' c2'
    end.


  Lemma w_subst_subst_neq:
    forall P x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    w_subst x v1 (w_subst y v2 P)
    =
    w_subst y v2 (w_subst x v1 P).
  Proof.
    induction P; intros; simpl.
    - rewrite SIMT.NExp.n_free_from_pure in *.
      rewrite i_subst_subst_neq_3; auto.
    - rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        destruct (Set_VAR.MF.eq_dec x v). {
          simpl.
          destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        rewrite SIMT.NExp.n_free_from_pure in *.
        rewrite i_subst_subst_neq_3; auto.
        rewrite <- SIMT.NExp.n_free_from_pure in *.
        rewrite r_subst_subst_neq_3; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        simpl.
        subst.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
        rewrite SIMT.NExp.n_free_from_pure in *.
        rewrite i_subst_subst_neq_3; auto.
        rewrite <- SIMT.NExp.n_free_from_pure in *.
        rewrite r_subst_subst_neq_3; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
      destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
      rewrite SIMT.NExp.n_free_from_pure in *.
      rewrite i_subst_subst_neq_3; auto.
      rewrite i_subst_subst_neq_3 with (c:=i0); auto.
      rewrite <- SIMT.NExp.n_free_from_pure in *.
      rewrite r_subst_subst_neq_3; auto.
      rewrite IHP; auto.
  Qed.

  Inductive WRun: w_inst -> vhist -> Prop :=
  | wrun_sync:
    forall c h,
    ULang.RunAll TID_COUNT c h ->
    WRun (WSync c) {{ h | [] }}

  | wrun_seq: forall i j mh_i mh_j mh,
    WRun i mh_i ->
    WRun j mh_j ->
    mh_i @ mh_j = mh ->
    WRun (WSeq i j) mh

  | wrun_for_cons:
    forall r r' n h1 h2 m1 m2 m3 c1 x c2 P,
    RStep r n r' ->
    ULang.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    ULang.RunAll TID_COUNT (ULang.i_subst x (SIMT.NExp.NNum n) c2) h2 ->
    WRun (WFor ULang.Skip x r' P c2) m2 ->
    {{ h1 }} @ m1 @ {{ h2 }} @ m2 = m3 ->
    WRun (WFor c1 x r P c2) m3

  | wrun_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall c1 h1 h2 r m m1 n x P c2,
    ROne r n ->
    ULang.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    ULang.RunAll TID_COUNT (ULang.i_subst x (SIMT.NExp.NNum n) c2) h2 ->
    {{ h1 }} @ m1 @ {{ h2 }} = m ->
    WRun (WFor c1 x r P c2) m.


  Inductive CanRun: w_inst -> Prop :=
  | can_run_sync:
    forall c,
    CanRun (WSync c)
  | can_run_seq:
    forall i j,
    CanRun i -> 
    CanRun j ->
    CanRun (WSeq i j)
  | can_run_for:
    forall x r P c1 c2,
    RHasNext r ->
    (forall n, RPick r n -> CanRun (w_subst x (NNum n) P)) -> 
    CanRun (WFor c1 x r P c2).

  Section X_CanRun.
    Variable x:var.
    Variable v:nexp.

  Inductive X_CanRun: w_inst -> Prop :=
  | x_can_run_sync:
    forall c,
    X_CanRun (WSync c)
  | x_can_run_seq:
    forall i j,
    X_CanRun i -> 
    X_CanRun j ->
    X_CanRun (WSeq i j)
  | x_can_run_for:
    forall y r P c1 c2,
    RHasNext (r_subst x v r) ->
    (forall n, RPick (r_subst x v r) n -> X_CanRun (w_subst y (NNum n) P)) -> 
    X_CanRun (WFor c1 y r P c2).
  End X_CanRun.

  Lemma x_can_run_subst:
    forall x v1 P,
    X_CanRun x v1 P ->
    forall v2 n,
    NStep v1 n ->
    NStep v2 n ->
    X_CanRun x v2 P.
  Proof.
    intros x v1 p H.
    induction H; intros v2 n Hn1 Hn2.
    - apply x_can_run_sync.
    - apply x_can_run_seq; eauto.
    - constructor.
      + eauto using r_has_next_subst.
      + eauto using r_pick_subst.
  Qed.

  Lemma w_subst_subst_eq_1:
    forall e1 e2 x P,
    w_subst x e1 (w_subst x e2 P) = w_subst x (n_subst x e1 e2) P.
  Proof.
    induction P; intros; simpl.
    - rewrite i_subst_subst_eq_1.
      rewrite NExp.n_subst_from_pure.
      reflexivity.
    - rewrite IHP1.
      rewrite IHP2.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        simpl.
        remove_eq v v.
        rewrite i_subst_subst_eq_1.
        rewrite r_subst_subst_eq_1.
        rewrite NExp.n_subst_from_pure.
        reflexivity.
      }
      simpl.
      remove_eq x v.
      repeat rewrite i_subst_subst_eq_1.
      rewrite r_subst_subst_eq_1.
      rewrite NExp.n_subst_from_pure.
      rewrite IHP.
      reflexivity.
  Qed.

  Lemma x_can_run_spec:
    forall x v P,
    NClosed v ->
    X_CanRun x v P <-> CanRun (w_subst x v P).
  Proof.
    split; intros. {
      generalize dependent H.
      induction H0; intros; simpl.
      - constructor.
      - constructor; auto.
      - destruct (Set_VAR.MF.eq_dec x y). {
          subst.
          constructor; auto.
          intros.
          rename_hyp (forall n, _ -> _ -> CanRun _) as Hx.
          rename_hyp (RPick _ _) as Hp.
          apply Hx in Hp; auto.
          rewrite w_subst_subst_eq_1 in Hp.
          simpl in *.
          assumption.
        }
        constructor; auto.
        intros.
        rename_hyp (forall n, _ -> _ -> CanRun _) as Hx.
        rename_hyp (RPick _ _) as Hp.
        apply Hx in Hp; auto.
        rewrite w_subst_subst_neq; auto.
    }
    remember (w_subst _ _ _) as Q.
    generalize dependent x.
    generalize dependent v.
    generalize dependent P.
    induction H0;
      intros P_in v Hv y Heq;
      destruct P_in;
      simpl in Heq;
      try (invc Heq; fail);
      try (rename v0 into x).
    - invc Heq.
      constructor.
    - destruct (Set_VAR.MF.eq_dec y x); invc Heq.
    - invc Heq.
      constructor; eauto.
    - destruct (Set_VAR.MF.eq_dec y x); invc Heq.
    - rename v0 into x'.
      destruct (Set_VAR.MF.eq_dec y x'); invc Heq. {
        constructor; auto.
        intros.
        rename_hyp (forall n, RPick _ _ -> forall P v, _ -> _) as Hx.
        rename_hyp (RPick _ _) as Hp.
        eapply Hx in Hp; eauto.
        rewrite w_subst_subst_eq_1.
        simpl.
        auto.
      }
      constructor; auto.
      intros.
      rename_hyp (forall n, RPick _ _ -> forall P v, _ -> _) as Hx.
      rename_hyp (RPick _ _) as Hp.
      eapply Hx in Hp; eauto.
      rewrite w_subst_subst_neq; eauto.
  Qed.

  Lemma can_run_subst:
    forall x v1 P,
    CanRun (w_subst x v1 P) ->
    forall v2 n,
    NStep v1 n ->
    NStep v2 n ->
    CanRun (w_subst x v2 P).
  Proof.
    intros.
    apply x_can_run_spec; eauto using n_step_to_closed.
    apply x_can_run_spec in H; eauto using n_step_to_closed.
    eauto using x_can_run_subst.
  Qed.

  Lemma run_to_can_run:
    forall w h,
    WRun w h ->
    CanRun w.
  Proof.
    intros.
    intros.
    induction H; constructor; auto; subst.
    - apply r_step_to_has_next in H.
      assumption.
    - intros n' H'.
      destruct r as (e1, e2).
      apply r_pick_inv_first in H'.
      destruct H' as [H'|H'].
      + assert (n' = n).
        * apply r_step_to_first in H.
          eauto using r_first_fun.
        * subst.
          assumption.
      + assert (RPick r' n').
        eauto using r_step_inv_r.
        invc IHWRun2.
        auto.
    - apply r_one_to_has_next in H.
      assumption.
    - intros n' H'.
      destruct r as (e1, e2).
      assert (n' = n).
      + invc H.
        invc H'.
        assert (n1 = n) by eauto using n_step_fun; subst.
        assert (n2 = S n) by eauto using n_step_fun; subst.
        lia.
      + subst.
        assumption.
  Qed.

  Definition WEq P Q :=
    forall h,
    WRun P h <-> WRun Q h.

  Fixpoint WVar x i :=
    match i with
    | WSync c => ULang.Var x c
    | WSeq i j => WVar x i \/ WVar x j
    | WFor c1 y _ P c2 =>
      x = y \/
      ULang.Var x c1 \/
      WVar x P \/ ULang.Var x c2
    end.

  Lemma w_subst_subst_neq_5:
    forall P x v y e,
    x <> y ->
    NClosed v ->
    ~ WVar x P ->
    w_subst x v (w_subst y e P) =
    w_subst y (n_subst x v e) (w_subst x v P).
  Proof.
    induction P; intros x v' y e Hn Hc Hv; simpl; simpl in Hv.
    - rewrite i_subst_subst_neq_5; auto.
      + rewrite NExp.n_subst_from_pure.
        reflexivity.
      + apply NExp.n_closed_from_pure.
        assumption.
    - rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        destruct (Set_VAR.MF.eq_dec x v). {
          intuition.
        }
        simpl.
        destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        rewrite i_subst_subst_neq_5; auto.
        2: { apply NExp.n_closed_from_pure. assumption. }
        rewrite NExp.n_subst_from_pure.
        rewrite r_subst_subst_neq_5; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v) as [?|_]. { intuition. }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v) as [?|_]. { intuition. }
      destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
      rewrite i_subst_subst_neq_5; auto.
      2: { apply NExp.n_closed_from_pure. assumption. }
      rewrite NExp.n_subst_from_pure.
      rewrite r_subst_subst_neq_5; auto.
      rewrite IHP; auto. {
        assert (rx: i_subst x (NExp.from_pure v') (i_subst y (NExp.from_pure e) i0) = 
                    i_subst y (NExp.n_subst x (NExp.from_pure v') (NExp.from_pure e)) (i_subst x (NExp.from_pure v') i0)). {
          rewrite i_subst_subst_neq_5; auto.
          - apply NExp.n_closed_from_pure. assumption.
          - intuition.
        }
        rewrite rx.
        rewrite NExp.n_subst_from_pure.
        auto.
      }
      intuition.
  Qed.


  Fixpoint Distinct P :=
    match P with
    | WSync _ => True
    | WSeq P Q => Distinct P /\ Distinct Q
    | WFor c1 x _ P c2 =>
      ULang.Distinct c1
      /\ ~ WVar x P
      /\ ~ Var x c2
      /\ Distinct P
      /\ ULang.Distinct c2
    end.

  Lemma wvar_inv_subst:
    forall y x v i,
    WVar y (w_subst x v i) ->
    WVar y i.
  Proof.
    induction i; simpl; intros; auto.
    - eauto using ULang.var_inv_subst.
    - intuition.
    - destruct (Set_VAR.MF.eq_dec x v0); simpl in *. {
        intuition.
        eauto using ULang.var_inv_subst.
      }
      intuition.
      + eauto using ULang.var_inv_subst.
      + eauto using ULang.var_inv_subst.
  Qed.

  Lemma wrun_one:
    forall i h,
    ~ WRun i {{h}}.
  Proof.
    intros i h.
    intros N.
    remember (v_one _) as v.
    generalize dependent h.
    induction N; intros.
    - inversion Heqv.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h1, (h2, (?, ?))).
      subst.
      eauto using IHN1.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h3, (h4, (Heq1, Heq2))).
      inversion Heq1; subst; clear Heq1.
      apply v_seq_inv_one in Heq2.
      destruct Heq2 as (h1, (h5, (?, Heqv))).
      subst.
      eauto.
    - subst.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h3, (h4, (Heq1, Heqv))).
      inversion Heq1; subst; clear Heq1.
      apply v_seq_inv_one in Heqv.
      destruct Heqv as (h5, (h6, (?, Heqv))).
      subst.
      eauto.
  Qed.

  Lemma wrun_has_many:
    forall i v,
    WRun i v ->
    HasMany v.
  Proof.
    intros.
    destruct v; simpl; auto.
    apply wrun_one in H.
    assumption.
  Qed.

  Lemma w_run_inv_for_skip:
    forall r P c m x,
    WRun (WFor ULang.Skip x r P c) m ->
    exists m1 h2 n,
    WRun (w_subst x (NNum n) P) m1 /\
    ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.NNum n) c) h2 /\
    (
    (
      exists m2 r',
      RStep r n r' /\
      WRun (WFor ULang.Skip x r' P c) m2 /\
      m = m1 @ {{ h2 }} @ m2
    )
    \/
    (ROne r n /\ m = m1 @ {{ h2 }})).
  Proof.
    intros.
    inversion H; subst; clear H;
      exists m1;
      exists h2;
      exists n;
      match goal with
        H: ULang.RunAll _ ULang.Skip _ |- _ =>
        apply ULang.run_all_inv_skip in H; subst; simpl; rewrite v_prefix_nil
      end;
      split; auto;
      split; auto
      .
    left.
    eauto.
  Qed.

  Lemma w_run_inv_for_skip_1:
    forall r P c m x,
    WRun (WFor ULang.Skip x r P c) m ->
    exists n,
    RFirst r n /\
    exists m1,
    WRun (w_subst x (NNum n) P) m1 /\
    exists h2,
    ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.NNum n) c) h2 /\
    exists m2,
    m = m1 @ {{ h2 }} @ m2.
  Proof.
    intros.
    apply w_run_inv_for_skip in H.
    destruct H as (m1, (h2, (n, (Hr, (Hr2, Hx))))).
    exists n.
    destruct Hx as [(m2, (r', (Hrs, (?, Hx))))|(Hx,?)]. {
      subst.
      apply r_step_to_first in Hrs.
      split; auto.
      exists m1.
      split; auto.
      exists h2.
      split; auto.
      exists m2.
      auto.
    }
    subst.
    split; auto using r_one_to_first.
    exists m1.
    split; auto.
    exists h2.
    split; auto.
    exists {{ [] }}.
    rewrite v_seq_one_nil_r.
    auto.
  Qed.

  Lemma wrun_for_inv_has_next:
    forall r P c v x,
    WRun (WFor ULang.Skip x r P c) v ->
    RHasNext r.
  Proof.
    intros.
    inversion H; subst; clear H. {
      eauto using r_step_to_has_next.
    }
    eauto using r_one_to_has_next.
  Qed.

  Section X_WRun.
    Variable x:var.
    Variable v:nexp.
    Inductive X_WRun: w_inst -> vhist -> Prop :=
    | x_wrun_sync:
      forall c h,
      ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.from_pure v) c) h ->
      X_WRun (WSync c) {{ h | [] }}

    | x_wrun_seq: forall i j mh_i mh_j mh,
      X_WRun i mh_i ->
      X_WRun j mh_j ->
      mh_i @ mh_j = mh ->
      X_WRun (WSeq i j) mh

    | x_wrun_for_cons:
      forall r r' n h1 h2 m1 m2 m3 c1 y c2 P,
      RStep (r_subst x v r) n (r_subst x v r') ->
      ULang.RunAll TID_COUNT (i_subst x (NExp.from_pure v) c1) h1 ->
      X_WRun (w_subst y (NNum n) P) m1 ->
      ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.from_pure v) (ULang.i_subst y (NExp.NNum n) c2)) h2 ->
      X_WRun (WFor ULang.Skip y r' P c2) m2 ->
      {{ h1 }} @ m1 @ {{ h2 }} @ m2 = m3 ->
      X_WRun (WFor c1 y r P c2) m3

    | x_wrun_for_eq:
      (* We note that the loops must run at least once. This is
         a constraint of our programming model. *)
      forall c1 h1 h2 r m m1 n y P c2,
      ROne (r_subst x v r) n ->
      ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.from_pure v) c1) h1 ->
      X_WRun (w_subst y (NNum n) P) m1 ->
      ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.from_pure v) (ULang.i_subst y (NExp.NNum n) c2)) h2 ->
      {{ h1 }} @ m1 @ {{ h2 }} = m ->
      X_WRun (WFor c1 y r P c2) m.

  Lemma wrun_to_x_wrun:
    forall P h,
    ~ WVar x P ->
    WRun (w_subst x v P) h ->
    NClosed v ->
    X_WRun P h.
  Proof.
    intros.
    remember (w_subst _ _ _) as Q.
    generalize dependent P.
    induction H0; intros.
    - destruct P; simpl in HeqQ; simpl in HeqQ; invc HeqQ. 2: {
        destruct (Set_VAR.MF.eq_dec x v0);
          rename_hyp (_ = _) as heq; invc heq.
      }
      constructor; auto.
    - destruct P; simpl in HeqQ; simpl in HeqQ; invc HeqQ. 2: {
        destruct (Set_VAR.MF.eq_dec x v0);
          rename_hyp (_ = _) as heq; invc heq.
      }
      rename_hyp (~ WVar _ _) as hv.
      simpl in hv.
      eapply x_wrun_seq; eauto.
    - destruct P0; simpl in HeqQ; simpl in HeqQ; invc HeqQ.
      rename_hyp (~ WVar _ _) as hv.
      simpl in hv.
      destruct (Set_VAR.MF.eq_dec x v0);
        rename_hyp (_ = _) as heq; invc heq. {
        intuition.
      }
      eapply x_wrun_for_cons with (n:=n) (r':=r'); eauto.
      + assert (rx: r_subst x v r' = r'). {
          eauto using r_defined_subst, r_step_to_defined_r.
        }
        rewrite rx.
        assumption.
      + apply IHWRun1; auto.
        * intros N.
          apply wvar_inv_subst in N.
          intuition.
        * rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
      + rewrite i_subst_subst_neq_3; auto.
        rewrite <- NExp.n_free_from_pure.
        auto.
      + apply IHWRun2.
        * intros N.
          simpl in N.
          intuition.
        * simpl.
          destruct (Set_VAR.MF.eq_dec x v0) as [?|_]; try contradiction.
          assert (rv: r' = r_subst x v r'). {
            symmetry.
            eauto using r_defined_subst, r_step_to_defined_r.
          }
          rewrite <- rv.
          reflexivity.
    - subst.
      destruct P0; simpl in HeqQ; simpl in HeqQ; invc HeqQ.
      rename_hyp (~ WVar _ _) as hv.
      simpl in hv.
      destruct (Set_VAR.MF.eq_dec x v0);
        rename_hyp (_ = _) as heq; invc heq. {
        subst.
        intuition.
      }
      eapply x_wrun_for_eq; eauto.
      + apply IHWRun.
        * intros N.
          apply wvar_inv_subst in N.
          auto.
        * rewrite w_subst_subst_neq; auto.
      + rewrite ULang.i_subst_subst_neq_3; auto.
        rewrite <- NExp.n_free_from_pure.
        auto.
  Qed.

  Lemma x_wrun_to_wrun:
    forall P h,
    X_WRun P h ->
    ~ WVar x P ->
    NClosed v ->
    WRun (w_subst x v P) h.
  Proof.
    intros P h H.
    induction H; intros; simpl; rename_hyp (~WVar _ _) as hv.
    - constructor; auto.
    - simpl in hv.
      econstructor; eauto.
    - destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        simpl in hv.
        intuition.
      }
      simpl in hv.
      eapply wrun_for_cons; eauto.
      + assert (hw: WRun (w_subst x v (w_subst y (NNum n) P)) m1). {
          apply IHX_WRun1; auto.
          intros N.
          apply wvar_inv_subst in N.
          auto.
        }
        rewrite w_subst_subst_neq; auto.
      + rewrite ULang.i_subst_subst_neq_3; auto.
        rewrite <- NExp.n_free_from_pure.
        auto.
      + assert (hw: WRun (w_subst x v (WFor Skip y r' P c2)) m2). {
          apply IHX_WRun2; auto.
          simpl in *.
          intuition.
        }
        simpl in hw.
        destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
        assumption.
    - simpl in hv.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]. {
        intuition.
      }
      subst.
      eapply wrun_for_eq; eauto.
      + assert (WRun (w_subst x v (w_subst y (NNum n) P)) m1). {
          apply IHX_WRun; auto.
          intros N.
          apply wvar_inv_subst in N.
          intuition.
        }
        rewrite w_subst_subst_neq; auto.
      + rewrite ULang.i_subst_subst_neq_3; auto.
        rewrite <- NExp.n_free_from_pure.
        auto.
  Qed.

  End X_WRun.

  Lemma x_wrun_subst:
    forall x e1 P v,
    X_WRun x e1 P v ->
    forall n,
    NStep e1 n ->
    forall e2,
    NStep e2 n ->
    X_WRun x e2 P v.
  Proof.
    intros x e1 P v H.
    induction H; intros.
    - constructor.
      eapply c_run_subst with (e:=e1); eauto using n_step_to_not_free, n_eq_def.
    - subst.
      econstructor; eauto.
    - subst.
      simpl in *.
      eapply x_wrun_for_cons with
        (m1:=m1) (r':=r') (n:=n) (m2:=m2) (h2:=h2);
        eauto.
      + eapply r_step_subst with (e1:=e1); eauto.
      + eapply c_run_subst with (e:=e1); eauto using n_step_to_not_free, n_eq_def.
      + eapply c_run_subst with (e:=e1); eauto using n_step_to_not_free, n_eq_def.
      + simpl.
        auto.
    - subst.
      simpl in *.
      eapply x_wrun_for_eq with
        (n:=n) (h1:=h1) (m1:=m1) (h2:=h2);
        eauto.
      + eapply r_one_subst with (e1:=e1); eauto using n_step_to_closed.
      + eapply c_run_subst with (e:=e1); eauto using n_step_to_not_free, n_eq_def.
      + eapply c_run_subst with (e:=e1); eauto using n_step_to_not_free, n_eq_def.
  Qed.

  Lemma w_run_subst:
    forall x P,
    ~ WVar x P ->
    forall e1 v,
    WRun (w_subst x e1 P) v ->
    forall n,
    NStep e1 n ->
    forall e2,
    NStep e2 n ->
    WRun (w_subst x e2 P) v.
  Proof.
    intros.
    apply x_wrun_to_wrun; eauto using n_step_to_closed.
    apply wrun_to_x_wrun in H0; eauto using n_step_to_closed.
    eapply x_wrun_subst; eauto.
  Qed.

  (* ------------------ IFIRST --------------------------------------- *)

  Inductive IFirst (a: access_val) : w_inst -> Prop :=
  | i_first_sync:
    forall c,
    CIn a c ->
    IFirst a (WSync c)
  | i_first_seq:
    forall i j,
    IFirst a i ->
    IFirst a (WSeq i j)
  | i_first_for_1:
    forall r c1 P c2 x,
    CIn a c1 ->
    IFirst a (WFor c1 x r P c2)
  | i_first_for_2:
    forall r n c1 x P c2,
    RFirst r n ->
    IFirst a (w_subst x (NNum n) P) ->
    IFirst a (WFor c1 x r P c2).


  Lemma i_first_subst:
    forall a P x e1 n,
    NStep e1 n ->
    IFirst a (w_subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    ~ WVar x P ->
    IFirst a (w_subst x e2 P).
  Proof.
    intros a P x e1 n Hn Hf.
    remember (w_subst _ _ _) as Q.
    generalize dependent e1.
    generalize dependent n.
    generalize dependent P.
    generalize dependent x.
    induction Hf.
    all: intros y P' n' e1 hn1 heq e2 hnn2 hv.
    - destruct P'; inversion heq; subst; clear heq; simpl.
      + constructor.
        eauto using c_in_subst.
      + rename_hyp (_ = _) as heq.
        destruct (Set_VAR.MF.eq_dec y v); inversion heq.
    - simpl in hv.
      assert (r1: NEq e1 e2) by eauto using n_eq_def.
      destruct P'; invc heq; simpl.
      + apply i_first_seq.
        simpl in hv.
        apply IHHf with (n:=n') (e1:=e1); auto.
      + rename_hyp (_ = _) as heq.
        destruct (Set_VAR.MF.eq_dec y v); subst; invc heq.
    - rename_hyp (_ = _) as heq.
      destruct P'; invc heq.
      destruct (Set_VAR.MF.eq_dec y v);
        rename_hyp (_ = _) as heq;
        invc heq;
        simpl. {
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        apply i_first_for_1.
        eauto using c_in_subst.
      }
      destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
      apply i_first_for_1.
      eauto using c_in_subst.
    - rename_hyp (_ = _) as heq.
      destruct P'; invc heq.
      destruct (Set_VAR.MF.eq_dec y v);
        rename_hyp (_ = _) as heq;
        invc heq;
        simpl.
      {
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        eapply i_first_for_2; eauto.
        eauto using r_first_subst.
     }
     simpl in hv.
     assert (rx: w_subst v (NNum n) (w_subst y e1 P') =
       w_subst y e1 (w_subst v (NNum n) P')). {
       eauto using w_subst_subst_neq, n_step_to_not_free.
     }
     assert (IFirst a (w_subst y e2 (w_subst v (NNum n) P'))). {
       eapply IHHf with (e1:=e1) (e2:=e2); eauto.
       intros N.
       apply wvar_inv_subst in N.
       auto.
     }
     destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
     apply i_first_for_2 with (n:=n); eauto using r_first_subst.
     rewrite w_subst_subst_neq;
          eauto using n_step_to_not_free.
  Qed.

  Lemma i_first_1:
    forall i v,
    WRun i v ->
    forall a,
    List.In a (first v) ->
    IFirst a i.
  Proof.
    intros i v H.
    induction H; intros a Hi; simpl in *.
    - apply i_first_sync.
      eapply c_in_1; eauto.
    - subst.
      apply first_inv_in_seq in Hi.
      intuition.
      + auto using i_first_seq.
      + destruct H1 as (h,(?,Hi)).
        subst.
        simpl in *.
        apply wrun_one in H.
        contradiction.
    - subst.
      apply first_inv_in_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CIn a c1). {
          eapply c_in_1; eauto.
        }
        auto using i_first_for_1.
      }
      apply first_inv_in_seq in Hi.
      destruct Hi as [Hi|(h', (?, Hi))]. {
        apply IHWRun1 in Hi; auto.
        eapply i_first_for_2; eauto using r_step_to_first.
      }
      subst.
      apply wrun_one in H1.
      contradiction.
    - subst.
      apply first_inv_in_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CIn a c1). {
          eapply c_in_1; eauto.
        }
        auto using i_first_for_1.
      }
      apply first_inv_in_seq in Hi.
      destruct Hi as [Hi|(h', (?, Hi))]. {
        eapply i_first_for_2; eauto using r_one_to_first.
      }
      subst.
      simpl in *.
      apply wrun_one in H1.
      contradiction.
  Qed.

  Lemma i_first_2:
    forall i v,
    WRun i v ->
    forall a,
    IFirst a i ->
    List.In a (first v).
  Proof.
    intros i v H.
    induction H; intros.
    - simpl.
      invc H0.
      invc H2.
      eapply ULang.run_all_i_in_to_in; eauto.
    - subst.
      invc H2.
      apply IHWRun1 in H3; auto using first_in_seq_l.
    - subst.
      simpl.
      invc H5. {
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      simpl in *.
      apply r_step_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply first_in_prefix_r.
      apply IHWRun1 in H11.
      auto using first_in_seq_l.
    - simpl in *.
      invc H4. {
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      apply r_one_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply IHWRun in H11.
      auto using first_in_seq_l, first_in_prefix_r, first_in_seq_l.
  Qed.

  (* ------------------ ILAST --------------------------------------- *)

  Inductive ILast (a: access_val) : w_inst -> Prop :=
  | i_last_seq:
    forall i j,
    ILast a j ->
    ILast a (WSeq i j)
  | i_last_for_1:
    forall r n c1 P c2 x,
    RLast r n ->
    (forall e, NStep e n -> ILast a (w_subst x e P)) ->
    ILast a (WFor c1 x r P c2)
  | i_last_for_2:
    forall r n c1 P c2 x,
    RLast r n ->
    (forall e, NStep e n -> CIn a (ULang.i_subst x (SIMT.NExp.from_pure e) c2)) ->
    ILast a (WFor c1 x r P c2)
  .

  Lemma i_last_subst:
    forall a P x e1 n,
    NStep e1 n ->
    ILast a (w_subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    ILast a (w_subst x e2 P).
  Proof.
    intros a P x e1 n Hn Hl.
    remember (w_subst _ _ _) as Q.
    generalize dependent e1.
    generalize dependent n.
    generalize dependent P.
    generalize dependent x.
    induction Hl; intros.
    - destruct P; inversion HeqQ; subst; clear HeqQ; simpl.
      + constructor.
        eauto.
      + destruct (Set_VAR.MF.eq_dec x v); inversion H1.
    - assert (r1: NEq e1 e2) by eauto using n_eq_def.
      destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
      destruct (Set_VAR.MF.eq_dec x0 v). {
        subst.
        invc H4.
        eapply i_last_for_1; eauto.
        rewrite r1 in *.
        assumption.
      }
      invc H4.
      rename x0 into y.
      rename P0 into Q.
      destruct r0 as (e1', e2').
      simpl in *.
      rewrite r1 in H.
      eapply i_last_for_1 with (n:=n); eauto.
      intros.
      rename_hyp (NStep e n) as hn.
      assert (H0 := H0 _ hn).
      assert (H1 := H1 _ hn y (w_subst v e Q) _ _ Hn).
      assert (ILast a (w_subst y e2 (w_subst v e Q))). {
        apply H1; auto.
        rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
      }
      rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
  - destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
    rename x0 into y.
    rename v into z.
    assert (r1: NEq e2 e1) by eauto using n_eq_def.
    destruct (Set_VAR.MF.eq_dec y z).
    all: invc H3. {
      eapply i_last_for_2; eauto.
      rewrite r1.
      auto.
    }
    eapply i_last_for_2 with (n:=n); eauto.
    + rewrite r1.
      auto.
    + intros e He.
      assert (~ NExp.NFree z (NExp.from_pure e2)). {
        rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      }
      assert (~ NExp.NFree y (NExp.from_pure e)). {
        rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      }
      assert (~ NExp.NFree z (NExp.from_pure e1)). {
        rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      }
      rewrite ULang.i_subst_subst_neq_3; auto.
      assert (Hi : CIn a (ULang.i_subst z (NExp.from_pure e) (ULang.i_subst y (NExp.from_pure e1) i0))) by eauto.
      rewrite ULang.i_subst_subst_neq_3 in Hi; auto.
      eapply c_in_subst with (n:=n0) (v:=e1); eauto.
  Qed.

  Lemma i_last_1:
    forall i v,
    WRun i v ->
    forall a,
    List.In a (last v) ->
    ILast a i.
  Proof.
    intros i v H.
    induction H; intros; simpl in *.
    - contradiction.
    - constructor.
      subst.
      rename_hyp (List.In _ _) as Hi.
      apply last_inv_in_seq in Hi.
      destruct Hi as [Hi| (h', (?, Hi))]. {
        auto.
      }
      subst.
      apply wrun_one in H0.
      contradiction.
    - subst.
      rename_hyp (List.In _ _) as Hi.
      apply last_inv_in_prefix in Hi.
      destruct Hi as [(h', (Heq, Hi))|Hi]. {
        symmetry in Heq.
        apply v_seq_inv_one in Heq.
        destruct Heq as (h1', (h3, (?, Heq))).
        subst.
        apply v_prefix_inv_one in Heq.
        destruct Heq as (h4, ?).
        subst.
        apply wrun_one in H3.
        contradiction.
      }
      apply last_inv_in_seq in Hi.
      destruct Hi as [Hi|(h, (Heq, Hi))]. {
        apply last_inv_in_prefix in Hi.
        destruct Hi as [(h', (?, Hi))| Hi]. {
          subst.
          apply wrun_one in H3.
          contradiction.
        }
        apply IHWRun2 in Hi.
        inversion Hi; subst; clear Hi.
        - apply i_last_for_1 with (n:=n0); eauto using r_step_last.
        - eapply i_last_for_2; eauto using r_step_last.
      }
      symmetry in Heq.
      apply v_prefix_inv_one in Heq.
      destruct Heq as (h'', ?).
      subst.
      apply wrun_one in H3.
      contradiction.
    - subst.
      rename_hyp (List.In _ _) as Hi.
      apply last_inv_in_prefix in Hi.
      destruct Hi as [(h', (Heq, Hi))|Hi]. {
        symmetry in Heq.
        apply v_seq_inv_one in Heq.
        destruct Heq as (h1', (h3, (?, Heq))).
        inversion Heq; subst; clear Heq.
        apply wrun_one in H1.
        contradiction.
      }
      apply last_inv_in_seq in Hi.
      simpl in *.
      destruct Hi as [Hi|(h', (Heq, Hi))]. {
        eapply i_last_for_2; eauto using r_one_to_last, n_step_num.
        assert (CIn a (ULang.i_subst x (NExp.NNum n) c2)). {
          eapply c_in_1; eauto.
        }
        intros e He.
        apply c_in_subst with (v:=NNum n) (n:=n); auto using n_step_num.
      }
      inversion Heq; subst; clear Heq.
      eapply i_last_for_1; eauto using r_one_to_last, n_step_num.
      {
        assert ( ILast a (w_subst x (NNum n) P)). {
          apply IHWRun; auto.
        }
        intros.
        auto.
        apply i_last_subst with (e1:=NNum n) (n:=n); eauto using n_step_num.
      }
  Qed.

  Lemma i_last_2:
    forall i v,
    WRun i v ->
    forall a,
    ILast a i ->
    List.In a (last v).
  Proof.
    intros i v H.
    induction H; intros a Hl; invc Hl.
    - apply last_in_seq_r; auto.
    - destruct (r_step_unfold r n r') as [hl|hl]; auto. {
        rename_hyp (WRun (WFor Skip _ _ _ _) _) as hr.
        (* If r' is empty, then hr could not have happened. *)
        apply r_empty_to_has_next in hl.
        contradict hl.
        invc hr. {
          eauto using r_step_to_has_next.
        }
        eauto using r_one_to_has_next.
      }
      assert (List.In a (last m2)). {
        apply IHWRun2.
        assert (RLast r' n0) by eauto using r_step_last_2.
        eapply i_last_for_1; eauto.
      }
      auto using last_in_seq_r.
    - destruct (r_step_unfold r n r') as [hl|hl]; auto. {
        rename_hyp (WRun (WFor Skip _ _ _ _) _) as hr.
        (* If r' is empty, then hr could not have happened. *)
        apply r_empty_to_has_next in hl.
        contradict hl.
        invc hr. {
          eauto using r_step_to_has_next.
        }
        eauto using r_one_to_has_next.
      }
      assert (List.In a (last m2)). {
        apply IHWRun2.
        assert (RLast r' n0) by eauto using r_step_last_2.
        eapply i_last_for_2; eauto.
      }
      auto using last_in_seq_r.
    - assert (List.In a (last m1)). {
        apply IHWRun.
        assert (n0 = n) by eauto using r_one_last_fun.
        subst.
        eauto using n_step_num.
      }
      auto using last_in_seq_r, last_in_seq_l_one.
    - assert (n0 = n) by eauto using r_one_last_fun.
      subst.
      assert (hi: CIn a (i_subst x (NExp.from_pure (NNum n)) c2)). {
        eauto using n_step_num.
      }
      assert (List.In a h2). {
        eapply c_in_2; eauto.
      }
      auto using last_in_seq_r.
  Qed.

  Notation any_inst := (ULang.inst + w_inst) % type.

  Definition OneOf (p:access_val*access_val) (P: any_inst) (Q:any_inst) : Prop :=
    let get_P : access_val -> Prop :=
      match P with
      | inl c => fun a => CIn a c
      | inr P => fun a => ILast a P
      end
    in  
    let get_Q : access_val -> Prop :=
      match Q with
      | inl c => fun a => CIn a c
      | inr Q => fun a => IFirst a Q
      end
    in
    let (a1, a2) := p in
      get_P a1 /\ get_Q a2
      \/
      get_P a2 /\ get_Q a1.

  Inductive IPairIn : (access_val * access_val) -> w_inst -> Prop :=
  | i_pair_in_sync:
    forall p c,
    CPairIn p c ->
    IPairIn p (WSync c)
  | i_pair_in_seq_l:
    forall p i j,
    IPairIn p i ->
    IPairIn p (WSeq i j)
  | i_pair_in_seq_r:
    forall p i j,
    IPairIn p j ->
    IPairIn p (WSeq i j)
  | i_pair_in_seq_both:
    forall p P Q,
    OneOf p (inr P) (inr Q) ->
    IPairIn p (WSeq P Q)
  (* Any iteration *)
  | i_pair_in_for_1:
    forall r e n c1 P c2 p x,
    RPick r n ->
    NStep e n ->
    IPairIn p (w_subst x e P) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_2:
    forall r e n c1 p P x c2,
    RPick r n ->
    NStep e n ->
    CPairIn p (ULang.i_subst x (NExp.from_pure e) c2) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_3:
    forall r e n c1 x p P c2,
    RPick r n ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inl (ULang.i_subst x (NExp.from_pure e) c2)) ->
    IPairIn p (WFor c1 x r P c2)
  (* ---- FIRST ITERATION ONLY ---- *)
  | i_pair_in_for_first_1:
    forall r c1 p P c2 x,
    CPairIn p c1 ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_first_2:
    forall r e n c1 p P x c2,
    RFirst r n ->
    NStep e n ->
    OneOf p (inl c1) (inr (w_subst x e P)) ->
    IPairIn p (WFor c1 x r P c2)
  (* -------- ALL BUT FIRST ---- *)
  | i_pair_in_for_mid_1:
    forall r n c1 p x P c2 e e',
    RPick2 r n ->
    NStep e n ->
    NStep e' (S n) ->
    OneOf p (inl (ULang.i_subst x (NExp.from_pure e) c2)) (inr (w_subst x e' P)) ->
    IPairIn p (WFor c1 x r P c2)

  | i_pair_in_for_mid_2:
    forall r n e e' P x c2 c1 p,
    RPick2 r n ->
    NStep e n ->
    NStep e' (S n) ->
    OneOf p (inr (w_subst x e P)) (inr (w_subst x e' P)) ->
    IPairIn p (WFor c1 x r P c2)
  .

  Lemma i_pair_in_for_run_0_1:
    forall r c1 p h x P c2,
    ULang.RunAll TID_COUNT c1 h ->
    PairIn p h ->
    IPairIn p (WFor c1 r x P c2).
  Proof.
    intros.
    eapply i_pair_in_for_first_1; eauto.
    eapply c_pair_in_1; eauto.
  Qed.

  Lemma i_pair_in_for_run_0_2:
    forall r n c1 P c2 h2 x p,
    RFirst r n ->
    ULang.RunAll TID_COUNT (ULang.i_subst x (NExp.NNum n) c2) h2 ->
    PairIn p h2 ->
    IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    assert (CPairIn p (ULang.i_subst x (NExp.NNum n) c2)). {
      eapply c_pair_in_1; eauto.
    }
    eapply i_pair_in_for_2; eauto using n_step_num.
    auto using r_first_to_pick.
  Qed.

  Lemma i_one_of_1:
    forall i j vi vj,
    WRun i vi ->
    WRun j vj ->
    forall p,
    MOneOf p (last vi) (first vj) ->
    OneOf p (inr i) (inr j).
  Proof.
    intros.
    destruct p as (a1, a2).
    unfold MOneOf in *.
    destruct H1 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto; simpl; intuition.
  Qed.

  Lemma i_one_of_2:
    forall c1 P c2 h v r n p x,
    ULang.RunAll TID_COUNT c1 h ->
    RFirst r n ->
    WRun (WFor ULang.Skip x r P c2) v ->
    MOneOf p h (first v) ->
    OneOf p (inl c1) (inr (w_subst x (NNum n) P)).
  Proof.
    intros.
    apply w_run_inv_for_skip_1 in H1.
    destruct H1 as (n', (Hfst, (m1, (Hr1, (h2, (Hr2, (m2, Heq))))))).
    assert (n' = n) by eauto using r_first_fun.
    subst.
    simpl in *.
    destruct m1 as [h'|h' m1]. {
      simpl in *.
      apply wrun_one in Hr1.
      contradiction.
    }
    destruct p as (a1, a2).
    destruct H2 as [(Ha,Hb)|(Ha,Hb)]; eapply c_in_1 in Ha; eauto. {
      apply first_inv_in_seq in Hb.
      destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
        eapply i_first_1 in Hb; eauto.
        simpl.
        auto.
      }
      inversion Hb1.
    }
    apply first_inv_in_seq in Hb.
    destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
      eapply i_first_1 in Hb; eauto.
      simpl.
      auto.
    }
    inversion Hb1.
  Qed.

  Lemma i_one_of_3:
    forall i v c h p,
    WRun i v ->
    ULang.RunAll TID_COUNT c h ->
    MOneOf p (last v) h ->
    OneOf p (inr i) (inl c).
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto; simpl;
      eapply c_in_1 in H0; eauto; exists ci; intuition
      .
  Qed.

  Lemma i_one_of_4:
    forall c1 h1 i m1 p,
    ULang.RunAll TID_COUNT c1 h1 ->
    WRun i m1 ->
    MOneOf p h1 (first m1) ->
    OneOf p (inl c1) (inr i).
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi,Hj)|(Hi,Hj)];
      simpl;
      eapply c_in_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto.
  Qed.

  Lemma i_one_of_skip_l:
    forall p P,
    ~ OneOf p (inl ULang.Skip) P.
  Proof.
    intros (a1, a2) [c|P]; simpl; intros N;
      destruct N as [(N,_)|(N,_)]; apply c_in_skip in N; auto.
  Qed.

  Lemma i_pair_in_for_cons:
    forall r n r' c1 p P c x,
    RStep r n r' ->
    IPairIn p (WFor ULang.Skip x r' P c) ->
    IPairIn p (WFor c1 x r P c).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - eauto using i_pair_in_for_1, r_step_pick_rev.
    - eauto using i_pair_in_for_2, r_step_pick_rev.
    - eauto using i_pair_in_for_3, r_step_pick_rev.
    - apply c_pair_in_skip in H3.
      contradiction.
    - rename_hyp (OneOf _ _ _) as Hi.
      apply i_one_of_skip_l in Hi.
      contradiction.
    - eauto using i_pair_in_for_mid_1, r_step_pick2_rev.
    - eauto using i_pair_in_for_mid_2, r_step_pick2_rev.
  Qed.

  (** Proving the correctness of IPairIn *)

  Lemma i_pair_in_1:
    forall i h,
    WRun i h ->
    forall p,
    VHist.MPairIn p h ->
    IPairIn p i.
  Proof.
    intros i h H.
    induction H; intros p Hi; simpl in *.
    - destruct Hi as [Hi|Hi]. 2: {
        apply pair_not_in_nil in Hi.
        contradiction.
      }
      eauto using i_pair_in_sync, c_pair_in_1.
    - subst.
      apply VHist.m_pair_in_inv_seq in Hi.
      intuition.
      + auto using i_pair_in_seq_l.
      + auto using i_pair_in_seq_r.
      + eapply i_one_of_1 in H2; eauto.
        eapply i_pair_in_seq_both; eauto.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CPairIn p c1). {
          eapply c_pair_in_1; eauto.
        }
        auto using i_pair_in_for_first_1.
      }
      destruct Hi as [Hi|Hi]. {
        apply VHist.m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|Hi]. {
          assert (IPairIn p (w_subst x (NNum n) P)). {
            apply IHWRun1; auto.
          }
          eapply i_pair_in_for_1; eauto using r_step_to_pick, n_step_num.
        }
        destruct Hi as [Hi|Hi]. {
          apply VHist.m_pair_in_inv_prefix in Hi.
          destruct Hi as [Hi|Hi]. {
            assert (Hc := H2).
            eapply c_pair_in_1 in Hc; eauto.
            simpl in *.
            eapply i_pair_in_for_run_0_2; eauto using r_step_to_first.
          }
          destruct Hi as [Hi|Hi]. {
            apply IHWRun2 in Hi.
            eapply i_pair_in_for_cons; eauto.
          }
          (* are we mid or are we last? *)
          assert (Hx := H).
          apply r_step_unfold in H.
          destruct H as [Hr|Hr]. {
            (* last *)
            apply wrun_for_inv_has_next in H3.
            apply r_empty_to_has_next in Hr.
            contradiction.
          }
          (* mid *)
          destruct Hr as (n', Hr).
          assert (n' = S n) by eauto using r_step_inv_next_eq.
          subst.
          eapply i_one_of_2 in Hi; eauto.
          apply r_first_to_has_next in Hr.
          eapply i_pair_in_for_mid_1 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        }
        apply m_one_of_inv_first_prefix_l in Hi.
        destruct Hi as [Hi|Hi]. {
          eapply i_one_of_3 in Hi; eauto.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_step_to_pick, n_step_num.
        }
        assert (OneOf p (inr (w_subst x (NNum n) P)) (inr (w_subst x (NNum (S n)) P))). {
          apply w_run_inv_for_skip_1 in H3.
          destruct H3 as (n_b, (Hf, (m_b, (Hr, (h2', (Hrr, (m3', Hx))))))).
          assert (n_b = S n) by eauto using r_step_inv_next_eq.
          subst.
          apply m_one_of_inv_first_seq_l in Hi.
          eapply i_one_of_1 in Hi; eauto.
          eauto using wrun_has_many.
        }
        eapply i_pair_in_for_mid_2 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        eapply r_step_to_pick2; eauto using wrun_for_inv_has_next.
      }
      apply m_one_of_inv_first_seq_l in Hi. 2: { eauto using wrun_has_many. }
      eapply i_one_of_4 in Hi; eauto.
      eapply i_pair_in_for_first_2; eauto using r_step_to_first, n_step_num.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|[Hi|Hi]].
      + (* c1 *)
        eapply c_pair_in_1 in Hi; eauto.
        eauto using i_pair_in_for_first_1.
      + apply m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|[Hi|Hi]].
        * (* w_subst x (NNum n) i *)
          apply IHWRun in Hi.
          eapply i_pair_in_for_1; eauto using r_one_to_pick, n_step_num.
        * simpl in *.
          (* c2 *)
          eapply i_pair_in_for_2; eauto using r_one_to_pick, n_step_num.
          eapply c_pair_in_1; eauto.
        * simpl in *.
          (* c2 / w_subst x (NNum n) i *)
          eapply i_one_of_3 in Hi; eauto.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_one_to_pick, n_step_num.
      + (* c1 / w_subst x (NNum n) i *)
        apply m_one_of_inv_first_seq_l in Hi.
        2: { eauto using wrun_has_many. }
        eapply i_one_of_4 in Hi; eauto.
        eapply i_pair_in_for_first_2; eauto using r_one_to_first, n_step_num.
  Qed.

  Fixpoint w_seq (c:ULang.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (c_seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 x r P c2 => WFor (c_seq c c1) x r P c2
   end.

  Lemma n_step_to_subst:
    forall x e n v,
    NStep e n ->
    NClosed v ->
    NStep (n_subst x v e) n.
  Proof.
    intros.
    assert (rx: n_subst x v e = e) by eauto
      using n_subst_not_free, n_step_to_not_free.
    rewrite rx.
    assumption.
  Qed.


  Lemma one_of_subst_r_r:
    forall x e1 e2 P Q p n,
    ~ WVar x Q ->
    OneOf p (inr (w_subst x e1 P)) (inr (w_subst x e1 Q)) ->
    NStep e1 n ->
    NStep e2 n ->
    OneOf p (inr (w_subst x e2 P)) (inr (w_subst x e2 Q)).
  Proof.
    intros.
    destruct p as (a1, a2).
    simpl in *.
    intuition.
    - left; split; eauto using i_first_subst, i_last_subst.
    - right; split; eauto using i_first_subst, i_last_subst.
  Qed.

  Lemma one_of_subst_r_l:
    forall x e1 e2 P c p n,
    NStep e1 n ->
    NStep e2 n ->
    OneOf p (inr (w_subst x e1 P))
            (inl (i_subst x (NExp.from_pure e1) c)) ->
    OneOf p (inr (w_subst x e2 P))
            (inl (i_subst x (NExp.from_pure e2) c)).
  Proof.
    intros.
    destruct p as (a1, a2).
    simpl in *.
    intuition.
    - left; split; eauto using i_last_subst, c_in_subst.
    - right; split; eauto using i_last_subst, c_in_subst.
  Qed.

  Lemma one_of_subst_l_r:
    forall x e1 e2 P c p n,
    NStep e1 n ->
    NStep e2 n ->
    ~ WVar x P ->
    OneOf p (inl (i_subst x (NExp.from_pure e1) c))
            (inr (w_subst x e1 P)) ->
    OneOf p (inl (i_subst x (NExp.from_pure e2) c))
            (inr (w_subst x e2 P)).
  Proof.
    intros.
    destruct p as (a1, a2).
    simpl in *.
    intuition.
    - left; split; eauto using c_in_subst, i_first_subst.
    - right; split; eauto using c_in_subst, i_first_subst.
  Qed.

  Section X_IPairIn.
  Variable x:var.
  Variable v:nexp.

  Inductive X_IPairIn : (access_val * access_val) -> w_inst -> Prop :=
  | x_i_pair_in_sync:
    forall p c,
    CPairIn p (ULang.i_subst x (NExp.from_pure v) c) ->
    X_IPairIn p (WSync c)
  | x_i_pair_in_seq_l:
    forall p i j,
    X_IPairIn p i ->
    X_IPairIn p (WSeq i j)
  | x_i_pair_in_seq_r:
    forall p i j,
    X_IPairIn p j ->
    X_IPairIn p (WSeq i j)
  | x_i_pair_in_seq_both:
    forall p P Q,
    OneOf p (inr (w_subst x v P)) (inr (w_subst x v Q)) ->
    X_IPairIn p (WSeq P Q)
  (* Any iteration *)
  | x_i_pair_in_for_1:
    forall r e n c1 P c2 p y,
    RPick (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    X_IPairIn p (w_subst y e P) ->
    X_IPairIn p (WFor c1 y r P c2)
  | x_i_pair_in_for_2:
    forall r e n c1 p P y c2,
    RPick (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    CPairIn p (ULang.i_subst x (NExp.from_pure v) (ULang.i_subst y (NExp.from_pure e) c2)) ->
    X_IPairIn p (WFor c1 y r P c2)
  | x_i_pair_in_for_3:
    forall r e n c1 y p P c2,
    RPick (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    OneOf p
      (inr (w_subst x v (w_subst y e P)))
      (inl (ULang.i_subst x (NExp.from_pure v) (ULang.i_subst y (NExp.from_pure e) c2))) ->
    X_IPairIn p (WFor c1 y r P c2)
  (* ---- FIRST ITERATION ONLY ---- *)
  | x_i_pair_in_for_first_1:
    forall r c1 p P c2 y,
    CPairIn p (ULang.i_subst x (NExp.from_pure v) c1) ->
    X_IPairIn p (WFor c1 y r P c2)
  | x_i_pair_in_for_first_2:
    forall r e n c1 p P y c2,
    RFirst (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    OneOf p
      (inl (ULang.i_subst x (NExp.from_pure v) c1))
      (inr (w_subst x v (w_subst y e P))) ->
    X_IPairIn p (WFor c1 y r P c2)
  (* -------- ALL BUT FIRST ---- *)
  | x_i_pair_in_for_mid_1:
    forall r n c1 p y P c2 e e',
    RPick2 (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    NStep (n_subst x v e') (S n) ->
    OneOf p
      (inl (ULang.i_subst x (NExp.from_pure v) (ULang.i_subst y (NExp.from_pure e) c2)))
      (inr (w_subst x v (w_subst y e' P))) ->
    X_IPairIn p (WFor c1 y r P c2)

  | x_i_pair_in_for_mid_2:
    forall r n e e' P y c2 c1 p,
    RPick2 (r_subst x v r) n ->
    NStep (n_subst x v e) n ->
    NStep (n_subst x v e') (S n) ->
    OneOf p
      (inr (w_subst x v (w_subst y e P)))
      (inr (w_subst x v (w_subst y e' P))) ->
    X_IPairIn p (WFor c1 y r P c2)
  .

  Lemma x_i_pair_in_1:
    forall p P,
    IPairIn p (w_subst x v P) ->
    ~ WVar x P ->
    NClosed v ->
    X_IPairIn p P.
  Proof.
    intros p P H.
    remember (w_subst _ _ _) as Q.
    generalize dependent P.
    induction H; intros P' Heq Hd Hn.
    - (* x_i_pair_in_sync *)
      destruct P'; invc Heq.
      2: {
        rename_hyp (_ = _) as Heq.
        rename v0 into y.
        destruct (Set_VAR.MF.eq_dec x y); invc Heq.
      }
      constructor.
      assumption.
    - (* x_i_pair_in_seq_l *)
      destruct P'; invc Heq.
      2: {
        rename_hyp (_ = _) as Heq.
        rename v0 into y.
        destruct (Set_VAR.MF.eq_dec x y); invc Heq.
      }
      simpl in Hd.
      apply x_i_pair_in_seq_l.
      auto.
    - (* x_i_pair_in_seq_r *)
      destruct P'; invc Heq.
      2: {
        rename_hyp (_ = _) as Heq.
        rename v0 into y.
        destruct (Set_VAR.MF.eq_dec x y); invc Heq.
      }
      simpl in Hd.
      apply x_i_pair_in_seq_r; eauto.
    - (* x_i_pair_in_seq_both *)
      destruct P'; invc Heq.
      2: {
        rename_hyp (_ = _) as Heq.
        rename v0 into y.
        destruct (Set_VAR.MF.eq_dec x y); invc Heq.
      }
      simpl in Hd.
      auto using x_i_pair_in_seq_both.
    - (* x_i_pair_in_for_1 *)
      destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      assert (hp: X_IPairIn p (w_subst y e P')). {
        eapply IHIPairIn; eauto.
        - rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
        - intros N.
          apply wvar_inv_subst in N.
          auto.
      }
      eapply x_i_pair_in_for_1 in hp; eauto using n_step_to_subst.
    - (* x_i_pair_in_for_2 *)
      destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      eapply x_i_pair_in_for_2 with (e:=e); eauto using n_step_to_subst.
      rewrite i_subst_subst_neq_3; eauto.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
    - destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      eapply x_i_pair_in_for_3 with (e:=e); eauto using n_step_to_subst.
      rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
      rewrite i_subst_subst_neq_3; eauto.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
    - destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      apply x_i_pair_in_for_first_1; auto.
    - destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      apply x_i_pair_in_for_first_2 with (e:=e) (n:=n); auto using n_step_to_subst.
      rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
    - destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      apply x_i_pair_in_for_mid_1 with (e:=e) (n:=n) (e':=e'); auto using n_step_to_subst.
      rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
      rewrite i_subst_subst_neq_3; eauto.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
      + rewrite <- NExp.n_free_from_pure.
        eauto using n_step_to_not_free.
    - destruct P'; invc Heq.
      rename_hyp (_ = _) as Heq.
      rename v0 into y.
      simpl in Hd.
      destruct (Set_VAR.MF.eq_dec x y); invc Heq. {
        intuition.
      }
      apply x_i_pair_in_for_mid_2 with (e:=e) (n:=n) (e':=e'); auto using n_step_to_subst.
      rewrite w_subst_subst_neq; eauto using n_step_to_not_free.
      assert (rx: w_subst y e' (w_subst x v P') = w_subst x v (w_subst y e' P')). {
        apply w_subst_subst_neq; eauto using n_step_to_not_free.
      }
      rename_hyp (OneOf _ _ _) as ho.
      rewrite rx in ho.
      auto.
  Qed.

  Lemma x_i_pair_in_2:
    forall p P,
    X_IPairIn p P ->
    ~ WVar x P ->
    NClosed v ->
    IPairIn p (w_subst x v P).
  Proof.
    intros p P H.
    induction H; intros Ht Hn; simpl in Ht; simpl.
    - eauto using i_pair_in_sync.
    - apply i_pair_in_seq_l.
      auto.
    - apply i_pair_in_seq_r.
      auto.
    - apply i_pair_in_seq_both.
      auto.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      assert (hp: IPairIn p (w_subst x v (w_subst y e P))). {
        eapply IHX_IPairIn; auto.
        intros N.
        apply wvar_inv_subst in N.
        auto.
      }
      apply n_closed_to_step in Hn.
      destruct Hn as (n', Hn).
      assert (~ WVar x P) by intuition.
      rewrite w_subst_subst_neq_5 in hp; eauto using n_step_to_closed.
      apply i_pair_in_for_1 with
        (r:=r_subst x v r)
        (n:=n)
        (c2:=i_subst x (NExp.from_pure v) c2)
        (c1:=i_subst x (NExp.from_pure v) c1) in hp; eauto.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      apply i_pair_in_for_2 with (e:=n_subst x v e) (n:=n); auto.
      eapply c_pair_in_subst with (e1:=n_subst x v e); eauto.
      rename_hyp (CPairIn _ _) as hp.
      rewrite i_subst_subst_neq_5 in hp; auto.
      + rewrite <- NExp.n_subst_from_pure.
        auto.
      + rewrite <- NExp.n_closed_from_pure.
        assumption.
      + intuition.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      apply i_pair_in_for_3 with (e:=n_subst x v e) (n:=n); auto.
      rename_hyp (OneOf _ _ _) as ho.
      rewrite i_subst_subst_neq_5 in ho; auto.
      2: { rewrite <- NExp.n_closed_from_pure. assumption. }
      2: { intuition. }
      rewrite w_subst_subst_neq_5 in ho; auto.
      2: { intuition. }
      rewrite <- NExp.n_subst_from_pure.
      auto.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      auto using i_pair_in_for_first_1.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      apply i_pair_in_for_first_2 with (e:=n_subst x v e) (n:=n); auto.
      rename_hyp (OneOf _ _ _) as ho.
      rewrite w_subst_subst_neq_5 in ho; auto.
      intuition.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      apply i_pair_in_for_mid_1 with
        (n:=n) (e:=n_subst x v e) (e':=n_subst x v e'); auto.
      rename_hyp (OneOf _ _ _) as ho.
      rewrite i_subst_subst_neq_5 in ho; auto.
      2: { rewrite <- NExp.n_closed_from_pure. assumption. }
      2: { intuition. }
      rewrite w_subst_subst_neq_5 in ho; auto.
      2: { intuition. }
      rewrite <- NExp.n_subst_from_pure.
      assumption.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try (intuition; fail).
      apply i_pair_in_for_mid_2 with
        (n:=n) (e:=n_subst x v e) (e':=n_subst x v e'); auto.
      rename_hyp (OneOf _ _ _) as ho.
      rewrite w_subst_subst_neq_5 in ho; auto. 2: { intuition. }
      assert (rx: w_subst x v (w_subst y e' P) = w_subst y (n_subst x v e') (w_subst x v P)). {
        apply w_subst_subst_neq_5; auto.
        intuition.
      }
      rewrite rx in ho.
      auto.
  Qed.

  End X_IPairIn.

  Lemma x_i_pair_in_subst:
    forall p x e1 P,
    X_IPairIn x e1 p P ->
    forall e2 n,
    NStep e1 n ->
    NStep e2 n ->
    ~ WVar x P ->
    X_IPairIn x e2 p P.
  Proof.
    intros p x e1 P H.
    induction H; intros; rename_hyp (~ WVar _ _) as hv; simpl in hv.
    - constructor.
      eapply c_pair_in_subst; eauto.
    - apply x_i_pair_in_seq_l.
      eauto.
    - apply x_i_pair_in_seq_r.
      eauto.
    - apply x_i_pair_in_seq_both.
      eapply one_of_subst_r_r; eauto.
    - eapply x_i_pair_in_for_1 with (n:=n); eauto.
      + eauto using r_pick_subst.
      + eauto using n_step_subst.
      + eapply IHX_IPairIn; eauto.
        intros N.
        apply wvar_inv_subst in N.
        auto.
    - eapply x_i_pair_in_for_2 with (n:=n) (e:=e); eauto.
      + eauto using r_pick_subst.
      + eauto using n_step_subst.
      + eauto using c_pair_in_subst.
    - eapply x_i_pair_in_for_3 with (n:=n) (e:=e); eauto.
      + eauto using r_pick_subst.
      + eauto using n_step_subst.
      + eapply one_of_subst_r_l with (e1:=e1); eauto.
    - eapply x_i_pair_in_for_first_1; eauto.
      eauto using c_pair_in_subst.
    - eapply x_i_pair_in_for_first_2 with (n:=n) (e:=e); eauto.
      + eauto using r_first_subst.
      + eauto using n_step_subst.
      + eapply one_of_subst_l_r with (e1:=e1); eauto.
        intros N.
        apply wvar_inv_subst in N.
        auto.
    - eapply x_i_pair_in_for_mid_1 with (n:=n) (e:=e) (e':=e'); eauto.
      + eauto using r_pick2_subst.
      + eauto using n_step_subst.
      + eauto using n_step_subst.
      + eapply one_of_subst_l_r with (e1:=e1); eauto.
        intros N.
        apply wvar_inv_subst in N.
        auto.
    - eapply x_i_pair_in_for_mid_2 with (n:=n) (e:=e) (e':=e'); eauto.
      + eauto using r_pick2_subst.
      + eauto using n_step_subst.
      + eauto using n_step_subst.
      + eapply one_of_subst_r_r with (e1:=e1); eauto.
        intros N.
        apply wvar_inv_subst in N; auto.
  Qed.
  
  Lemma i_pair_in_subst:
    forall e1 e2 n p x P,
    ~ WVar x P ->
    NStep e1 n ->
    NStep e2 n ->
    IPairIn p (w_subst x e1 P) ->
    IPairIn p (w_subst x e2 P).
  Proof.
    intros.
    apply x_i_pair_in_2; eauto using n_step_to_closed.
    rename_hyp (IPairIn _ _) as hp.
    apply x_i_pair_in_1 in hp; eauto using n_step_to_closed.
    eapply x_i_pair_in_subst; eauto.
  Qed.

  Fixpoint Occurs x P :=
    match P with
    | WSync c => ULang.Occurs x c
    | WSeq P Q => Occurs x P \/ Occurs x Q
    | WFor c1 y r P c2 => ULang.Occurs x c1 \/
      RFree x r \/ x = y \/ Occurs x P \/ ULang.Occurs x c2
    end.

  Lemma occurs_inv_subst_eq:
    forall x e P,
    ~ WVar x P ->
    Occurs x (w_subst x e P) ->
    NFree x e.
  Proof.
    induction P; simpl; intros.
    - rewrite NExp.n_free_from_pure.
      eapply occurs_inv_subst_eq; eauto.
    - intuition.
    - rename_hyp (Occurs _ _) as Hw.
      destruct (Set_VAR.MF.eq_dec x v); simpl in *. {
        subst.
        intuition.
      }
      intuition.
      + rewrite NExp.n_free_from_pure.
        eauto using occurs_inv_subst_eq.
      + eauto using r_free_inv_subst_eq.
      + rewrite NExp.n_free_from_pure.
        eauto using occurs_inv_subst_eq.
  Qed.

  Lemma w_subst_not_occurs:
    forall x P,
    ~ Occurs x P ->
    forall v,
    w_subst x v P = P.
  Proof.
    induction P; simpl; intros.
    - rewrite i_subst_not_occurs; auto.
    - assert (~ Occurs x P1) by intuition.
      assert (~ Occurs x P2) by intuition.
      rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assert (~ ULang.Occurs v i) by intuition.
        rewrite i_subst_not_occurs; auto.
        rewrite r_subst_not_free; auto.
      }
      rewrite i_subst_not_occurs; auto.
      rewrite r_subst_not_free; auto.
      assert (~  (Occurs x P \/ ULang.Occurs x i0) ) by intuition.
      rewrite i_subst_not_occurs; auto.
      rewrite IHP; auto.
  Qed.

  Definition WClosed P :=
    forall x,
    ~ Occurs x P.

  Lemma w_closed_inv_seq:
    forall P1 P2,
    WClosed (WSeq P1 P2) ->
    WClosed P1 /\ WClosed P2.
  Proof.
    unfold WClosed.
    intros.
    split;
      simpl in *;
      intros;
      assert (H:= H x);
      intuition.
  Qed.

  Lemma w_closed_inv_for:
    forall c1 x r P c2,
    WClosed (WFor c1 x r P c2) ->
    CClosed c1
    /\ RClosed r
    /\ (forall y, x <> y ->  ~ Occurs y P)
    /\ (forall y, x <> y -> ~ ULang.Occurs y c2).
  Proof.
    intros.
    unfold WClosed in H.
    simpl in *.
    repeat split; intros y n; assert (H := H y); intuition.
  Qed.

  Inductive GetFirst : w_inst -> inst -> Prop :=
  | get_first_sync:
    forall c,
    GetFirst (WSync c) c
  | get_first_seq:
    forall P c Q,
    GetFirst P c ->
    GetFirst (WSeq P Q) c
  | get_first_for:
    forall c1 x r P n c2 c,
    RFirst r n ->
    GetFirst (w_subst x (NNum n) P) c ->
    GetFirst (WFor c1 x r P c2) (ULang.c_seq c1 c).

  Lemma get_first_fun:
    forall P c,
    GetFirst P c ->
    forall c',
    GetFirst P c' ->
    c' = c.
  Proof.
    intros P c H.
    induction H; intros c' Hg; invc Hg; auto.
    assert (n0 = n) by eauto using r_first_fun.
    subst.
    assert (c4 = c) by eauto.
    subst.
    reflexivity.
  Qed.

  Lemma get_first_subst:
    forall P c,
    GetFirst P c ->
    forall x v,
    NClosed v ->
    ~ WVar x P ->
    GetFirst (w_subst x v P) (i_subst x (NExp.from_pure v) c).
  Proof.
    intros P c H.
    induction H; intros y v Hc Hv.
    - simpl.
      constructor.
    - simpl in *.
      apply get_first_seq.
      eauto.
    - simpl.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        simpl in *.
        intuition.
      }
      assert (Hn : NClosed (NNum n)) by auto using n_closed_num.
      simpl in *.
      assert (Hw: ~ WVar y (w_subst x (NNum n) P) ). {
        intros N.
        apply wvar_inv_subst in N.
        intuition.
      }
      assert (IHGetFirst := IHGetFirst y v Hc Hw).
      rewrite ULang.i_subst_c_seq.
      apply get_first_for with (n:=n).
      + auto using r_first_subst_1.
      + rewrite w_subst_subst_neq; auto.
  Qed.

  Lemma get_first_exists:
    forall P,
    CanRun P ->
    exists c, GetFirst P c.
  Proof.
    intros P H.
    induction H.
    - eexists.
      constructor.
    - destruct IHCanRun1 as (c, Hg).
      eexists.
      constructor.
      eauto.
    - destruct H as (n, Hp).
      assert (RPick r n) by eauto using r_first_to_pick.
      assert (Hg : exists c, GetFirst (w_subst x (NNum n) P) c). {
        eauto.
      }
      destruct Hg as (c, Hg).
      eexists.
      apply get_first_for with (n:=n); eauto.
  Qed.

  Lemma get_first_1:
    forall P c,
    GetFirst P c ->
    forall a,
    CIn a c ->
    IFirst a P.
  Proof.
    intros P c H.
    induction H; intros a Hi.
    - constructor; auto.
    - constructor.
      auto.
    - apply c_in_inv_c_seq in Hi.
      destruct Hi as [Hi|Hi].
      + auto using i_first_for_1.
      + eauto using i_first_for_2.
  Qed.

  Lemma get_first_2:
    forall P a,
    IFirst a P ->
    forall c,
    GetFirst P c ->
    CIn a c.
  Proof.
    intros P a H.
    induction H; intros c_out Hg; invc Hg; auto.
    - eauto using c_in_c_seq_l.
    - assert (n0 = n) by eauto using r_first_fun.
      subst.
      eauto using c_in_c_seq_r.
  Qed.

  Corollary get_first_spec:
    forall P c,
    GetFirst P c ->
    forall a,
    IFirst a P <-> CIn a c.
  Proof.
    split; intros.
    - eauto using get_first_2.
    - eauto using get_first_1.
  Qed.

  Lemma distinct_subst:
    forall P,
    Distinct P ->
    forall x v,
    Distinct (w_subst x v P).
  Proof.
    induction P; simpl; intros; auto. {
      destruct H; eauto.
    }
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      simpl.
      intuition.
      eauto using distinct_subst.
    }
    simpl.
    intuition.
    - eauto using distinct_subst.
    - rename_hyp (WVar v _) as Hv.
      apply wvar_inv_subst in Hv.
      contradiction.
    - rename_hyp (Var v _) as Hv.
      apply var_inv_subst in Hv.
      contradiction.
    - auto using ULang.distinct_subst.
  Qed.

  Inductive GetLast : w_inst -> inst -> Prop :=
  | get_last_sync:
    forall c,
    GetLast (WSync c) Skip
  | get_last_seq:
    forall P c Q,
    GetLast Q c ->
    GetLast (WSeq P Q) c
  | get_last_for:
    forall c1 x r P n c2 c,
    RLast r n ->
    GetLast (w_subst x (NNum n) P) c ->
    GetLast (WFor c1 x r P c2) (ULang.c_seq c (i_subst x (NExp.NNum n) c2)).

  Lemma get_last_1:
    forall P c,
    GetLast P c ->
    forall a,
    CIn a c ->
    ILast a P.
  Proof.
    intros P c H.
    induction H; intros a Hc.
    - apply c_in_skip in Hc.
      contradiction.
    - constructor.
      simpl in *.
      auto.
    - simpl in *.
      apply c_in_inv_c_seq in Hc.
      destruct Hc. {
        eapply i_last_for_1; eauto.
        intros.
        apply i_last_subst with (e1:=NNum n) (n:=n); auto using n_step_num.
      }
      eapply i_last_for_2; eauto.
      intros.
      apply c_in_subst with (v:=NNum n) (n:=n); auto using n_step_num.
  Qed.

  Lemma get_last_2:
    forall P a,
    ILast a P ->
    forall c,
    GetLast P c ->
    CIn a c.
  Proof.
    intros P a H.
    induction H; intros c Hg; invc Hg.
    - auto.
    - assert (n0 = n) by eauto using r_last_fun.
      subst.
      eauto using c_in_c_seq_l, n_step_num.
    - assert (n0 = n) by eauto using r_last_fun.
      subst.
      rename_hyp (forall e, _ -> _) as hi.
      assert (hi := hi (NNum n)).
      simpl in *.
      eauto using c_in_c_seq_r, n_step_num.
  Qed.

  Corollary get_last_spec:
    forall P c,
    GetLast P c ->
    forall a,
    ILast a P <-> CIn a c.
  Proof.
    split; intros.
    - eauto using get_last_2.
    - eauto using get_last_1.
  Qed.

  Lemma get_last_exists:
    forall P,
    CanRun P ->
    exists c, GetLast P c.
  Proof.
    intros P H.
    induction H.
    - eexists.
      constructor.
    - destruct IHCanRun2 as (c, Hg).
      eexists.
      constructor.
      eauto.
    - edestruct r_has_next_to_last as (n, Hl); eauto.
      assert (RPick r n) by eauto using r_last_to_pick.
      assert (Hg : exists c, GetLast (w_subst x (NNum n) P) c). {
        eauto.
      }
      destruct Hg as (c, Hg).
      eexists.
      apply get_last_for with (n:=n); eauto.
  Qed.

  Lemma i_pair_in_2_for_1:
    forall x n c2 h2 r P e' e p h0 m0 h1 m1 m2,
    RunAll TID_COUNT (i_subst x (NExp.NNum n) c2) h2 ->
    ~ WVar x P ->
    NStep e' (S n) ->
    NStep e n ->
    OneOf p (inl (i_subst x (NExp.from_pure e) c2)) (inr (w_subst x e' P)) ->
    RFirst r (S n) ->
    RunAll TID_COUNT Skip h0 ->
    WRun (w_subst x (NNum (S n)) P) m0 ->
    MPairIn p
      (v_prefix h1
         (v_seq m1
            (v_prefix h2 (v_seq (v_one h0) (v_seq m0 m2))))).
  Proof.
    intros.
    rename_hyp (RunAll _ Skip _) as hr.
    apply run_all_inv_skip in hr.
    subst.
    simpl.
    rewrite v_prefix_nil.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e' P) m0). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (RunAll TID_COUNT (i_subst x (NExp.from_pure e) c2) h2). {
      apply c_run_subst with (e:=NNum n) (n:=n);
      eauto using n_step_num, n_eq_def.
    }
    destruct ho as [(hc2,hf)|(hc2,hf)];
    eapply i_first_2 with (v:=m0) in hf; auto;
    apply c_in_2 with (h:=h2) in hc2; auto;
    apply m_pair_in_prefix_r;
    apply m_pair_in_seq_r.
    - auto using m_pair_in_prefix_1, first_in_seq_l.
    - auto using m_pair_in_prefix_2, first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_2:
    forall x n h2 P e' e p h0 m0 h1 m1 m2,
    ~ WVar x P ->
    WRun (w_subst x (NNum n) P) m1 ->
    NStep e' (S n) ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inr (w_subst x e' P)) ->
    RunAll TID_COUNT Skip h0 ->
    WRun (w_subst x (NNum (S n)) P) m0 ->
    MPairIn p
      (v_prefix h1
         (v_seq m1 (v_prefix h2 (v_seq (v_one h0) (v_seq m0 m2))))).
  Proof.
    intros.
    rename_hyp (RunAll _ Skip _) as hr.
    apply run_all_inv_skip in hr.
    subst.
    simpl.
    rewrite v_prefix_nil.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (WRun (w_subst x e' P) m0). {
      eapply w_run_subst; eauto using n_step_num.
    }
    apply m_pair_in_prefix_r.
    destruct ho as [(hl,hf)|(hl,hf)];
      apply i_first_2 with (v:=m0) in hf; auto;
      apply i_last_2 with (v:=m1) in hl; auto.
    * auto using m_pair_in_seq_both_1,first_in_prefix_r, first_in_seq_l.
    * auto using m_pair_in_seq_both_2,first_in_prefix_r, first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_3:
    forall x n P e p c1 h1 m1 m2,
    ~ WVar x P ->
    RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    NStep e n ->
    OneOf p (inl c1) (inr (w_subst x e P)) ->
    MPairIn p (v_prefix h1 (v_seq m1 m2)).
  Proof.
    intros.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    destruct ho as [(hc,hf)|(hc,hf)];
    apply c_in_2 with (h:=h1) in hc; auto;
    apply i_first_2 with (v:=m1) in hf; auto.
    * apply m_pair_in_prefix_1; auto using first_in_seq_l.
    * apply m_pair_in_prefix_2; auto using first_in_seq_l.
  Qed.

  Lemma i_pair_in_2_for_4:
    forall x n P e p h1 m1 m2 c2 h2,
    ~ WVar x P ->
    WRun (w_subst x (NNum n) P) m1 ->
    RunAll TID_COUNT (i_subst x (NExp.NNum n) c2) h2 ->
    NStep e n ->
    OneOf p (inr (w_subst x e P)) (inl (i_subst x (NExp.from_pure e) c2)) ->
    MPairIn p (v_prefix h1 (v_seq m1 (v_prefix h2 m2))).
  Proof.
    intros.
    destruct p as (a1, a2).
    rename_hyp (OneOf _ _ _) as ho.
    assert (WRun (w_subst x e P) m1). {
      eapply w_run_subst; eauto using n_step_num.
    }
    assert (RunAll TID_COUNT (i_subst x (NExp.from_pure e) c2) h2). {
      eapply c_run_subst with (e:=NNum n); eauto using n_step_num, n_eq_def.
    }
    destruct ho as [(hl, hc)|(hl,hc)];
    apply i_last_2 with (v:=m1) in hl; auto;
    apply c_in_2 with (h:=h2) in hc; auto;
    apply m_pair_in_prefix_r.
    - apply m_pair_in_seq_both_1; auto using first_in_prefix_l.
    - apply m_pair_in_seq_both_2; auto using first_in_prefix_l.
  Qed.


  Lemma i_pair_in_2:
    forall i h,
    WRun i h ->
    Distinct i ->
    forall p,
    IPairIn p i ->
    VHist.MPairIn p h.
  Proof.
    intros i h H.
    induction H; intros Hd p Hp.
    - invc Hp.
      left.
      eauto using c_pair_in_to_pair_in.
    - subst.
      destruct Hd as (Hd1, Hd2).
      invc Hp.
      + apply m_pair_in_seq_l.
        apply IHWRun1; auto.
      + apply m_pair_in_seq_r.
        apply IHWRun2; auto.
      + destruct p as (a1, a2).
        simpl in *.
        all: intuition.
        all: rename_hyp (ILast _ _) as hl.
        all: rename_hyp (IFirst _ _) as hf.
        all: eapply i_first_2 in hf; eauto.
        all: eapply i_last_2 in hl; eauto.
        * auto using m_pair_in_seq_both_1.
        * auto using m_pair_in_seq_both_2.
    - subst.
      simpl.
      simpl in Hd.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      invc Hp.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          assert (MPairIn p m1). {
            apply IHWRun1.
            - auto using distinct_subst.
            - eapply i_pair_in_subst; eauto using n_step_num.
          }
          auto using m_pair_in_prefix_r, m_pair_in_seq_l.
        }
        assert (MPairIn p m2). {
          apply IHWRun2.
          - simpl.
            intuition.
          - eapply i_pair_in_for_1; eauto.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          apply m_pair_in_prefix_r.
          apply m_pair_in_seq_r.
          apply m_pair_in_prefix_l.
          eapply c_pair_in_to_pair_in; eauto.
          assert (hx: NExp.NNum n = NExp.from_pure (NNum n)) by reflexivity.
          rewrite hx.
          eapply c_pair_in_subst; eauto using n_step_num.
        }
        assert (MPairIn p m2). {
          apply IHWRun2.
          - simpl; intuition.
          - eapply i_pair_in_for_2; eauto using r_step_inv_r.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + rename_hyp (RPick _ _) as hp.
        eapply r_step_pick_advance in hp; eauto.
        destruct hp as [hp|hp]. {
          subst.
          apply i_pair_in_2_for_4 with (x:=x) (n:=n) (P:=P) (c2:=c2) (e:=e);
            auto; intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2.
          - simpl; intuition.
          - eapply i_pair_in_for_3; eauto using r_step_inv_r.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_r.
      + apply m_pair_in_prefix_l.
        eapply c_pair_in_to_pair_in; eauto.
      + assert (n0 = n). {
          assert (RFirst r n) by eauto using r_step_to_first.
          eauto using r_first_fun.
        }
        subst.
        apply i_pair_in_2_for_3 with (x:=x) (n:=n) (P:=P) (e:=e) (c1:=c1);
          eauto using n_step_num; intuition.
      + rename_hyp (RPick2 _ _) as hp.
        eapply r_step_pick2_advance in hp; eauto.
        destruct hp as [(?,hp)|hp]. {
          subst.
          rename_hyp (WRun (WFor _ _ _ _ _) _ ) as hr.
          invc hr. 2: {
            rename_hyp (ROne _ _) as ro.
            assert (n0 = S n). {
              assert (RFirst r' n0) by eauto using r_one_to_first.
              eauto using r_first_fun.
            }
            subst.
            eapply i_pair_in_2_for_1; eauto; intuition.
          }
          assert (n0 = S n). {
            assert (RFirst r' n0) by eauto using r_step_to_first.
            eauto using r_first_fun.
          }
          subst.
          eapply i_pair_in_2_for_1; eauto; intuition.
        }
        assert (MPairIn p m2). {
          apply IHWRun2.
          - simpl; intuition.
          - eapply i_pair_in_for_mid_1; eauto.
        }
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        apply m_pair_in_prefix_r.
        auto.
      + rename_hyp (RPick2 _ _) as hp.
        eapply r_step_pick2_advance in hp; eauto.
        destruct hp as [(?,hp)|hp]. {
          subst.
          rename_hyp (WRun (WFor _ _ _ _ _) _ ) as hr.
          invc hr. 2: {
            assert (n0 = S n). {
              assert (RFirst r' n0) by eauto using r_one_to_first.
              eauto using r_first_fun.
            }
            subst.
            eapply i_pair_in_2_for_2; eauto.
          }
          assert (n0 = S n). {
            assert (RFirst r' n0) by eauto using r_step_to_first.
            eauto using r_first_fun.
          }
          subst.
          eapply i_pair_in_2_for_2; eauto.
        }
        assert (MPairIn p m2). {
          apply IHWRun2.
          - simpl; intuition.
          - eapply i_pair_in_for_mid_2; eauto.
        }
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        apply m_pair_in_prefix_r.
        auto.
    - subst.
      simpl.
      invc Hp.
      + simpl in Hd.
        destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
        assert (MPairIn p m1). {
          apply IHWRun.
          - auto using distinct_subst.
          - assert (n0 = n) by eauto using r_one_pick_fun.
            subst.
            eapply i_pair_in_subst; eauto using n_step_num.
        }
        auto using m_pair_in_prefix_r, m_pair_in_seq_l.
      + assert (n0 = n) by eauto using r_one_pick_fun.
        subst.
        apply m_pair_in_prefix_r.
        apply m_pair_in_seq_r.
        simpl.
        eapply c_pair_in_to_pair_in; eauto.
        assert (hx: NExp.NNum n = NExp.from_pure (NNum n)) by reflexivity.
        rewrite hx.
        eapply c_pair_in_subst; eauto using n_step_num.
      + assert (n0 = n) by eauto using r_one_pick_fun.
        subst.
        assert (rx: v_one h2 = v_prefix h2 (v_one [])). {
          simpl.
          rewrite app_nil_r.
          reflexivity.
        }
        rewrite rx.
        destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
        apply i_pair_in_2_for_4 with (x:=x) (n:=n) (P:=P) (c2:=c2) (e:=e);
          auto; intuition.
      + apply m_pair_in_prefix_l.
        eapply c_pair_in_to_pair_in; eauto.
      + assert (n0 = n) by eauto using r_one_to_first, r_first_fun.
        subst.
        destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
        apply i_pair_in_2_for_3 with (x:=x) (n:=n) (P:=P) (e:=e) (c1:=c1);
          auto using n_step_num; intuition.
      + rename_hyp (RPick2 _ _) as hp.
        contradict hp.
        eauto using r_one_to_not_pick2.
      + rename_hyp (RPick2 _ _) as hp.
        contradict hp.
        eauto using r_one_to_not_pick2.
  Qed.

  Definition DRF P :=
    forall p,
    IPairIn p P ->
    AVal.Safe (fst p) (snd p).

End Defs.

Module WLangNotations.
  Import ULang.CLangNotations.
  Infix ";" := WSeq (at level 50, only printing)
    : lang_scope.
  Notation "c [ x := v ]" := (i_subst x v c) (at level 30, only printing)
    : lang_scope. 
  Infix ";;" := w_seq (at level 50, only printing)
    : lang_scope.
  Notation "c1 ';' 'for' x 'in' r '{' P ',' c2 '}' " := (WFor c1 x r P c2) (at level 50, only printing)
    : lang_scope.
  Infix "∈" := IPairIn (at level 30, only printing)
    : lang_scope.
End WLangNotations.