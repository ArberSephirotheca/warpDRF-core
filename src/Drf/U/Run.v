From Stdlib Require Import Lists.List.
From Faial.Core Require Import Var.
From Faial.Core Require Import AVal.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import InUtil.
From Faial.Core Require Import Tictac.
From Faial.Core Require Import Hist.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Expr Require Import SIMT.B.Exp.
From Faial.Expr Require Import SIMT.R.Exp.
From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.

Import ListNotations.

Section Defs.
  Notation history := (list access_val).

  Context `{T:Tasks}.

  Section RUN.
  Variable tid: nat.
  Notation NStep := (NStep tid).
  Notation BStep := (BStep tid).
  Notation AStep := (AStep tid).

  Inductive Run : t -> history -> Prop :=
  | run_skip:
    Run Skip []
  | run_access:
    forall e v,
    AStep e v ->
    Run (MemAcc e) [v]
  | run_seq:
    forall i j h1 h2,
    Run i h1 ->
    Run j h2 ->
    Run (Seq i j) (h1 ++ h2)
  | run_if:
    forall i j e b hi hj,
    BStep e b ->
    Run i hi ->
    Run j hj ->
    Run (If e i j) (if b then hi else hj)
  | run_for_cons:
    forall r r' n i x h1 h2,
    RStep tid r n r' ->
    Run (f x (NNum n) i) h1 ->
    Run (For x r' i) h2 ->
    Run (For x r i) (h1 ++ h2)
  | run_for_nil:
    forall x i r,
    REmpty tid r ->
    Run (For x r i) []
  | run_decl:
    forall x i h,
    Run i h ->
    Run (Decl x i) h
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

  Inductive CanRun : t -> Prop :=
  | can_run_skip:
    CanRun Skip
  | can_run_seq:
    forall i j,
    CanRun i ->
    CanRun j ->
    CanRun (Seq i j)
  | can_run_if:
    forall e b i j,
    BStep e b ->
    CanRun i ->
    CanRun j ->
    CanRun (If e i j)
  | can_run_acc:
    forall e v,
    AStep e v ->
    CanRun (MemAcc e)
  | can_run_for:
    forall x r i,
    RDefined tid r ->
    (forall n, RPick tid r n -> CanRun (f x (NNum n) i)) ->
    CanRun (For x r i)
  | can_run_decl:
    forall x i,
    CanRun i ->
    CanRun (Decl x i).
  End RUN.

  Definition REq i1 i2 :=
   forall n h,
   Run n i1 h <-> Run n i2 h.

  Inductive RunAll : nat -> t -> history -> Prop :=
  | run_all_zero:
    forall i,
    RunAll 0 i []
  | run_all_succ:
    forall i n h1 h2,
    Run n i h1 ->
    RunAll n i h2 ->
    RunAll (S n) i (h1 ++ h2).

  Lemma run_all_inv_in:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    exists m h',
    m < n /\ Run m i h' /\ incl h' h /\ List.In x h'.
  Proof.
    intros n i h H.
    induction H; intros. { contradiction. }
    apply in_app_or in H1.
    destruct H1.
    - exists n.
      exists h1.
      eauto using InUtil.incl_app_refl_l with *.
    - edestruct IHRunAll as (m, (h, (Hl, (Hr, (Hi,Hj))))); eauto.
      exists m.
      exists h.
      auto using incl_appr with *.
  Qed.

  Lemma run_inv_in_eq:
    forall n i h,
    Run n i h ->
    forall a,
    List.In a h ->
    av_owner a = n.
  Proof.
    intros n i h H.
    induction H; intros.
    - contradiction.
    - simpl in *.
      intuition.
      subst.
      eauto using a_step_inv_tid.
    - apply List.in_app_iff in H1.
      destruct H1; auto.
    - destruct b; auto.
    - apply List.in_app_iff in H2.
      intuition.
    - contradiction.
    - auto.
  Qed.

  Lemma run_all_inv_in_eq:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    av_owner x < n.
  Proof.
    intros.
    eapply run_all_inv_in in H0; eauto.
    destruct H0 as (m, (h', (?, (Hr, (Hi, Hj))))).
    eapply run_inv_in_eq in Hj; eauto.
    subst.
    assumption.
  Qed.

  Lemma run_all_inv_run:
    forall n i h,
    RunAll n i h ->
    forall m,
    m < n ->
    exists h',
    Run m i h' /\ incl h' h.
  Proof.
    intros n i h H.
    induction H; intros m Hl. { inversion Hl. }
    inversion Hl; subst; clear Hl. {
      exists h1.
      split; auto.
      apply InUtil.incl_app_refl_l.
    }
    apply IHRunAll in H2.
    destruct H2 as (h', (Hr, Hi)).
    exists h'.
    split; auto.
    apply incl_tran with (m:= h2); auto.
    apply InUtil.incl_app_refl_r.
  Qed.

  Section XRun.
  Variable tid:nat.
  Variable x:var.
  Variable e:nexp.
  Notation AStep := (AStep tid).
  Notation NStep := (NStep tid).
  Notation BStep := (BStep tid).

  Inductive XRun : t -> history -> Prop :=
  | x_run_skip:
    XRun Skip []
  | x_run_access:
    forall a v,
    AStep (a_subst x e a) v ->
    XRun (MemAcc a) [v]
  | x_run_seq:
    forall i j h1 h2,
    XRun i h1 ->
    XRun j h2 ->
    XRun (Seq i j) (h1 ++ h2)
  | x_run_if:
    forall e' i j b hi hj,
    BStep (b_subst x e e') b ->
    XRun i hi ->
    XRun j hj ->
    XRun (If e' i j) (if b then hi else hj)
  | x_run_for_cons_eq:
    forall r r' n i h1 h2,
    RStep tid (r_subst x e r) n r' ->
    Run tid (f x (NNum n) i) h1 ->
    Run tid (For x r' i) h2 ->
    XRun (For x r i) (h1 ++ h2)
  | x_run_for_cons_neq:
    forall r r' n y i h1 h2,
    x <> y ->
    RStep tid (r_subst x e r) n r' ->
    XRun (f y (NNum n) i) h1 ->
    XRun (For y r' i) h2 ->
    XRun (For y r i) (h1 ++ h2)
  | x_run_for_nil:
    forall r y i,
    REmpty tid (r_subst x e r) ->
    XRun (For y r i) []
  | x_run_decl_eq:
    forall i h,
    Run tid i h ->
    XRun (Decl x i) h
  | x_run_decl_neq:
    forall y i h,
    x <> y ->
    XRun i h ->
    XRun (Decl y i) h
  .
  End XRun.

  Lemma run_to_x_run:
    forall n x e i h,
    Run n (f x e i) h ->
    forall m,
    NStep n e m ->
    XRun n x e i h.
  Proof.
    intros.
    remember (f x e i) as j.
    generalize dependent x.
    generalize dependent e.
    generalize dependent i.
    induction H; intros.
    - destruct i; inversion Heqj; subst; clear Heqj.
      constructor.
    - destruct i; inversion Heqj; subst; clear Heqj.
      constructor.
      assumption.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      constructor; eauto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      eauto using x_run_if.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      rename x0 into y.
      rename v into z.
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        eapply x_run_for_cons_eq; eauto.
      }
      rename r0 into r.
      rename n0 into n'.
      apply x_run_for_cons_neq with (r:=r) (r':=r') (n:=n'); auto.
      + apply IHRun1; auto.
        rewrite subst_subst_neq_3; auto.
        eauto using n_step_to_not_free.
      + apply IHRun2; auto.
        simpl.
        destruct (Set_VAR.MF.eq_dec y z). {
          contradiction.
        }
        simpl.
        f_equal.
        rewrite r_subst_closed; eauto using r_step_to_closed_r.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      rename x0 into x.
      rename v into y.
      destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        eauto using x_run_for_nil.
      }
      eapply x_run_for_nil; auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct (Set_VAR.MF.eq_dec x0 v). {
        subst.
        eapply x_run_decl_eq.
        eassumption.
      }
      eapply x_run_decl_neq; eauto.
  Qed.

  Lemma x_run_to_run:
    forall n x e i h,
    XRun n x e i h ->
    forall m,
    NStep n e m ->
    Run n (f x e i) h.
  Proof.
    intros n x e i h H.
    induction H; intros; simpl.
    - constructor.
    - constructor; auto.
    - constructor; eauto.
    - constructor; eauto.
    - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      eapply run_for_cons; eauto.
    - destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        simpl in *.
        destruct (Set_VAR.MF.eq_dec y y) as [_|?]; try contradiction.
      }
      simpl in *.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      assert (Hy: r_subst x e r' = r'). {
       rewrite r_subst_closed; eauto using r_step_to_closed_r.
      }
      rewrite Hy in *.
      eapply run_for_cons; eauto.
      assert (Hx: Run n (f x e (f y (NNum n0) i)) h1). {
        eauto.
      }
      rewrite subst_subst_neq_3 in Hx; auto.
      eauto using n_step_to_not_free.
    - destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        eapply run_for_nil; eauto.
      }
      eapply run_for_nil; eauto.
    - destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      eapply run_decl.
      eassumption.
    - destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_decl.
      eauto.
  Qed.

  Lemma run_subst t:
    forall c x e1 h n,
    NStep t e1 n ->
    Run t (f x e1 c) h ->
    forall e2,
    NStep t e2 n ->
    Run t (f x e2 c) h.
  Proof.
    intros c x e1 h n He1 Hr.
    eapply run_to_x_run in Hr; eauto.
    intros.
    eapply x_run_to_run; eauto.
    generalize dependent e2.
    generalize dependent n.
    induction Hr; intros.
    - simpl.
      constructor.
    - simpl.
      constructor.
      assert (r1: NEq t e1 e2) by eauto using n_eq_def.
      eapply a_step_proper; eauto using eq_subst_proper.
    - simpl.
      constructor; eauto.
    - eapply x_run_if; eauto.
      assert (r1: NEq t e1 e2) by eauto using n_eq_def.
      rewrite r1 in H.
      eauto using x_run_if.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      assert (r1: NEq t e1 e2) by eauto using n_eq_def.
      eapply x_run_for_cons_eq; eauto.
      rewrite <- r1.
      assumption.
    - simpl in *.
      rename e1 into e.
      rename e2 into e'.
      assert (r1: NEq t e e') by eauto using n_eq_def.
      eapply x_run_for_cons_neq; eauto.
      rewrite <- r1.
      auto.
    - rename e1 into e.
      rename e2 into e'.
      assert (r1: NEq t e e') by eauto using n_eq_def.
      eapply x_run_for_nil; eauto.
      rewrite <- r1.
      auto.
    - eapply x_run_decl_eq; eassumption.
    - eapply x_run_decl_neq; eauto.
  Qed.

  Lemma run_all_inv_skip:
    forall n h,
    RunAll n Skip h ->
    h = [].
  Proof.
    induction n; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    apply IHn in H2.
    subst.
    simpl in *.
    inversion H1; subst; clear H1.
    reflexivity.
  Qed.

  Lemma run_to_can_run:
    forall i c h,
    Run i c h ->
    CanRun i c.
  Proof.
    intros.
    induction H.
    - constructor.
    - econstructor.
      eauto.
    - constructor; auto.
    - econstructor; eauto.
    - constructor.
      + eauto using r_step_to_defined_l.
      + intros.
        rename_hyp (RPick _ _ _) as hr.
        eapply r_step_inv_pick in hr; eauto.
        destruct hr as [hr|hr]. {
          subst.
          assumption.
        }
        invc IHRun2.
        eauto.
     - apply can_run_for.
       + auto using r_empty_to_defined.
       + intros.
        contradict H.
        eauto using r_pick_to_empty.
     - econstructor; eauto.
  Qed.

  Lemma run_all_impl:
    forall m,
    forall c1 c2,
    (forall n h, n < m -> Run n c1 h -> Run n c2 h) ->
    forall h,
    RunAll m c1 h ->
    RunAll m c2 h.
  Proof.
    induction m; intros. {
      inversion H0; subst; clear H0.
      apply run_all_zero.
    }
    inversion H0; subst; clear H0.
    apply run_all_succ; eauto.
  Qed.
End Defs.
