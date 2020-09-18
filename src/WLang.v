Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationPairs.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.
Require Import PairInUtil.
Require Import VHist.
Require Import RangeList.
Require Import Conc.
Require Import Tictac.

Require RangeList.
Require Import Lia.

Import ListNotations.
Require Conc.

Section Defs.

  Notation history := (list access_val).

  Notation mhistory := (list history).

  Notation histpair := (mhistory * history) % type.

  Context `{T:Tasks}.
  Context {A:Access}.

  Open Scope vhist_scope.

(* -------------------- RUN --------------------------- *)


  Inductive w_inst :=
  | WSync: Conc.inst -> w_inst 
  | WSeq: w_inst -> w_inst -> w_inst
  | WFor : Conc.inst -> var -> range -> w_inst -> Conc.inst -> w_inst.

  Fixpoint w_subst x v i :=
    match i with
    | WSync c => WSync (Conc.i_subst x v c)
    | WSeq i1 i2 => WSeq (w_subst x v i1) (w_subst x v i2)
    | WFor c1 y r i2 c2 =>
      let (i2', c2') := if VAR.eq_dec x y
        then (i2, c2)
        else (w_subst x v i2, Conc.i_subst x v c2)
      in
      WFor (Conc.i_subst x v c1) y (r_subst x v r) i2' c2'
    end.


  Lemma w_subst_subst_neq_3:
    forall P x y v1 v2,
    x <> y ->
    ~ NIn y v1 ->
    ~ NIn x v2 ->
    w_subst x v1 (w_subst y v2 P)
    =
    w_subst y v2 (w_subst x v1 P).
  Proof.
    induction P; intros; simpl.
    - rewrite i_subst_subst_neq_3; auto.
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
        rewrite i_subst_subst_neq_3; auto.
        rewrite r_subst_subst_neq_3; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        simpl.
        subst.
        destruct (Set_VAR.MF.eq_dec v v) as [_|?]; try contradiction.
        destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
        rewrite i_subst_subst_neq_3; auto.
        rewrite r_subst_subst_neq_3; auto.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v) as [?|_]; try contradiction.
      destruct (Set_VAR.MF.eq_dec y v) as [?|_]; try contradiction.
      rewrite i_subst_subst_neq_3; auto.
      rewrite i_subst_subst_neq_3 with (c:=i0); auto.
      rewrite r_subst_subst_neq_3; auto.
      rewrite IHP; auto.
  Qed.

  Inductive WRun: w_inst -> vhist -> Prop :=
  | wrun_sync:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    WRun (WSync c) {{ h | [] }}
  | wrun_seq: forall i j mh_i mh_j mh,
    WRun i mh_i ->
    WRun j mh_j ->
    mh_i @ mh_j = mh ->
    WRun (WSeq i j) mh
  | wrun_for_cons:
    forall r r' n h1 h2 m1 m2 m3 c1 x c2 P,
    RStep r n r' ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c2) h2 ->
    WRun (WFor Conc.Skip x r' P c2) m2 ->
    {{ h1 }} @ m1 @ {{ h2 }} @ m2 = m3 ->
    WRun (WFor c1 x r P c2) m3

  | wrun_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall c1 h1 h2 r m m1 n x P c2,
    ROne r n ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) P) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c2) h2 ->
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

  Definition WEq P Q :=
    forall h,
    WRun P h <-> WRun Q h.

  Fixpoint WVar x i :=
    match i with
    | WSync c => Conc.Var x c
    | WSeq i j => WVar x i \/ WVar x j
    | WFor c1 y _ P c2 =>
      x = y \/
      Conc.Var x c1 \/
      WVar x P \/ Conc.Var x c2
    end.

  Lemma wvar_subst_inv_1:
    forall y x n i,
    WVar y (w_subst x (NNum n) i) ->
    WVar y i.
  Proof.
    induction i; simpl; intros; auto.
    - eauto using Conc.var_subst_inv_1.
    - destruct H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); simpl in *. {
        intuition.
        eauto using Conc.var_subst_inv_1.
      }
      intuition.
      + eauto using Conc.var_subst_inv_1.
      + eauto using Conc.var_subst_inv_1.
  Qed.

  Lemma wvar_subst_not_in:
    forall x P y e n,
    NStep e n ->
    ~ WVar x P ->
    ~ WVar x (w_subst y e P).
  Proof.
    (* This one might be a long one, since we would need to prove a similar
       result for Conc, NExp, BExp, and access_exp. *)
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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
    WRun (WFor Conc.Skip x r P c) m ->
    exists m1 h2 n,
    WRun (w_subst x (NNum n) P) m1 /\
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c) h2 /\
    (
    (
      exists m2 r',
      RStep r n r' /\
      WRun (WFor Conc.Skip x r' P c) m2 /\
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
        H: Conc.RunAll _ Conc.Skip _ |- _ =>
        apply Conc.run_all_inv_skip in H; subst; simpl; rewrite v_prefix_nil
      end;
      split; auto;
      split; auto
      .
    left.
    eauto.
  Qed.

  Lemma w_run_inv_for_skip_1:
    forall r P c m x,
    WRun (WFor Conc.Skip x r P c) m ->
    exists n,
    RFirst r n /\
    exists m1,
    WRun (w_subst x (NNum n) P) m1 /\
    exists h2,
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c) h2 /\
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
    WRun (WFor Conc.Skip x r P c) v ->
    RHasNext r.
  Proof.
    intros.
    inversion H; subst; clear H. {
      eauto using r_step_to_has_next.
    }
    eauto using r_one_to_has_next.
  Qed.


  Lemma can_run_subst:
    forall x e e' P,
(* (* These assumptions might be useful *)
    ~ Var TID P ->
    ~ NIn TID e ->
    ~ NIn TID e' ->
    x <> TID ->
    *)
    forall n,
    NStep e n ->
    NStep e' n ->
    CanRun (w_subst x e P) ->
    CanRun (w_subst x e' P).
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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



  Lemma i_first_1:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    List.In a (first v) ->
    IFirst a i.
  Proof.
    intros i v H.
    induction H; intros Hv a Hi; simpl in *.
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
        2: { intros N. intuition. apply wvar_subst_inv_1 in N. intuition.  }
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
        apply IHWRun; auto.
        intros N.
        apply wvar_subst_inv_1 in N.
        intuition.
      }
      subst.
      simpl in *.
      apply wrun_one in H1.
      contradiction.
  Qed.

  Lemma i_first_2:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    IFirst a i ->
    List.In a (first v).
  Proof.
    intros i v H.
    induction H; intros.
    - simpl.
      inversion H1; subst; clear H1.
      inversion H3; subst.
      eapply Conc.run_all_i_in_to_in; eauto.
    - subst.
      inversion H3; subst; clear H3.
      apply IHWRun1 in H4; auto using first_in_seq_l.
      simpl in *.
      auto.
    - subst.
      simpl.
      inversion H6; subst; clear H6. {
        simpl in *.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      simpl in *.
      apply r_step_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply first_in_prefix_r.
      apply IHWRun1 in H12.
      2: { intros N. apply wvar_subst_inv_1 in N. intuition. }
      auto using first_in_seq_l.
    - simpl in *.
      inversion H5; subst; clear H5. {
        simpl.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      apply r_one_to_first in H.
      assert (n0 = n) by eauto using r_first_fun.
      subst.
      apply IHWRun in H12.
      2: { intros N. apply wvar_subst_inv_1 in N. intuition. }
      auto using first_in_seq_l, first_in_prefix_r, first_in_seq_l.
  Qed.

  Lemma i_first_w_subst:
    forall a P x e1 n,
    NStep e1 n ->
    IFirst a (w_subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    x <> TID ->
    IFirst a (w_subst x e2 P).
  Proof.
    (* See i_last_w_subst for an example *)
    (* TODO: PROVE ME PLEASE *)
  Admitted.
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
    (forall e, NStep e n -> CIn a (Conc.i_subst x e c2)) ->
    ILast a (WFor c1 x r P c2)
  .

  Ltac handle_not_var :=
    match goal with
    | [  |- ~ WVar TID (w_subst _ _ _) ]  =>
      let N := fresh in
      intros N; apply wvar_subst_inv_1 in N; intuition
    | [  |- ~ Conc.Var TID (Conc.i_subst _ _ _) ] =>
      let N := fresh in
      intros N; apply Conc.var_subst_inv_1 in N; intuition
    | [ |- ~ WVar TID _ ] => simpl in *; intuition
   end.

  Lemma i_last_w_subst:
    forall a P x e1 n,
    NStep e1 n ->
    ILast a (w_subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    x <> TID ->
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
      + destruct (Set_VAR.MF.eq_dec x v); inversion H2.
    - assert (r1: NEq e1 e2) by eauto using n_eq_def.
      destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
      destruct (Set_VAR.MF.eq_dec x0 v). {
        subst.
        inversion H5; subst; clear H5.
        eapply i_last_for_1; eauto.
        rewrite r1 in *.
        assumption.
      }
      inversion H5; subst; clear H5.
      rename x0 into y.
      rename P0 into Q.
      destruct r0 as (e1', e2').
      simpl in *.
      rewrite r1 in H.
      eapply i_last_for_1 with (n:=n); eauto.
      intros.
      assert (H0 := H0 _ H4).
      assert (H1 := H1 _ H4 y (w_subst v e Q) n0 e1 Hn).
      assert (ILast a (w_subst y e2 (w_subst v e Q))). {
        apply H1; auto.
        rewrite w_subst_subst_neq_3; eauto using n_step_to_not_in.
      }
      rewrite w_subst_subst_neq_3; eauto using n_step_to_not_in.
  - destruct P0; inversion HeqQ; subst; clear HeqQ; simpl.
    rename x0 into y.
    rename v into z.
    assert (r1: NEq e2 e1) by eauto using n_eq_def.
    destruct (Set_VAR.MF.eq_dec y z);
      inversion H4; subst; clear H4. {
      subst.
      eapply i_last_for_2; eauto.
      rewrite r1.
      auto.
    }
    eapply i_last_for_2 with (n:=n); eauto.
    + rewrite r1.
      auto.
    + intros e He.
      assert (~ NIn z e2) by eauto using n_step_to_not_in.
      assert (~ NIn y e) by eauto using n_step_to_not_in.
      assert (~ NIn z e1) by eauto using n_step_to_not_in.
      rewrite Conc.i_subst_subst_neq_3; auto.
      assert (Hi : CIn a (Conc.i_subst z e (Conc.i_subst y e1 i0))) by eauto.
      rewrite Conc.i_subst_subst_neq_3 in Hi; auto.
      eapply c_in_subst with (n2:=n0) (v:=e1); eauto.
  Qed.

  Lemma i_last_1:
    forall i v,
    WRun i v ->
    ~ WVar TID i ->
    forall a,
    List.In a (last v) ->
    ILast a i.
  Proof.
    intros i v H.
    induction H; intros; simpl in *.
    - contradiction.
    - constructor.
      subst.
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
      apply last_inv_in_seq in Hi.
      destruct Hi as [Hi| (h', (?, Hi))]. {
        auto.
      }
      subst.
      apply wrun_one in H0.
      contradiction.
    - subst.
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
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
        2: { intros N. intuition. }
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
      match goal with
        H: List.In _ _ |- _ => rename H into Hi
      end.
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
        assert (CIn a (Conc.i_subst x (NNum n) c2)). {
          eapply c_in_1; eauto.
          handle_not_var.
        }
        intros e He.
        apply c_in_subst with (v:=NNum n) (n0:=n); auto using n_step_num.
      }
      inversion Heq; subst; clear Heq.
      eapply i_last_for_1; eauto using r_one_to_last, n_step_num.
      {
        assert ( ILast a (w_subst x (NNum n) P)). {
          apply IHWRun; auto.
          handle_not_var.
        }
        intros.
        auto.
        apply i_last_w_subst with (e1:=NNum n) (n:=n); eauto using n_step_num.
      }
  Qed.

  Notation any_inst := (Conc.inst + w_inst) % type.

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
    CPairIn p (Conc.i_subst x e c2) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_3:
    forall r e n c1 x p P c2,
    RPick r n ->
    OneOf p (inr (w_subst x e P)) (inl (Conc.i_subst x e c2)) ->
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
    OneOf p (inl (Conc.i_subst x e c2)) (inr (w_subst x e' P)) ->
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
    Conc.RunAll TID_COUNT c1 h ->
    PairIn p h ->
    ~ Conc.Var TID c1 ->
    IPairIn p (WFor c1 r x P c2).
  Proof.
    intros.
    eapply i_pair_in_for_first_1; eauto.
    eapply c_pair_in_1; eauto.
  Qed.

  Lemma i_pair_in_for_run_0_2:
    forall r n c1 P c2 h2 x p,
    RFirst r n ->
    Conc.RunAll TID_COUNT (Conc.i_subst x  (NNum n) c2) h2 ->
    PairIn p h2 ->
    ~ Conc.Var TID (Conc.i_subst x (NNum n) c2) ->
    IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    assert (CPairIn p (Conc.i_subst x (NNum n) c2)). {
      eapply c_pair_in_1; eauto.
    }
    eapply i_pair_in_for_2; eauto using n_step_num.
    auto using r_first_to_pick.
  Qed.

  Lemma i_one_of_1:
    forall i j vi vj,
    WRun i vi ->
    WRun j vj ->
    ~ WVar TID i ->
    ~ WVar TID j ->
    forall p,
    MOneOf p (last vi) (first vj) ->
    OneOf p (inr i) (inr j).
  Proof.
    intros.
    destruct p as (a1, a2).
    unfold MOneOf in *.
    destruct H3 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto; simpl; intuition.
  Qed.

  Lemma i_one_of_2:
    forall c1 P c2 h v r n p x,
    Conc.RunAll TID_COUNT c1 h ->
    RFirst r n ->
    WRun (WFor Conc.Skip x r P c2) v ->
    MOneOf p h (first v) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID (w_subst x (NNum n) P) ->
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
    Conc.RunAll TID_COUNT c h ->
    MOneOf p (last v) h ->
    ~ WVar TID i ->
    ~ Conc.Var TID c ->
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
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun i m1 ->
    MOneOf p h1 (first m1) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID i ->
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
    ~ OneOf p (inl Conc.Skip) P.
  Proof.
    intros (a1, a2) [c|P]; simpl; intros N;
      destruct N as [(N,_)|(N,_)]; apply c_in_skip in N; auto.
  Qed.

  Lemma i_pair_in_for_cons:
    forall r n r' c1 p P c x,
    RStep r n r' ->
    IPairIn p (WFor Conc.Skip x r' P c) ->
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



  Lemma i_pair_in_1:
    forall i h,
    WRun i h ->
    ~ WVar TID i -> 
    forall p,
    VHist.MPairIn p h ->
    IPairIn p i.
  Proof.
    intros i h H.
    induction H; intros Hv p Hi; simpl in *.
    - destruct Hi as [Hi|Hi]. 2: {
        apply par_not_in_nil in Hi.
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
            handle_not_var.
          }
          eapply i_pair_in_for_1; eauto using r_step_to_pick, n_step_num.
        }
        destruct Hi as [Hi|Hi]. {
          apply VHist.m_pair_in_inv_prefix in Hi.
          destruct Hi as [Hi|Hi]. {
            assert (Hc := H2).
            eapply c_pair_in_1 in Hc; eauto.
            2: { handle_not_var. }
            simpl in *.
            eapply i_pair_in_for_run_0_2; eauto using r_step_to_first.
            handle_not_var.
          }
          destruct Hi as [Hi|Hi]. {
            apply IHWRun2 in Hi.
            2: { intuition. }
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
          eapply i_one_of_2 in Hi; eauto; try handle_not_var.
          apply r_first_to_has_next in Hr.
          eapply i_pair_in_for_mid_1 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        }
        apply m_one_of_inv_first_prefix_l in Hi.
        destruct Hi as [Hi|Hi]. {
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_step_to_pick.
        }
        assert (OneOf p (inr (w_subst x (NNum n) P)) (inr (w_subst x (NNum (S n)) P))). {
          apply w_run_inv_for_skip_1 in H3.
          destruct H3 as (n_b, (Hf, (m_b, (Hr, (h2', (Hrr, (m3', Hx))))))).
          assert (n_b = S n) by eauto using r_step_inv_next_eq.
          subst.
          apply m_one_of_inv_first_seq_l in Hi.
          eapply i_one_of_1 in Hi; eauto; try handle_not_var.
          eauto using wrun_has_many.
        }
        eapply i_pair_in_for_mid_2 with (n:=n); eauto using r_step_to_pick2, n_step_num.
        eapply r_step_to_pick2; eauto using wrun_for_inv_has_next.
      }
      apply m_one_of_inv_first_seq_l in Hi. 2: { eauto using wrun_has_many. }
      eapply i_one_of_4 in Hi; eauto; try handle_not_var.
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
          apply IHWRun in Hi; try handle_not_var.
          eapply i_pair_in_for_1; eauto using r_one_to_pick, n_step_num.
        * simpl in *.
          (* c2 *)
          eapply i_pair_in_for_2; eauto using r_one_to_pick, n_step_num.
          eapply c_pair_in_1; eauto; try handle_not_var.
        * simpl in *.
          (* c2 / w_subst x (NNum n) i *)
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          eapply i_pair_in_for_3 with (n:=n); eauto using r_one_to_pick.
      + (* c1 / w_subst x (NNum n) i *)
        apply m_one_of_inv_first_seq_l in Hi.
        2: { eauto using wrun_has_many. }
        eapply i_one_of_4 in Hi; eauto; try handle_not_var.
        eapply i_pair_in_for_first_2; eauto using r_one_to_first, n_step_num.
  Qed.


End Defs. 