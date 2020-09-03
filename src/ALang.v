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

Require RangeList.
Require Import Lia.

Import ListNotations.
Require Conc.
Require Import NSync.

Section Defs.

  Notation history := (list access_val).

  Notation mhistory := (list history).

  Notation histpair := (mhistory * history) % type.

  Context `{T:Tasks}.
  Context {A:Access}.

  Open Scope vhist_scope.

(* -------------------- RUN --------------------------- *)


  Inductive inst :=
  | Sync
  | Block: Conc.inst -> inst
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst.

  Fixpoint i_subst x v i :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
    | For y r i2 =>
      let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
      For y (r_subst x v r) i2'
    end.

  Inductive Run: inst -> vhist -> Prop :=
  | run_sync:
    Run Sync {{ [] | [] }}
  | run_block:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) {{ h }}
  | run_seq: forall i j mh_i mh_j mh,
    Run i mh_i ->
    Run j mh_j ->
    mh_i @ mh_j = mh ->
    Run (Seq i j) mh
  | run_for_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) m1 ->
    Run (For x (NNum (S n1), NNum n2) i) m2 ->
    m1 @ m2 = m3 ->
    Run (For x (e1, e2) i) m3
  | run_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall x i e1 e2 m n,
    NStep e1 n ->
    NStep e2 (S n) ->
    Run (i_subst x (NNum n) i) m ->
    Run (For x (e1, e2) i) m.


  Goal Run Sync {{ [] | [] }}.
  Proof.
    apply run_sync.
  Qed.

  Goal Run (Seq Sync Sync) {{ [] | [] | [] }}.
  Proof.
    eapply run_seq.
    + apply run_sync.
    + apply run_sync.
    + reflexivity.
  Qed.

  Goal Run (Seq (Seq Sync Sync) Sync) {{ [] | [] | [] | [] }}.
  Proof.
    eapply run_seq.
    - eapply run_seq.
      + apply run_sync.
      + apply run_sync.
      + reflexivity.
    - apply run_sync.
    - reflexivity.
  Qed.

(* ------------------------------ VAR -------------------------- *)

  Fixpoint Var x i :=
    match i with
    | Sync => False
    | Block c => Conc.Var x c
    | Seq i j => Var x i \/ Var x j
    | For y _ i => x = y \/ Var x i
    end.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto.
    - eauto using Conc.var_subst_inv_1.
    - destruct H; auto.
    - destruct H; auto.
      destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

(* ------------------------------- NOSYNC ------------------------ *)

  Fixpoint unsynced (i:inst) : bool :=
    match i with
    | Sync => false
    | Block _ => true
    | Seq i j => unsynced i && unsynced j
    | For _ _ i => unsynced i
    end.

  Definition synced (i:inst) : bool := negb (unsynced i).

  Lemma unsynced_subst:
    forall i x v,
    unsynced (i_subst x v i) = unsynced i.
  Proof.
    induction i; intros; simpl in *; auto.
    - rewrite IHi1 with (x:=x) (v:=v); auto.
      rewrite IHi2 with (x:=x) (v:=v); auto.
    - assert (IHi := IHi x v0).
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      assumption.
  Qed.

  Inductive w_inst :=
  | WSync: Conc.inst -> w_inst 
  | WSeq: w_inst -> w_inst -> w_inst
  | WFor : Conc.inst -> var -> range -> w_inst -> Conc.inst -> w_inst.

  Fixpoint seq (c: Conc.inst) (i:w_inst) : w_inst :=
    match i with
    | WSync c' => WSync (Conc.Seq c c')
    | WSeq i j => WSeq (seq c i) j
    | WFor c1 x r i c2 => WFor (Conc.Seq c c1) x r i c2
    end.

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

  Fixpoint w_to_i (i:w_inst) : inst :=
    match i with
    | WSync c => Seq (Block c) Sync
    | WSeq i j => Seq (w_to_i i) (w_to_i j)
    | WFor c1 x r i c2 =>
      Seq (Block c1) (For x r (Seq (w_to_i i) (Block c2)))
    end.

  Inductive CIn : access_val -> Conc.inst -> Prop :=
  | c_in_def:
    forall a c,
    access_tid a < TID_COUNT ->
    Conc.IIn a c ->
    CIn a c.

  Lemma c_in_1:
    forall c h a,
    ~ Conc.Var TID c ->
    Conc.RunAll TID_COUNT c h ->
    List.In a h ->
    CIn a c.
  Proof.
    intros c h a Hv Hr Hi.
      eauto using c_in_def, Conc.run_all_inv_in_eq, Conc.run_all_to_i_in.
  Qed.

  Lemma c_in_2:
    forall c h a,
    ~ Conc.Var TID c ->
    Conc.RunAll TID_COUNT c h ->
    CIn a c ->
    List.In a h.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eapply Conc.run_all_i_in_to_in; eauto.
  Qed.



  Inductive CPairIn : (access_val * access_val) -> Conc.inst -> Prop :=
  | c_pair_in_def:
    forall a1 a2 c,
    CIn a1 c ->
    CIn a2 c ->
    CPairIn (a1, a2) c.

  Lemma c_pair_in_def_2:
    forall c h p,
    ~ Conc.Var TID c ->
    Conc.RunAll TID_COUNT c h ->
    PairIn p h ->
    CPairIn p c.
  Proof.
    intros c h (a1, a2) Hv Hr Hi.
    inversion Hi; subst; clear Hi.
    eauto using c_pair_in_def, c_in_1.
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
    forall e1 e2 n1 n2 i x h1 h2 m1 m2 m3 c1 c2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n1) i) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n1) c2) h2 ->
    WRun (WFor Conc.Skip x (NNum (S n1), NNum n2) i c2) m2 ->
    {{ h1 }} @ m1 @ {{ h2 }} @ m2 = m3 ->
    WRun (WFor c1 x (e1, e2) i c2) m3
  | wrun_for_eq:
    (* We note that the loops must run at least once. This is
       a constraint of our programming model. *)
    forall x i c1 c2 h1 h2 e1 e2 m m1 n,
    NStep e1 n ->
    NStep e2 (S n) ->
    Conc.RunAll TID_COUNT c1 h1 ->
    WRun (w_subst x (NNum n) i) m1 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n) c2) h2 ->
    {{ h1 }} @ m1 @ {{ h2 }} = m ->
    WRun (WFor c1 x (e1, e2) i c2) m.


  Fixpoint WVar x i :=
    match i with
    | WSync c => Conc.Var x c
    | WSeq i j => WVar x i \/ WVar x j
    | WFor c1 y _ i c2 =>
      x = y \/
      Conc.Var x c1 \/
      WVar x i \/
      Conc.Var x c2
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


  Lemma w_run_inv_for_skip:
    forall x n1 n2 i c m,
    WRun (WFor Conc.Skip x (NNum n1, NNum n2) i c) m ->
    exists m1 h2,
    WRun (w_subst x (NNum n1) i) m1 /\
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n1) c) h2 /\
    (
    (
      exists m2,
      n1 < S n2 /\
      WRun (WFor Conc.Skip x (NNum (S n1), NNum n2) i c) m2 /\
      m = m1 @ {{ h2 }} @ m2
    )
    \/
    (n2 = S n1 /\ m = m1 @ {{ h2 }})
    ).
  Proof.
    intros.
    inversion H; subst; clear H. {
      assert (n0 = n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      apply Conc.run_all_inv_skip in H10.
      subst.
      exists m1.
      exists h2.
      split; auto.
      split; auto.
      left.
      exists m2.
      split; auto.
      split; auto.
      simpl.
      rewrite v_prefix_nil.
      reflexivity.
    }
    apply Conc.run_all_inv_skip in H9.
    subst.
    exists m1.
    exists h2.
    assert (n = n1) by eauto using n_step_num, n_step_fun.
    assert (S n = n2) by eauto using n_step_num, n_step_fun.
    subst.
    intuition.
    right.
    simpl.
    rewrite v_prefix_nil.
    auto.
  Qed.


  Lemma w_run_inv_for_skip_1:
    forall x n1 n2 i c m,
    WRun (WFor Conc.Skip x (NNum n1, NNum n2) i c) m ->
    exists m1 h2 m2,
    WRun (w_subst x (NNum n1) i) m1 /\
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n1) c) h2 /\
    m = m1 @ {{ h2 }} @ m2.
  Proof.
    intros.
    apply w_run_inv_for_skip in H.
    destruct H as (m1, (h2, (Hr, (Hr2, Hx)))).
    exists m1, h2.
    destruct Hx as [(m2, (?, (?,?)))|(Hx,?)]. {
      exists m2.
      auto.
    }
    subst.
    exists {{ [] }}.
    rewrite v_seq_one_nil_r.
    auto.
  Qed.

  Lemma wrun_for_inv_end:
    forall e x i c v,
    ~ WRun (WFor Conc.Skip x (e, e) i c) v.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N. {
      assert (n1 = n2) by eauto using n_step_fun.
      subst.
      lia.
    }
    assert (n = S n) by eauto using n_step_fun.
    lia.
  Qed.

  Lemma c_in_skip:
    forall a,
    ~ CIn a Conc.Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    inversion H0; subst; clear H0.
  Qed.


  (* --------------------------- GET FIRST ----------------------- *)

  Inductive GetFirst: w_inst -> Conc.inst -> Prop :=
  | get_first_sync:
    forall c,
    GetFirst (WSync c) c
  | get_first_seq:
    forall i j c,
    GetFirst i c ->
    GetFirst (WSeq i j) c
  | get_first_for_1:
    forall r c1 x i c2,
    GetFirst (WFor c1 x r i c2) c1
  | get_first_for_2:
    forall e1 e2 n1 n2 c1 x i c2 c,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetFirst (w_subst x (NNum n1) i) c ->
    GetFirst (WFor c1 x (e1, e2) i c2) c
  .

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
    forall r c1 x i c2,
    CIn a c1 ->
    IFirst a (WFor c1 x r i c2)
  | i_first_for_2:
    forall e1 e2 n1 n2 c1 x i c2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    IFirst a (w_subst x (NNum n1) i) ->
    IFirst a (WFor c1 x (e1, e2) i c2).

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
        2: { intros N. apply wvar_subst_inv_1 in N. intuition. }
        eapply i_first_for_2; eauto.
      }
      subst.
      apply wrun_one in H3.
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
        eapply i_first_for_2; eauto.
        apply IHWRun; auto.
        intros N.
        apply wvar_subst_inv_1 in N.
        auto.
      }
      subst.
      simpl in *.
      apply wrun_one in H2.
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
      inversion H8; subst; clear H8. {
        simpl in *.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      simpl in *.
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      apply first_in_prefix_r.
      apply IHWRun1 in H17.
      2: { intros N. apply wvar_subst_inv_1 in N. auto. }
      auto using first_in_seq_l.
    - simpl in *.
      inversion H6; subst; clear H6. {
        simpl.
        apply first_in_prefix_l.
        eapply c_in_2; eauto.
      }
      assert (n1 = n) by eauto using n_step_fun.
      assert (n2 = S n) by eauto using n_step_fun.
      subst.
      apply IHWRun in H16.
      2: { intros N. apply wvar_subst_inv_1 in N. auto. }
      auto using first_in_seq_l, first_in_prefix_r, first_in_seq_l.
  Qed.

  Lemma i_first_to_get_first:
    forall a i,
    IFirst a i ->
    exists c, GetFirst i c /\ CIn a c.
  Proof.
    intros a i H.
    induction H; intros.
    - eauto using get_first_sync.
    - destruct IHIFirst as (c, (Hg, Hc)).
      eauto using get_first_seq.
    - eauto using get_first_for_1.
    - destruct IHIFirst as (c, (Hg, Hc)).
      eauto using get_first_for_2.
  Qed.

  (* ------------------ ILAST --------------------------------------- *)

  Inductive GetLast : w_inst -> Conc.inst -> Prop :=
  | get_last_sync:
    forall c,
    GetLast (WSync c) Conc.Skip
  | get_last_seq:
    forall i j c,
    GetLast j c ->
    GetLast (WSeq i j) c
  | get_last_for_1:
    forall e1 e2 n1 n2 c1 x i c2 c,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetLast (w_subst x (NNum (n2 - 1)) i) c ->
    GetLast (WFor c1 x (e1, e2) i c2) c
  | get_last_for_2:
    forall e1 e2 n1 n2 c1 x i c2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetLast (WFor c1 x (e1, e2) i c2) (Conc.i_subst x (NNum (n2 - 1)) c2).

  Inductive ILast (a: access_val) : w_inst -> Prop :=
  | i_last_seq:
    forall i j,
    ILast a j ->
    ILast a (WSeq i j)
  | i_last_for_1:
    forall e1 e2 n1 n2 c1 x i c2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    ILast a (w_subst x (NNum (n2 - 1)) i) ->
    ILast a (WFor c1 x (e1, e2) i c2)
  | i_last_for_2:
    forall e1 e2 n1 n2 c1 x i c2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    CIn a (Conc.i_subst x (NNum (n2 - 1)) c2) ->
    ILast a (WFor c1 x (e1, e2) i c2)
  .

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
          apply wrun_one in H5.
          contradiction.
        }
        apply IHWRun2 in Hi.
        2: { intros N. intuition. }
        inversion Hi; subst; clear Hi.
        - assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
          assert (n3 = n2) by eauto using n_step_fun, n_step_num.
          subst.
          assert (Hx: exists n2', n2 = S n2'). {
            destruct n2. { lia. }
            eauto.
          }
          destruct Hx as (n2', Hx).
          subst.
          rename n2' into n2.
          eapply i_last_for_1; eauto.
        - assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
          assert (n3 = n2) by eauto using n_step_fun, n_step_num.
          subst.
          eapply i_last_for_2; eauto.
      }
      symmetry in Heq.
      apply v_prefix_inv_one in Heq.
      destruct Heq as (h'', ?).
      subst.
      apply wrun_one in H5.
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
        apply wrun_one in H2.
        contradiction.
      }
      apply last_inv_in_seq in Hi.
      simpl in *.
      destruct Hi as [Hi|(h', (Heq, Hi))]. {
        eapply i_last_for_2; eauto.
        assert (R: S n - 1 = n) by lia.
        rewrite R in *.
        eapply c_in_1; eauto.
        intros N.
        apply Conc.var_subst_inv_1 in N.
        auto.
      }
      inversion Heq; subst; clear Heq.
      eapply i_last_for_1; eauto.
      assert (R: S n - 1 = n) by lia.
      rewrite R in *.
      apply IHWRun; auto.
      intros N.
      apply wvar_subst_inv_1 in N.
      auto.
  Qed.

  Lemma i_last_to_get_last:
    forall a i,
    ILast a i ->
    exists c, GetLast i c /\ CIn a c.
  Proof.
    intros a i H.
    induction H; intros.
    - destruct IHILast as (c, (Hg, Hc)).
      eauto using get_last_seq.
    - destruct IHILast as (c, (Hg, Hc)).
      eauto using get_last_for_1.
    - eauto using get_last_for_2.
  Qed.

  Definition AnyOf (a:access_val) P Q :Prop :=
    P a \/ Q a.

  Definition AnyPairOf (p:access_val * access_val) P Q :=
    match p with
    | (a1, a2) => AnyOf a1 P Q /\ AnyOf a2 P Q
    end.

  (* ------------------------- ONE OF ------------------------------ *)

  Definition OneOf (p:access_val*access_val) P Q :=
    let (a1,a2) := p in
    (P a1 /\ Q a2) \/
    (P a2 /\ Q a1).

  Definition IOneOf (p:access_val*access_val) c1 c2 :=
    let (a1,a2) := p in
    (CIn a1 c1 /\ CIn a2 c2) \/
    (CIn a1 c2 /\ CIn a2 c1).

  Definition IPairInAux p c i :=
    CPairIn p c \/
    OneOf p (fun a => CIn a c)
            (fun a => IFirst a i).

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
    forall p i j c1 c2,
    GetLast i c1 ->
    GetFirst j c2 ->
    IOneOf p c1 c2 ->
    IPairIn p (WSeq i j)
  | i_pair_in_for_first_1:
    forall r i x c1 c2 p,
    CPairIn p c1 ->
    IPairIn p (WFor c1 x r i c2)
  | i_pair_in_for_first_2:
    forall e1 e2 n1 n2 i x c1 c2 c3 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetFirst (w_subst x (NNum n1) i) c3 ->
    IOneOf p c1 c3 ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_first_3:
    forall e1 e2 n1 n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    IPairIn p (w_subst x (NNum n1) i) ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_mid_1:
    forall e1 e2 n1 n n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n < n2 ->
    CPairIn p (Conc.i_subst x (NNum (n - 1)) c2) ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_mid_2:
    forall e1 e2 n1 n n2 i x c1 c2 c3 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n < n2 ->
    GetFirst (w_subst x (NNum n) i) c3 ->
    IOneOf p (Conc.i_subst x (NNum (n - 1)) c2) c3 ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_mid_3:
    forall e1 e2 n1 n n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n < n2 ->
    IPairIn p (w_subst x (NNum n) i) ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_last_1:
    forall e1 e2 n1 n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    CPairIn p (Conc.i_subst x (NNum (n2 - 1)) c2) ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_last_2:
    forall e1 e2 n1 n2 i x c1 c2 c3 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetLast (w_subst x (NNum (n2 - 1)) i) c3 ->
    CPairIn p c3 ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  | i_pair_in_for_last_3:
    forall e1 e2 n1 n2 i x c1 c2 c3 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    GetLast (w_subst x (NNum (n2 - 1)) i) c3 ->
    IOneOf p
      (Conc.i_subst x (NNum (n2 - 1)) c2)
      c3 ->
    IPairIn p (WFor c1 x (e1, e2) i c2)
  .

(*
  Lemma i_pair_in_seq_1:
    forall p i,
    IPairIn p i ->
    forall c,
    CPairIn p c ->
    IPairIn p (seq c i).
  Proof.
    intros p i H.
    induction H; intros; simpl.
    -  
  Qed.
*)
(*

  Lemma m_one_of_to_i_one_of:
    forall p i j mh_i mh_j,
    WRun i mh_i ->
    WRun j mh_j ->
    ~ WVar TID i -> 
    ~ WVar TID j -> 
    MOneOf p (last mh_i) (first mh_j) ->
    IOneOf p (fun a => ILast a i)
            (fun a => IFirst a j).
  Proof.
    intros.
    unfold MOneOf, OneOf in *.
    destruct p as (a1, a2).
    destruct H3 as [(Hi,Hj)|(Hi,Hj)]. {
      left.
      split. {
        eapply i_last_1; eauto.
      }
      eapply i_first_1; eauto.
    }
    right.
    split. {
      eapply i_last_1; eauto.
    }
    eapply i_first_1; eauto.
  Qed.
*)
  Lemma i_pair_in_for_run_0_1:
    forall e1 n1 e2 n2 c2 i x c1 p h,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Conc.RunAll TID_COUNT c1 h ->
    PairIn p h ->
    ~ Conc.Var TID c1 ->
    IPairIn p (WFor c1 x (e1, e2) i c2).
  Proof.
    intros.
    eapply i_pair_in_for_first_1; eauto.
    eapply c_pair_in_def_2; eauto.
  Qed.
(*
  Lemma c_pair_in_to_any_pair_of:
    forall p c i,
    CPairIn p c ->
    AnyPairOf p
      (fun a => CIn a c)
      (fun a => ILast a i).
  Proof.
    intros.
    unfold AnyPairOf.
    destruct p as (a1, a2).
    inversion H; subst; clear H.
    unfold AnyOf.
    intuition.
  Qed.*)

  Lemma i_pair_in_for_run_0_2:
    forall e1 e2 n1 n2 c1 c2 i x h2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Conc.RunAll TID_COUNT (Conc.i_subst x (NNum n1) c2) h2 ->
    PairIn p h2 ->
    ~ Conc.Var TID c2 ->
    IPairIn p (WFor c1 x (e1, e2) i c2).
  Proof.
    intros.
    assert (R: S n1 - 1 = n1) by lia.
    match goal with
      H: _ < _ |- _ => rename H into Hlt
    end.
    assert (CPairIn p (Conc.i_subst x (NNum n1) c2)). {
      eapply c_pair_in_def_2; eauto.
      intros N.
      apply Conc.var_subst_inv_1 in N.
      auto.
    }
    inversion Hlt; subst; clear Hlt. {
      eapply i_pair_in_for_last_1; eauto.
      rewrite R.
      assumption.
    }
    eapply i_pair_in_for_mid_1 with (n:=S n1); eauto.
    { lia. }
    rewrite R.
    assumption.
  Qed.

  Lemma i_one_of_1:
    forall i j vi vj,
    WRun i vi ->
    WRun j vj ->
    ~ WVar TID i ->
    ~ WVar TID j ->
    forall p,
    MOneOf p (last vi) (first vj) ->
    exists c1 c2,
    GetLast i c1 /\
    GetFirst j c2 /\
    IOneOf p c1 c2.
  Proof.
    intros.
    destruct p as (a1, a2).
    unfold MOneOf in *.
    destruct H3 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto;
      apply i_last_to_get_last in Hi;
      destruct Hi as (ci, (Hgi, Hci));
      eapply i_first_1 in Hj; eauto;
      apply i_first_to_get_first in Hj;
      destruct Hj as (cj, (Hgj, Hcj)); unfold IOneOf;
      exists ci, cj; auto.
  Qed.

  Lemma i_one_of_2:
    forall c1 c2 i h v n1 n2 x p,
    Conc.RunAll TID_COUNT c1 h ->
    WRun (WFor Conc.Skip x (NNum (S n1), NNum (S n2)) i c2) v ->
    MOneOf p h (first v) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID i ->
    exists c,
    GetFirst (w_subst x (NNum (S n1)) i) c /\
    IOneOf p c1 c.
  Proof.
    intros.
    apply w_run_inv_for_skip_1 in H0.
    destruct H0 as (m1, (h2, (m2, (Hr1, (Hr2, Heq))))).
    subst.
    simpl in *.
    destruct m1 as [h'|h' m1]. {
      simpl in *.
      apply wrun_one in Hr1.
      contradiction.
    }
    destruct p as (a1, a2).
    destruct H1 as [(Ha,Hb)|(Ha,Hb)]; eapply c_in_1 in Ha; eauto. {
      apply first_inv_in_seq in Hb.
      destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
        eapply i_first_1 in Hb; eauto. 2: {
          intros N. apply wvar_subst_inv_1 in N. intuition.
        }
        apply i_first_to_get_first in Hb.
        destruct Hb as (c', (Hg, Hci)).
        exists c'.
        split; auto.
        unfold IOneOf; auto.
      }
      inversion Hb1.
    }
    apply first_inv_in_seq in Hb.
    destruct Hb as [Hb|(h'', (Hb1, Hb2))]. {
      eapply i_first_1 in Hb; eauto. 2: {
        intros N. apply wvar_subst_inv_1 in N. intuition.
      }
      apply i_first_to_get_first in Hb.
      destruct Hb as (c', (Hg, Hci)).
      exists c'.
      split; auto.
      unfold IOneOf; auto.
    }
    inversion Hb1.
  Qed.

  Lemma c_pair_in_skip:
    forall p,
    ~ CPairIn p Conc.Skip.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    apply c_in_skip in H.
    contradiction.
  Qed.

  Lemma i_one_of_skip_l:
    forall p c,
    ~ IOneOf p Conc.Skip c.
  Proof.
    intros (a1, a2) c [(N,_)|(_, N)];
      apply c_in_skip in N; auto.
  Qed.

  Lemma i_pair_in_for_cons:
    forall e1 e2 n1 n2 x i c2 c1 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    IPairIn p (WFor Conc.Skip x (NNum (S n1), NNum n2) i c2) ->
    IPairIn p (WFor c1 x (e1, e2) i c2).
  Proof.
    intros.
    inversion H2; subst; clear H2.
    - apply c_pair_in_skip in H5.
      contradiction.
    - apply i_one_of_skip_l in H14.
      contradiction.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_mid_3; eauto.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_mid_1 with (n:=n); eauto.
      lia.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_mid_2 with (n:=n); eauto.
      lia.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_mid_3 with (n:=n); eauto.
      lia.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_last_1; eauto.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_last_2; eauto.
    - assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
      assert (n3 = n2) by eauto using n_step_num, n_step_fun.
      subst.
      eapply i_pair_in_for_last_3; eauto.
  Qed.

  Lemma run_1:
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
      eauto using i_pair_in_sync, c_pair_in_def_2.
    - subst.
      apply VHist.m_pair_in_inv_seq in Hi.
      intuition.
      + auto using i_pair_in_seq_l.
      + auto using i_pair_in_seq_r.
      + eapply i_one_of_1 in H2; eauto.
        destruct H2 as (c1, (c2, (Hg1, (Hg2, Hi)))).
        eapply i_pair_in_seq_both; eauto.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|Hi]. {
        assert (CPairIn p c1). {
          eapply c_pair_in_def_2; eauto.
        }
        auto using i_pair_in_for_first_1.
      }
      destruct Hi as [Hi|Hi]. {
        apply VHist.m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|Hi]. {
          assert (IPairIn p (w_subst x (NNum n1) i)). {
            apply IHWRun1; auto.
            simpl.
            intros N.
            apply wvar_subst_inv_1 in N.
            auto.
          }
          eauto using i_pair_in_for_first_3.
        }
        destruct Hi as [Hi|Hi]. {
          apply VHist.m_pair_in_inv_prefix in Hi.
          destruct Hi as [Hi|Hi]. {
            eapply i_pair_in_for_run_0_2; eauto.
            intuition.
          }
          destruct Hi as [Hi|Hi]. {
            apply IHWRun2 in Hi.
            2: {
              intros N. contradict Hv. destruct N as [?|[N|?]]; auto; try contradiction. 
            }
            eapply i_pair_in_for_cons; eauto.
          }
          (* are we mid or are we last? *)
          inversion H1; subst; clear H1. {
            (* last *)
            apply wrun_for_inv_end in H5.
            contradiction.
          }
          (* mid *)
          eapply i_one_of_2 in Hi; eauto.
          3: { intuition. }
          2: { intros N. apply Conc.var_subst_inv_1 in N. intuition. }
          destruct Hi as (c, (Hg, Hi)).
          eapply i_pair_in_for_mid_2 with (n:=S n1); eauto.
          { lia. }
          assert (R: S n1 - 1 = n1) by lia.
          rewrite R.
          clear R.
          assumption.
        }
        admit.
      }
      admit.
    - subst.
      apply m_pair_in_inv_prefix in Hi.
      destruct Hi as [Hi|[Hi|Hi]].
      + (* c1 *)
        admit.
      + apply m_pair_in_inv_seq in Hi.
        destruct Hi as [Hi|[Hi|Hi]].
        * (* w_subst x (NNum n) i *)
          admit.
        * simpl in *.
          (* c2 *)
          admit.
        * simpl in *.
          (* c2 / w_subst x (NNum n) i *)
          admit.
      + (* c1 / w_subst x (NNum n) i *)
        admit.
  Admitted.

(* ------------------------------ PHASE -------------------------- *)
  (* Count how many phases this instruction yields. *)

  Inductive Phase : inst -> nat -> Prop :=
  | phase_block:
    forall c,
    Phase (Block c) 0
  | phase_sync:
    Phase Sync 1
  | phase_seq:
    forall i j n m o,
    Phase i n ->
    Phase j m ->
    o = n + m ->
    Phase (Seq i j) o
  | phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    Phase (For x (NNum (S n1), e2) i) m ->
    n + m = o ->
    Phase (For x (e1, e2) i) o
  | phase_for_eq:
    forall i x e1 e2 n m,
    NStep e1 n ->
    NStep e2 (S n) ->
    Phase (i_subst x (NNum n) i) m ->
    Phase (For x (e1, e2) i) m
  .

  Lemma phase_inv_unsynced:
    forall i n,
    Phase i n ->
    unsynced i = true ->
    n = 0.
  Proof.
    intros i n H.
    induction H; intros; simpl in *.
    - reflexivity.
    - inversion H.
    - apply Bool.andb_true_iff in H2.
      destruct H2 as (Ha, Hb).
      rewrite IHPhase1 in H1; auto.
      rewrite IHPhase2 in H1; auto.
    - rewrite IHPhase2 in H4; clear IHPhase2; auto.
      rewrite IHPhase1 in H4; auto.
      rewrite unsynced_subst.
      assumption.
    - rewrite IHPhase; auto.
      rewrite unsynced_subst.
      assumption.
  Qed.

  Lemma phase_to_unsynced:
    forall i,
    Phase i 0 ->
    unsynced i = true.
  Proof.
    intros i H.
    remember 0.
    generalize dependent Heqn.
    induction H; intros; simpl; auto.
    - inversion Heqn.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      rewrite Bool.andb_true_iff.
      auto.
    - subst.
      assert (n = 0) by lia.
      assert (m = 0) by lia.
      subst.
      simpl in *.
      rewrite <- unsynced_subst with (x:=x) (v:=NNum n1); auto.
    - rewrite <- unsynced_subst with (x:=x) (v:=NNum n); auto.
  Qed.

(* ------------------------ IN PHASE ------------------------------ *)

  Inductive InPhase (a:access_val) : nat -> inst -> Prop :=
  | in_phase_block:
    forall c,
    Conc.IIn a c ->
    InPhase a 0 (Block c)
  | in_phase_seq_l:
    forall i j n,
    InPhase a n i ->
    InPhase a n (Seq i j)
  | in_phase_seq_r:
    forall i j n m o,
    Phase i n ->
    InPhase a m j ->
    o = n + m ->
    InPhase a o (Seq i j)
  | in_phase_for_eq:
    forall i x e1 e2 n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    InPhase a n (i_subst x (NNum n1) i) ->
    InPhase a n (For x (NNum (S n1), e2) i)
  | in_phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    InPhase a m (For x (NNum (S n1), e2) i) ->
    o = n + m ->
    InPhase a o (For x (e1, e2) i).

(* -------------------------------- IIN/ IPAIRIN ---------------------- *)
(*
  Definition IIn a i : Prop := exists n, InPhase a n i.

  Definition IPairIn (p:access_val * access_val) i : Prop :=
    let (a1, a2) := p in
    exists n, InPhase a1 n i /\ InPhase a2 n i.
*)

End Defs.