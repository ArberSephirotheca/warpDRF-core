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


  Inductive w_inst :=
  | WSync: Conc.inst -> w_inst 
  | WSeq: w_inst -> w_inst -> w_inst
  | WFor : Conc.inst -> var -> range -> w_inst -> Conc.inst -> w_inst.
(*
  Fixpoint seq (c: Conc.inst) (i:w_inst) : w_inst :=
    match i with
    | WSync c' => WSync (Conc.Seq c c')
    | WSeq i j => WSeq (seq c i) j
    | WFor c1 x r i c2 => WFor (Conc.Seq c c1) x r i c2
    end.
*)
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

(*
  Fixpoint w_to_i (i:w_inst) : inst :=
    match i with
    | WSync c => Seq (Block c) Sync
    | WSeq i j => Seq (w_to_i i) (w_to_i j)
    | WFor c1 x r i c2 =>
      Seq (Block c1) (For x r (Seq (w_to_i i) (Block c2)))
    end.
*)

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

(*
  Inductive Wellformed: w_inst -> Prop :=
  | wellformed_sync:
    forall c,
    Wellformed (WSync c)
  | wellformed_seq:
    forall i j,
    Wellformed i -> 
    Wellformed j ->
    Wellformed (WSeq i j)
  | wellformed_for_1:
    forall c1 c2 x r r' n i,
    RStep r n r' ->
    Wellformed (w_subst x (NNum n) i) ->
    Wellformed (WFor Conc.Skip x r' i c2) -> 
    Wellformed (WFor c1 x r i c2)
  | wellformed_for_2:
    forall c1 c2 x r n i,
    ROne r n ->
    Wellformed (w_subst x (NNum n) i) ->
    Wellformed (WFor c1 x r i c2).

  Lemma wrun_to_wellformed:
    forall i v,
    WRun i v ->
    Wellformed i.
  Proof.
    intros.
    induction H; try (constructor; auto).
    - subst.
      eapply wellformed_for_1; eauto.
    - eapply wellformed_for_2; eauto.
  Qed.
*)
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
    forall r c1 P c2 x,
    GetFirst (WFor c1 x r P c2) c1
  | get_first_for_2:
    forall r n c1 x P c2 c,
    RFirst r n ->
    GetFirst (w_subst x (NNum n) P) c ->
    GetFirst (WFor c1 x r P c2) c
  .

  Lemma get_first_inv_for_skip:
    forall r P c1 c x,
    GetFirst (WFor Conc.Skip x r P c1) c ->
    c = Conc.Skip \/ exists n, RFirst r n /\ GetFirst (w_subst x (NNum n) P) c.
  Proof.
    intros.
    inversion H; subst; clear H; eauto.
  Qed.

  (* ------------------ IFIRST --------------------------------------- *)
(*
  Fixpoint i_seq (c:Conc.inst) (i:w_inst) :=
    match i with
    | WSync c' => WSync (Conc.Seq c c')
    | WSeq i j => WSeq (i_seq c i) j
    | WFor c1 x r i c2 => WFor (Conc.Seq c c1) x r i c2
    end.
*)
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
    forall r n c1 x P c2 c,
    RLast r n ->
    GetLast (w_subst x (NNum n) P) c ->
    GetLast (WFor c1 x r P c2) c
  | get_last_for_2:
    forall r n c1 x P c2,
    RLast r n ->
    GetLast (WFor c1 x r P c2) (Conc.i_subst x (NNum n) c2).

  Inductive ILast (a: access_val) : w_inst -> Prop :=
  | i_last_seq:
    forall i j,
    ILast a j ->
    ILast a (WSeq i j)
  | i_last_for_1:
    forall r n c1 P c2 x,
    RLast r n ->
    ILast a (w_subst x (NNum n) P) ->
    ILast a (WFor c1 x r P c2)
  | i_last_for_2:
    forall r n c1 P c2 x,
    RLast r n ->
    CIn a (Conc.i_subst x (NNum n) c2) ->
    ILast a (WFor c1 x r P c2)
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
        eapply i_last_for_2; eauto using r_one_to_last.
        eapply c_in_1; eauto.
        intros N.
        apply Conc.var_subst_inv_1 in N.
        intuition.
      }
      inversion Heq; subst; clear Heq.
      eapply i_last_for_1; eauto using r_one_to_last.
      apply IHWRun; auto.
      intros N.
      apply wvar_subst_inv_1 in N.
      intuition.
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

  Definition IOneOf (p:access_val*access_val) c1 c2 :=
    let (a1,a2) := p in
    (CIn a1 c1 /\ CIn a2 c2) \/
    (CIn a1 c2 /\ CIn a2 c1).

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
  (* Any iteration *)
  | i_pair_in_for_1:
    forall r n c1 P c2 p x,
    RPick r n ->
    IPairIn p (w_subst x (NNum n) P) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_2:
    forall r n c1 p P x c2,
    RPick r n ->
    CPairIn p (Conc.i_subst x (NNum n) c2) ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_3:
    forall r n c1 c3 x p P c2,
    RPick r n ->
    GetLast (w_subst x (NNum n) P) c3 ->
    IOneOf p c3 (Conc.i_subst x (NNum n) c2) ->
    IPairIn p (WFor c1 x r P c2)
  (* ---- FIRST ITERATION ONLY ---- *)
  | i_pair_in_for_first_1:
    forall r c1 p P c2 x,
    CPairIn p c1 ->
    IPairIn p (WFor c1 x r P c2)
  | i_pair_in_for_first_2:
    forall r n c1 c3 p P x c2,
    RFirst r n ->
    GetFirst (w_subst x (NNum n) P) c3 ->
    IOneOf p c1 c3 ->
    IPairIn p (WFor c1 x r P c2)
  (* -------- ALL BUT FIRST ---- *)
  | i_pair_in_for_mid_1:
    forall r n c1 c3 p x P c2,
    RPick2 r n ->
    GetFirst (w_subst x (NNum (S n)) P) c3 ->
    IOneOf p (Conc.i_subst x (NNum n) c2) c3 ->
    IPairIn p (WFor c1 x r P c2)

  | i_pair_in_for_mid_2:
    forall r n P x c2 c1 c c' p,
    RPick2 r n ->
    GetLast (w_subst x (NNum n) P) c ->
    GetFirst (w_subst x (NNum (S n)) P) c' ->
    IOneOf p c c' ->
    IPairIn p (WFor c1 x r P c2)
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
    eapply i_pair_in_for_2; eauto.
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
    forall c1 P c2 h v r n p x,
    Conc.RunAll TID_COUNT c1 h ->
    RFirst r n ->
    WRun (WFor Conc.Skip x r P c2) v ->
    MOneOf p h (first v) ->
    ~ Conc.Var TID c1 ->
    ~ WVar TID (w_subst x (NNum n) P) ->
    exists c,
    GetFirst (w_subst x (NNum n) P) c /\
    IOneOf p c1 c.
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
      eapply i_first_1 in Hb; eauto.
      apply i_first_to_get_first in Hb.
      destruct Hb as (c', (Hg, Hci)).
      exists c'.
      split; auto.
      unfold IOneOf; auto.
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
    exists c',
    GetLast i c' /\
    IOneOf p c' c.
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi, Hj)|(Hi, Hj)];
      eapply i_last_1 in Hi; eauto;
      eapply i_last_to_get_last in Hi;
      destruct Hi as (ci, (Hri, Hci));
      unfold IOneOf;
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
    exists c, GetFirst i c /\ IOneOf p c1 c.
  Proof.
    intros.
    destruct p as (a1, a2).
    destruct H1 as [(Hi,Hj)|(Hi,Hj)];
      eapply c_in_1 in Hi; eauto;
      eapply i_first_1 in Hj; eauto;
      eapply i_first_to_get_first in Hj;
      destruct Hj as (c, (Hj,Hij)); unfold IOneOf; exists c; auto.
  Qed.

  Lemma i_one_of_skip_l:
    forall p c,
    ~ IOneOf p Conc.Skip c.
  Proof.
    intros (a1, a2) c [(N,_)|(_, N)];
      apply c_in_skip in N; auto.
  Qed.

  Lemma i_one_of_skip_r:
    forall p c,
    ~ IOneOf p c Conc.Skip.
  Proof.
    intros (a1, a2) c [(_,N)|(N,_)];
      apply c_in_skip in N; auto.
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
    - apply i_one_of_skip_l in H9.
      contradiction.
    - eauto using i_pair_in_for_mid_1, r_step_pick2_rev.
    - eauto using i_pair_in_for_mid_2, r_step_pick2_rev.
  Qed.

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
        destruct H2 as (c1, (c2, (Hg1, (Hg2, Hi)))).
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
          eapply i_pair_in_for_1; eauto using r_step_to_pick.
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
          destruct Hi as (c, (Hg, Hi)).
          apply r_first_to_has_next in Hr.
          eapply i_pair_in_for_mid_1 with (n:=n); eauto using r_step_to_pick2.
        }
        apply m_one_of_inv_first_prefix_l in Hi.
        destruct Hi as [Hi|Hi]. {
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          destruct Hi as (c, (Hg, Hi)).
          eapply i_pair_in_for_3 with (n:=n); eauto using r_step_to_pick.
        }
        eapply i_one_of_1 in Hi; eauto; try handle_not_var.
        destruct Hi as (c1', (c3', (Hl, (Hf, Hi)))).
        assert (Hx := H).
        apply r_step_to_first in H.
        eapply get_first_inv_for_skip in Hf; eauto.
        destruct Hf as [?|(n',(Hf, Hg))]. {
          subst.
          apply i_one_of_skip_r in Hi.
          contradiction.
        }
        assert (n'= S n) by eauto using r_step_inv_next_eq.
        subst.
        apply r_first_to_has_next in Hf.
        eapply i_pair_in_for_mid_2 with (n:=n); eauto using r_step_to_pick2.
      }
      apply m_one_of_inv_first_seq_l in Hi. 2: { eauto using wrun_has_many. }
      eapply i_one_of_4 in Hi; eauto; try handle_not_var.
      destruct Hi as (c, (Hg, Hi)).
      eapply i_pair_in_for_first_2; eauto using r_step_to_first.
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
          eapply i_pair_in_for_1; eauto using r_one_to_pick.
        * simpl in *.
          (* c2 *)
          eapply i_pair_in_for_2; eauto using r_one_to_pick.
          eapply c_pair_in_1; eauto; try handle_not_var.
        * simpl in *.
          (* c2 / w_subst x (NNum n) i *)
          eapply i_one_of_3 in Hi; eauto; try handle_not_var.
          destruct Hi as (c', (Hg, Hi)).
          eapply i_pair_in_for_3 with (n:=n); eauto using r_one_to_pick.
      + (* c1 / w_subst x (NNum n) i *)
        apply m_one_of_inv_first_seq_l in Hi.
        2: { eauto using wrun_has_many. }
        eapply i_one_of_4 in Hi; eauto; try handle_not_var.
        destruct Hi as (c, (Hg, Hi)).
        eapply i_pair_in_for_first_2; eauto using r_one_to_first.
  Qed.

  Definition IEq P Q :=
    forall p,
    IPairIn p P <-> IPairIn p Q.

  (* ------------------------------------------------------------- *)
(*
  Fixpoint i_seq (c:Conc.inst) (i:w_inst) :=
    match i with
    | WSync c' => WSync (Conc.Seq c' c)
    | WSeq i j => WSeq (i_seq c i) j
    | WFor c1 x r i c2 => WFor (Conc.Seq c c1) x r i c2
    end.

  Inductive EPairIn : (access_val * access_val) -> w_inst -> Prop :=
  | e_pair_in_sync:
    forall p c,
    CPairIn p c ->
    EPairIn p (WSync c)

  | e_pair_in_seq_l:
    forall p i j,
    EPairIn p i ->
    EPairIn p (WSeq i j)

  | e_pair_in_seq_r:
    forall p i j c,
    GetLast i c ->
    EPairIn p (i_seq c j) ->
    EPairIn p (WSeq i j)

  | e_pair_in_for_start:
    forall e1 e2 n1 n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    EPairIn p (i_seq c1 (w_subst x (NNum n1) i)) ->
    EPairIn p (WFor c1 x (e1, e2) i c2)

  | e_pair_in_for_mid:
    forall e1 e2 n1 n n2 i x c1 c2 ci p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n < n2 ->
    GetLast (w_subst x (NNum (n - 1)) i) ci ->
    EPairIn p (i_seq (Conc.Seq ci (Conc.i_subst x (NNum (n - 1)) c2)) (w_subst x (NNum n1) i)) ->
    EPairIn p (WFor c1 x (e1, e2) i c2)

  | e_pair_in_for_end:
    forall e1 e2 n1 n2 i x c1 c2 p,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    CPairIn p (Conc.i_subst x (NNum (n2 - 1)) c2 )->
    EPairIn p (WFor c1 x (e1, e2) i c2).

  Lemma c_in_seq_l:
    forall a i j,
    CIn a i ->
    CIn a (Conc.Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using Conc.i_in_seq_l.
  Qed.

  Lemma c_in_seq_r:
    forall a i j,
    CIn a j ->
    CIn a (Conc.Seq i j).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply c_in_def; auto.
    auto using Conc.i_in_seq_r.
  Qed.

  Lemma c_in_inv_seq:
    forall a i j,
    CIn a (Conc.Seq i j) ->
    CIn a i \/ CIn a j.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H1; subst; clear H1; auto using c_in_def.
  Qed.

  Inductive Wellformed: w_inst -> Prop :=
  | wellformed_sync:
    forall c,
    Wellformed (WSync c)
  | wellformed_seq:
    forall i j,
    Wellformed i -> 
    Wellformed j ->
    Wellformed (WSeq i j)
  | wellformed_for_1:
    forall c1 c2 x r r' n i,
    RStep r n r' ->
    Wellformed (w_subst x (NNum n) i) ->
    Wellformed (WFor Conc.Skip x r' i c2) -> 
    Wellformed (WFor c1 x r i c2)
  | wellformed_for_2:
    forall c1 c2 x r n i,
    ROne r n ->
    Wellformed (w_subst x (NNum n) i) ->
    Wellformed (WFor c1 x r i c2).

  Lemma wrun_to_wellformed:
    forall i v,
    WRun i v ->
    Wellformed i.
  Proof.
    intros.
    induction H; try (constructor; auto).
    - subst.
      eapply wellformed_for_1; eauto.
    - eapply wellformed_for_2; eauto.
  Qed.

  Lemma e_pair_in_i_seq_1:
    forall i p,
    CIn p c ->
    EPairIn p (i_seq c1 i).

  Lemma e_pair_in_i_seq_2:
    forall i c2,
    GetFirst i c2 ->
    forall a1 a2 c1,
    CIn a1 c1 ->
    CIn a2 c2 ->
    EPairIn (a1, a2) (i_seq c1 i).
  Proof.
    intros i c2 H.
    induction H; intros; simpl.
    - constructor.
      apply c_pair_in_def; auto using c_in_seq_l, c_in_seq_r.
    - auto using e_pair_in_seq_l.
    - destruct r as (e1, e2).
      eapply e_pair_in_for_start; eauto.
  Qed.

  Lemma e_pair_in_1:
(*    forall i h,
    WRun i h ->
    ~ WVar TID i -> *)
    forall p i,
    IPairIn p i ->
    EPairIn p i.
  Proof.
    intros.
    induction H.
    - constructor; auto.
    - constructor; auto.
    - eapply e_pair_in_seq_r.
      admit.
      admit.
    - destruct p as (a1, a2).
      destruct H1 as [(Ha, Hb)|(Ha, Hb)].
      + eapply e_pair_in_seq_r; eauto.
  Qed.
  
*)

End Defs.