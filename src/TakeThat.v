Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.

Require Import Lia.

Import ListNotations.
Require Conc.
Require Import NSync.
Section C1.

Notation history := (list access_val).

Notation mhistory := (list history).

Notation histpair := (mhistory * history) % type.

Context `{T:Tasks}.
Context {A:Access}.

(* ----------------------- PHASESET ------------------- *)
(*
Inductive phaseset :=
| ph_base: history -> phaseset
| ph_many: history -> mhistory -> history -> phaseset
.

Definition merge (p1 p2:phaseset): phaseset :=
match p1, p2 with
| ph_one h1, ph_one h2 => ph_one (h1 ++ h2)
| ph_one h1, ph_many h2 m2 t2 => ph_many (h1 ++ h2) m2 t2
| ph_many h1 m1 t1, ph_one h2 => ph_many h1 m1 (t1 ++ h2)
| ph_many h1 m1 t1, ph_many h2 m2 t2 =>
  ph_many h1 (m1 ++ (t1 ++ h2) :: m2) t2
end.
*)
Inductive phaseset :=
| ph_one: history -> phaseset
| ph_cons: history -> phaseset -> phaseset
.

Fixpoint HIn h p :=
match p with
| ph_one h' => h' = h
| ph_cons h' p => h' = h \/ HIn h p
end.

Definition ph_skip := ph_one [].
Definition ph_block h := ph_one h.
Fixpoint ph_suffix (p:phaseset) (h:history) :=
match p with
| ph_one h' => ph_one (h' ++ h)
| ph_cons h' p => ph_cons h' (ph_suffix p h)
end.

Definition ph_prefix h p :=
match p with
| ph_one h' => ph_one (h ++ h')
| ph_cons h' p => ph_cons (h ++ h') p
end.

Fixpoint ph_seq p1 p2 :=
  match p1 with
  | ph_one h1 => ph_prefix h1 p2 
  | ph_cons h1 p1 => ph_cons h1 (ph_seq p1 p2)
  end.

Fixpoint PIn (a:access_val) (p:phaseset) : Prop :=
match p with
| ph_one h => List.In a h
| ph_cons h p => List.In a h \/ PIn a p
end.

Fixpoint phase_to_list (p:phaseset) : mhistory :=
match p with
| ph_one h => [h]
| ph_cons h m => h::phase_to_list m
end.

Inductive phaseloc := FirstPhase | MidPhase | LastPhase.

Fixpoint PInLast a (p:phaseset) := 
  match p with
  | ph_one h => List.In a h
  | ph_cons _ p => PInLast a p
  end.

Definition PInFirst a (p:phaseset) :=
  match p with
  | ph_one _ => False
  | ph_cons h _ => List.In a h
  end.

Definition PInMid a (p:phaseset) :=
  match p with
  | ph_one _ => False
  | ph_cons _ p => PIn a p
  end.

Definition PInAs a p m :=
  match m with
  | FirstPhase => PInFirst a p
  | MidPhase => PInMid a p
  | LastPhase => PInLast a p
  end.

Lemma p_in_mid_cons_in_first:
  forall a h p,
  PInFirst a p ->
  PInMid a (ph_cons h p).
Proof.
  intros.
  destruct p as [h'|h']; simpl in *; auto.
  contradiction.
Qed.

Lemma p_in_mid_to_p_in:
  forall a p,
  PInMid a p ->
  PIn a p.
Proof.
  intros.
  destruct p; simpl in *; auto.
  contradiction.
Qed.

Lemma p_in_mid_cons:
  forall a h p,
  PInMid a p ->
  PInMid a (ph_cons h p).
Proof.
  intros.
  simpl.
  auto using p_in_mid_to_p_in.
Qed.

Lemma p_in_last_cons:
  forall a h p,
  PInLast a p ->
  PInLast a (ph_cons h p).
Proof.
  intros.
  simpl.
  assumption.
Qed.

Lemma p_in_to_p_in_as:
  forall a p,
  PIn a p ->
  exists m, PInAs a p m.
Proof.
  induction p; intros Hi; simpl in Hi. {
    exists LastPhase.
    auto.
  }
  destruct Hi. {
    exists FirstPhase.
    eauto.
  }
  apply IHp in H.
  destruct H as (m, Hi).
  destruct m; simpl in Hi.
  - exists MidPhase.
    apply p_in_mid_cons_in_first.
    assumption.
  - exists MidPhase.
    apply p_in_mid_cons; auto.
  - exists LastPhase.
    auto.
Qed.

(*
Inductive PIn a : phaseset -> phaseloc -> Prop :=
| p_in_one: forall h,
  List.In a h ->
  PIn a (ph_one h) LastPhase
| p_in_head: forall h m t,
  List.In a h ->
  PIn a (ph_cons h m) FirstPhase
| p_in_mid: forall h m t,
  PIn a m ->
  PIn a (ph_cons h m) MidPhase
| p_in_tail: forall h m t,
  List.In a t ->
  PIn a (ph_many h m t) LastPhase
  .
*)

  Lemma p_in_nil:
    forall a,
    ~ PIn a (ph_one []).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma p_in_as_nil:
    forall a m,
    ~ PInAs a (ph_one []) m.
  Proof.
    intros.
    intros N.
    apply p_in_inv_one in N.
    contradiction.
  Qed.

  Lemma p_in_as_inv_cons:
    forall a h p m,
    PInAs a (ph_cons h p) m ->
    (m = FirstPhase /\ List.In a h)
    \/ (m = MidPhase /\ PIn a p)
    \/ (m = LastPhase /\ PInLast a p).
  Proof.
    intros.
    destruct m; simpl in *; auto.
  Qed.

  Lemma p_in_as_inv_cons_nil:
    forall a p m,
    PInAs a (ph_cons [] p) m ->
    (m = MidPhase /\ PIn a p)
    \/ (m = LastPhase /\ PInLast a p).
  Proof.
    intros.
    destruct m; simpl in *; auto.
    contradiction.
  Qed.

  Lemma p_in_as_inv_one:
    forall a h m,
    PInAs a (ph_one h) m ->
    m = LastPhase /\ List.In a h.
  Proof.
    intros.
    destruct m; simpl in *; auto; contradiction.
  Qed.

  Lemma p_in_as_inv_prefix:
    forall a h p m,
    PInAs a (ph_prefix h p) m ->
    List.In a h \/
    PInAs a p m.
  Proof.
    intros.
    destruct m; destruct p as [h'|h']; simpl in *; auto.
    - apply in_app_iff in H.
      destruct H; auto.
    - apply in_app_iff in H.
      destruct H; auto.
  Qed.
 (*
  Lemma p_in_inv_many:
    forall a h m t p,
    PIn a (ph_many h m t) p ->
    List.In a h \/ MIn a m \/ List.In a t.
  Proof.
    intros.
    inversion H; subst; auto.
  Qed.

  (* XXX: move to InUtil *)
  Lemma m_in_inv_cons:
    forall A a h m,
    @MIn A a (h :: m) ->
    In a h \/ MIn a m.
  Proof.
    intros.
    assert (R: h ::m = [h] ++m) by auto.
    rewrite R in H.
    apply m_in_inv_app in H.
    destruct H as [H|H]; auto.
    apply m_in_inv_cons_nil in H.
    auto.
  Qed.

  Lemma p_in_inv_merge:
    forall a p1 p2 m,
    PIn a (merge p1 p2) m ->
    PIn a p1  \/ PIn a p2.
  Proof.
    intros.
    destruct p1, p2; simpl in *.
    - apply p_in_inv_one in H.
      apply in_app_iff in H.
      destruct H; auto using p_in_one.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]].
      + apply in_app_iff in H.
        destruct H; auto using p_in_one, p_in_head.
      + auto using p_in_mid.
      + auto using p_in_tail.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]]; auto using p_in_head, p_in_mid.
      apply in_app_iff in H.
      destruct H; auto using p_in_tail, p_in_one.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]]; auto using p_in_head, p_in_tail.
      apply m_in_inv_app in H.
      destruct H; auto using p_in_mid.
      apply m_in_inv_cons in H.
      destruct H as [H|H]; auto using p_in_mid.
      apply in_app_iff in H.
      destruct H; auto using p_in_tail, p_in_head.
  Qed.

  Lemma p_in_merge_l:
    forall a p1 p2,
    PIn a p1 ->
    PIn a (merge p1 p2).
  Proof.
    intros a p1 p2 Hi.
    inversion Hi; subst; clear Hi; simpl.
    - destruct p2.
      + apply p_in_one.
        apply in_app_iff.
        auto.
      + apply p_in_head.
        apply in_app_iff.
        auto.
    - destruct p2; auto using p_in_one, p_in_head.
    - destruct p2; apply p_in_mid; auto.
      auto using m_in_app_l.
    - destruct p2.
      + apply p_in_tail; apply in_app_iff; auto.
      + apply p_in_mid.
        apply m_in_app_r.
        apply m_in_eq.
        apply in_app_iff.
        auto.
  Qed.

  Lemma p_in_merge_r:
    forall a p1 p2,
    PIn a p2 ->
    PIn a (merge p1 p2).
  Proof.
    intros a p1 p2 Hi.
    inversion Hi; subst; clear Hi; simpl; destruct p1; simpl;
      try apply p_in_one.
    - apply in_app_iff; auto.
    - apply p_in_tail.
      apply in_app_iff; auto.
    - apply p_in_head.
      apply in_app_iff; auto.
    - apply p_in_mid.
      apply m_in_app_r.
      apply m_in_eq.
      apply in_app_iff; auto.
    - apply p_in_mid.
      assumption.
    - apply p_in_mid.
      apply m_in_app_r.
      apply m_in_cons.
      assumption.
    - apply p_in_tail.
      assumption.
    - apply p_in_tail.
      assumption.
  Qed.
*)
(* -------------------- RUN --------------------------- *)

Inductive Run2: inst -> phaseset -> Prop :=
| run2_skip:
  Run2 Skip (ph_one [])
| run2_sync:
  Run2 Sync (ph_cons [] (ph_one []))
| run2_block:
  forall c h,
  Conc.RunAll TID_COUNT c h ->
  Run2 (Block c) (ph_one h)
| run2_seq: forall i j mh_i mh_j mh,
  Run2 i mh_i ->
  Run2 j mh_j ->
  ph_seq mh_i mh_j = mh ->
  Run2 (Seq i j) mh
| run2_if_true: forall b i mh,
  BStep b true ->
  Run2 i mh ->
  Run2 (If b i) mh
| run2_if_false: forall b i,
  BStep b false ->
  Run2 (If b i) (ph_one [])
| run2_for_cons:
  forall e1 e2 n1 n2 i x h1 h2 h3,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 < n2 ->
  Run2 (i_subst x (NNum n1) i) h1 ->
  Run2 (For x (NNum (S n1), NNum n2) i) h2 ->
  ph_seq h1 h2 = h3 ->
  Run2 (For x (e1, e2) i) h3
| run2_for_nil:
  forall x i e1 e2 n1 n2,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 >= n2 ->
  Run2 (For x (e1, e2) i) (ph_one []).

Goal Run2 (Seq Sync Skip) (ph_cons [] (ph_one [])).
Proof.
  eapply run2_seq.
  + apply run2_sync.
  + apply run2_skip.
  + reflexivity.
Qed.

Goal Run2 (Seq Sync Sync) (ph_cons [] (ph_cons [] (ph_one []))).
Proof.
  eapply run2_seq.
  + apply run2_sync.
  + apply run2_sync.
  + reflexivity.
Qed.

Goal Run2 (Seq (Seq Sync Sync) Sync) (ph_cons [] (ph_cons [] (ph_cons [] (ph_one [])))).
Proof.
  eapply run2_seq.
  - eapply run2_seq.
    + apply run2_sync.
    + apply run2_sync.
    + reflexivity.
  - apply run2_sync.
  - reflexivity.
Qed.

(* ------------------------------ VAR -------------------------- *)
  Fixpoint Var x i :=
  match i with
  | Skip | Sync | Loop _ _ _ => False
  | Block c => Conc.Var x c
  | Seq i j => Var x i \/ Var x j
  | For y _ i => x = y \/ Var x i
  | If _ i => Var x i
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

(* ------------------------------ IIN -------------------------- *)

Fixpoint has_sync p :=
  match p with
  | Skip | Block _ => false
  | Sync => true
  | For _ _ i | If _ i => has_sync i
  | Seq i j => orb (has_sync i) (has_sync j)
  | Loop _ _ _ => false
  end.

Inductive IIn (a:access_val) : inst -> phaseloc -> Prop :=
| i_in_block: forall i,
  Conc.IIn a i ->
  IIn a (Block i) LastPhase

| i_in_seq_l_eq:
  forall i j p,
  IIn a i p ->
  p = FirstPhase \/ p = MidPhase \/ has_sync j = false ->
  IIn a (Seq i j) p
  
| i_in_seq_l_last:
  forall i j,
  IIn a i LastPhase ->
  has_sync j = true ->
  IIn a (Seq i j) MidPhase

| i_in_seq_r_eq:
  forall i j p,
  p = MidPhase \/ p = LastPhase \/ has_sync i = false ->
  IIn a j p ->
  IIn a (Seq i j) p
| i_in_seq_r_first:
  forall i j,
  IIn a j FirstPhase ->
  has_sync i = true ->
  IIn a (Seq i j) MidPhase
  
| i_in_if: forall b i p,
  BStep b true ->
  IIn a i p ->
  IIn a (If b i) p

 | i_in_for_unsync:
  forall e1 e2 i n1 n2 n x,
  has_sync i = true ->
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 <= n < n2 ->
  IIn a (i_subst x (NNum n) i) LastPhase ->
  IIn a (For x (e1,e2) i) LastPhase

 | i_in_for_first:
  forall e1 e2 i n1 n2 x,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 < n2 ->
  IIn a (i_subst x (NNum n1) i) FirstPhase ->
  IIn a (For x (e1,e2) i) FirstPhase

 | i_in_for_last:
  forall e1 e2 i n1 n2 x,
  NStep e1 n1 ->
  NStep e2 (S n2) ->
  IIn a (i_subst x (NNum n2) i) LastPhase ->
  IIn a (For x (e1,e2) i) LastPhase

 | i_in_for_mid:
  forall e1 e2 i n1 n2 n x m,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 <= n < n2 ->
  IIn a (i_subst x (NNum n) i) m ->
  IIn a (For x (e1,e2) i) MidPhase
  .


  Lemma run_p_in_to_i_in:
    forall i h,
    Run2 i h ->
    ~ Var TID i ->
    forall a m,
    PInAs a h m ->
    IIn a i m.
  Proof.
    intros i h H.
    induction H; intros Hwf a m Hi.
    - apply p_in_as_nil in Hi.
      contradiction.
    - apply p_in_as_inv_cons_nil in Hi.
      destruct Hi as [(?,Hi)|(?,Hi)]; subst; simpl in *; contradiction.
    - apply p_in_as_inv_one in Hi.
      destruct Hi as (?,Hi).
      subst.
      apply i_in_block.
      eapply Conc.run_all_to_i_in in H; eauto.
    - subst.
      destruct mh_i as [h|h]; simpl in Hi.
      + apply p_in_as_inv_prefix in Hi.
        destruct Hi as [Hi|Hi].
        * 
      apply p_in_inv_merge in Hi.
      simpl in Hwf.
      destruct Hi.
      + apply i_in_seq_l; auto.
      + apply i_in_seq_r; auto.
    - auto using i_in_if.
    - apply p_in_inv_one in Hi.
      contradiction.
    - subst.
      apply p_in_inv_merge in Hi.
      simpl in Hwf.
      destruct Hi as [Hi|Hi].
      + eapply i_in_for; eauto.
        apply IHRun2_1; auto.
        intros N.
        apply var_subst_inv_1 in N.
        auto.
      + apply IHRun2_2 in Hi; auto.
        inversion Hi; subst; clear Hi.
        eapply i_in_for with (n:=n); eauto.
        assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
        assert (n3 = n2) by eauto using n_step_fun, n_step_num.
        subst.
        lia.
    - apply p_in_inv_one in Hi.
      contradiction.
  Qed.

  Lemma run_i_in_to_p_in:
    forall i h,
    Run2 i h ->
    ~ Var TID i ->
    forall a,
    access_tid a < TID_COUNT ->
    IIn a i ->
    PIn a h.
  Proof.
    intros i h H.
    induction H;
      intros Hwf a Hlt Hi;
      simpl in Hwf;
      inversion Hi;
      subst;
      clear Hi.
    - apply p_in_one.
      eapply Conc.run_all_i_in_to_in; eauto.
    - apply p_in_merge_l.
      auto.
    - apply p_in_merge_r.
      auto.
    - auto.
    - assert (N: true = false) by eauto using b_step_fun.
      inversion N.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (X: n1 = n \/ n1 < n) by lia.
      destruct X. {
        subst.
        apply p_in_merge_l.
        apply IHRun2_1; auto.
        intros N.
        apply var_subst_inv_1 in N.
        auto.
      }
      apply p_in_merge_r.
      apply IHRun2_2; auto.
      apply i_in_for with (n1:=S n1) (n2:=n2) (n:=n); auto using n_step_num.
      lia.
    - assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      lia.
  Qed.
