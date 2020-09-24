Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import RExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.

Require Import Lia.

Import ListNotations.
Require Conc.

Section C1.
  Context {A:Access}.
  Context `{T:Tasks}.
  Inductive inst :=
  | Skip
  | Sync
  | If: bexp -> inst -> inst
  | Block: Conc.inst -> inst
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst.


Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Sync => Sync
  | Block c => Block (Conc.i_subst x v c)
  | If b i => If (b_subst x v b) (i_subst x v i)
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  end.


Notation history := (list access_val).

Notation mhistory := (list history).

Notation histpair := (mhistory * history) % type.


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
(*
  Lemma p_in_as_nil:
    forall a m,
    ~ PInAs a (ph_one []) m.
  Proof.
    intros.
    intros N.
    apply p_in_inv_one in N.
    contradiction.
  Qed.
*)
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

  
Inductive Run: inst -> phaseset -> Prop :=
| run_skip:
  Run Skip (ph_one [])
| run_sync:
  Run Sync (ph_cons [] (ph_one []))
| run_block:
  forall c h,
  Conc.RunAll TID_COUNT c h ->
  Run (Block c) (ph_one h)
| run_seq: forall i j mh_i mh_j mh,
  Run i mh_i ->
  Run j mh_j ->
  ph_seq mh_i mh_j = mh ->
  Run (Seq i j) mh
| run_if_true: forall b i mh,
  BStep b true ->
  Run i mh ->
  Run (If b i) mh
| run_if_false: forall b i,
  BStep b false ->
  Run (If b i) (ph_one [])
| run_for_cons:
  forall e1 e2 n1 n2 i x h1 h2 h3,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 < n2 ->
  Run (i_subst x (NNum n1) i) h1 ->
  Run (For x (NNum (S n1), NNum n2) i) h2 ->
  ph_seq h1 h2 = h3 ->
  Run (For x (e1, e2) i) h3
| run_for_nil:
  forall x i e1 e2 n1 n2,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 >= n2 ->
  Run (For x (e1, e2) i) (ph_one []).


End C1.
