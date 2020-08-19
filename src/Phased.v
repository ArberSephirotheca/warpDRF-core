Require Import Coq.Lists.List.
Require Import NExp.
Require Import Var.
Require Import AccExp.
Require Import Tasks.
Require Import VHist.
Require Conc.
Require Import ALang.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.

  Notation history := (list access_val).
  Notation mhistory := (list history).
(*
  Inductive inst :=
  | Sync
  | Block: Conc.inst -> inst
  | Seq: inst -> inst -> inst
  | For: inst -> var -> range -> inst -> inst.
*)
  Inductive phased :=
  | SyncUnsync: inst -> Conc.inst -> phased
  | OnlyUnsync: Conc.inst -> phased.

  Inductive Run: inst -> list history -> Prop :=
  | run_sync:
    Run Sync []
  | run_block:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) [h]
  | run_seq: forall i j mh_i mh_j mh,
    Run i mh_i ->
    Run j mh_j ->
    mh_i ++ mh_j = mh ->
    Run (Seq i j) mh
  | run_for_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) m1 ->
    Run (For x (NNum (S n1), NNum n2) i) m2 ->
    m1 ++ m2 = m3 ->
    Run (For x (e1, e2) i) m3
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run (For x (e1, e2) i) [].

  (* ----------------------- Acces membership ---------------------- *)

  Inductive Phase : inst -> nat -> Prop :=
  | phase_block:
    forall c,
    Phase (Block c) 1
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
  | phase_for_nil:
    forall i x e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Phase (For x (e1, e2) i) 0.

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

  (* ---------------------------- TRANSLATION ---------------------- *)

  Fixpoint seq1 (c:Conc.inst) (n:inst) :=
    match n with
    | Sync => Block c
    | Block c2 => Block (Conc.Seq c c2)
    | Seq i j => Seq (seq1 c i) j
    | For x r j => (* Should not happen *) For x r j 
    end.

  Definition seq2 (c:Conc.inst) (a:phased) :=
    match a with
    | OnlyUnsync c2 => OnlyUnsync (Conc.Seq c c2)
    | SyncUnsync n c2 => SyncUnsync (seq1 c n) c2
    end.

  Definition seq3 (n:inst) (a:phased) :=
    match a with
    | OnlyUnsync c2 => SyncUnsync n c2
    | SyncUnsync n2 c2 => SyncUnsync (Seq n n2) c2
    end.

  Definition seq (a1 a2: phased) : phased :=
    match a1 with
    | OnlyUnsync c1 => seq2 c1 a2
    | SyncUnsync n c1 => seq3 n (seq2 c1 a2)
    end.

  Fixpoint i_subst x v (i:inst) :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | For y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      For y (r_subst x v r) i'
    end.

  Fixpoint translate (i:ALang.inst) : phased :=
    match i with
    | ALang.Block c => OnlyUnsync c
    | ALang.Sync => SyncUnsync Sync Conc.Skip
    | ALang.Seq i j => seq (translate i) (translate j)
    | ALang.For x (e1, e2) i =>
      match translate i with
      | OnlyUnsync c => OnlyUnsync (Conc.For x (e1, e2) c)
      | SyncUnsync b c =>
        let e2' := NBin NMinus e2 (NNum 1) in
        let x' := NBin NPlus (NNum 1) (NVar x) in
        SyncUnsync
          (Seq (i_subst x e1 b) (For x (e1, e2') (seq1 c (i_subst x x' b))))
          (Conc.i_subst x e2' c)
      end
    end.
End Defs.