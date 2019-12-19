Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Import ListNotations.

Module L1 (M:ACC).

Section Defs.
  Inductive proto :=
  | PSkip
  | PSync
  | PAcc: M.E -> proto
  | PSeq : proto -> proto -> proto
  | PFor : var -> range -> proto -> proto
  | PLoop : var -> list nat -> proto -> proto.

  Fixpoint p_subst x v p :=
  match p with
  | PAcc a => PAcc (M.a_subst x v a)  
  | PSeq p1 p2 => PSeq (p_subst x v p1) (p_subst x v p2)
  | PFor y r p2 => if VAR.eq_dec x y then p else (PFor y (r_subst x v r) (p_subst x v p2)) 
  | PLoop y r p2 => if VAR.eq_dec x y then p else (PLoop x r (p_subst x v p2)) 
  | PSkip => PSkip
  | PSync => PSync 
  end.

  Definition state := list M.A.

  Inductive Step: (state * proto) -> (state * proto) -> Prop :=
  | step_sync:
    forall s,
    Step (s, PSync) (nil, PSkip)
  | step_acc:
    forall s e a,
    M.AStep e a ->
    Step (s, PAcc e) (a ++ s, PSkip)
  | step_seq_step:
    forall s1 s2 p1 p2 p3,
    Step (s1, p1) (s2, p2) ->
    Step (s1, PSeq p1 p3) (s2, PSeq p2 p3)
  | step_seq_skip:
    forall s p,
    Step (s, PSeq PSkip p) (s, p)
  | step_for_step:
    forall x r p l s,
    RStep r l ->
    Step (s, PFor x r p) (s, PLoop x l p)
  | step_loop_step:
    forall s x n l p,
    Step (s, PLoop x (n::l) p) (s, PSeq (p_subst x n p) (PLoop x l p))
  | step_loop_skip:
    forall s x p,
    Step (s, PLoop x [] p) (s, PSkip).

  Fixpoint upper_bound n l : nat :=
  match l with
  | [] => n
  | n :: l => upper_bound n l
  end.

  Definition bounds l :=
  match l with
  | [] => (0, 0) (* should not appear *)
  | [ _ ] => (0, 0) (* should not appear *)
  | n1 :: n2 :: l => (n1, upper_bound n2 l)
  end.

End Defs.
End L1.

Module L2 (M:ACC).
Section Defs.

  Inductive proto :=
  | PSkip
  | PAcc: M.E -> proto
  | PSeq : proto -> proto -> proto
  | PDecl : var -> range -> proto -> proto
  | PPar : var -> list nat -> proto -> proto.

  Fixpoint p_subst x v p :=
  match p with
  | PAcc a => PAcc (M.a_subst x v a)  
  | PSeq p1 p2 => PSeq (p_subst x v p1) (p_subst x v p2)
  | PDecl y r p2 => if VAR.eq_dec x y then p else (PDecl y (r_subst x v r) (p_subst x v p2)) 
  | PPar y r p2 => if VAR.eq_dec x y then p else (PPar x r (p_subst x v p2)) 
  | PSkip => PSkip
  end.

  Definition state := list M.A.

  Definition proc := list (state * proto).

  Fixpoint join (h:proc) (q:proto) :=
  match h with
  | [] => []
  | (s,p)::h => (s, PSeq p q) :: h
  end.

  Inductive SStep: (state * proto) -> list (state * proto) -> Prop :=
  | s_step_acc:
    forall s e a,
    M.AStep e a ->
    SStep (s, PAcc e) [(a ++ s, PSkip)]
  | s_step_seq_step:
    forall s1 p1 h p3,
    SStep (s1, p1) h ->
    SStep (s1, PSeq p1 p3) (join h p3)
  | s_step_seq_skip:
    forall s p,
    SStep (s, PSeq PSkip p) [(s, p)]
  | s_step_for_step:
    forall x r p l s,
    RStep r l ->
    SStep (s, PDecl x r p) [(s, PPar x l p)]
  | s_step_par_step:
    forall s x n l p,
    SStep (s, PPar x (n::l) p) ((s, p_subst x n p) :: (s, PPar x l p) :: [])
  | s_step_par_skip:
    forall s x p,
    SStep (s, PPar x [] p) [(s, PSkip)].

  Inductive Step: proc -> proc -> Prop :=
  | step_eq:
    forall p h1 h2,
    SStep p h1 ->
    Step (p::h2) (h1 ++ h2)
  | step_skip:
    forall s h,
    Step ((s,PSkip)::h) h
  | step_cons:
    forall p h1 h2,
    Step h1 h2 ->
    Step (p::h1) (p::h2).

End Defs.
End L2.

Section Defs.
(*
  Inductive proto :=
  | PSkip
  | PSync
  (* location @ range: mode *)
  | PAcc: loc -> list nexp -> mode -> proto
  | PSeq : proto -> proto -> proto
  (* Non-deterministic loop *)
  | PDecl : var -> range -> proto -> proto
  | PFor : var -> range -> proto -> proto.
*)
(*
  Definition history := list access.

  Definition state := Map_LOC.t history.

  Definition add_acc x a (s:state) :=
  match Map_LOC.find x s with
  | Some h => Map_LOC.add x (a::h) s
  | None => Map_LOC.add x (a::[]) s
  end.

  Fixpoint p_add x idx m l (s:state) :=
  match l with
  | [] => s
  | t :: l => add_acc x {| access_tid := t; access_mode := m; access_index := idx |} s
  end.
*)
End Defs.

Section SO.
(*
  Definition SafeHist h :=
    forall a1 a2, List.In a1 h -> List.In a2 h -> SafeAcc a1 a2. 

  Definition SafeSt s := forall l h, Map_LOC.MapsTo l h s -> SafeHist h.

  Definition Safe (a:state * proto) := let (s,_) := a in SafeSt s.

  Definition SafeMap f :=
    forall s,
    SafeSt s ->
    forall p s' p',
    Step (s, p) (s', p') <->
    Step (f (s, p)) (f (s', p')).

  Lemma safe_map_to_drf:
    forall f a,
    SafeMap f ->
    DRF a ->
    DRF (f a).
  Proof.
    intros.
    unfold DRF in *.
    unfold DRF, MStep.
    intros.
    generalize dependent 
  Qed.
*)
End SO.

Module PhaseOrdering (M:ACC).
  Module M1 := L1 M.
  Module M2 := L2 M.
Section PO.
  Fixpoint size p :=
  match p with
  | M1.PAcc _
  | M1.PSkip => NNum 0
  | M1.PSync => NNum 1
  | M1.PSeq p1 p2 => add (size p1) (size p2)
  | M1.PFor x (lo, hi) p => mul (sub hi lo) (size p) 
  | M1.PLoop x l p =>
    let (lo, hi) := M1.bounds l in mul (sub (NNum hi) (NNum lo)) (size p) 
  end.

  Fixpoint flatten p n :=
  match p with
  | M1.PSkip => M2.PSkip
  | M1.PSync => M2.PSkip
  | M1.PAcc a => M2.PAcc (M.prefix_index a n)
  | M1.PSeq p1 p2 => M2.PSeq (flatten p1 n) (flatten p2 (add n (size p1)))
  | M1.PFor x r p => M2.PDecl x r (flatten p (add n (mul (NVar x) (size p))))  
  | M1.PLoop x r p => M2.PSkip
  (* PDecl x r (flatten p (add n (mul (NVar x) (size p))))  *)
  end.

  Lemma drf_to_safe_st:
    forall tids s p,
    DRF tids (s, p) ->
    SafeSt s.
  Proof.
    unfold DRF; intros.
    apply H with (p':=p).
    apply rt_refl.
  Qed.



  Lemma drf_sync:
    forall tids s,
    DRF tids (s, PSync) <-> SafeSt s.
  Proof.
    split; intros.
    + eauto using drf_to_safe_st.
    + unfold DRF.
      intros.
      induction H0.
      - 
  Qed.

  Corollary corr:
    forall tids s p,
    DRF tids (s, p) <-> DRF tids (s, flatten p (NNum 0)).
  Proof.
    induction p; intros; simpl.
    - intuition.
    - split; intros. {
        
      }
  Qed.
End PO.
End PhaseOrdering.