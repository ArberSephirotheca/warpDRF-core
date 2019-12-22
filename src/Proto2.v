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
Require Import Acc.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Proto1.

Import ListNotations.

Module L2 (M:ACC).
  Module H := History M.

Section Defs.
  Import Aniceto.Graphs.Graph.

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

  Definition history := list M.A.

  Definition state := list (history * proto).

  Fixpoint join (l:state) (q:proto) :=
  match l with
  | [] => []
  | (h,p)::l => (h, PSeq p q) :: l
  end.

  Inductive SStep: (history * proto) -> state -> Prop :=
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

  Inductive Step: state -> state -> Prop :=
  | step_eq:
    forall p h1 h2,
    SStep p h1 ->
    Step (p::h2) (h1 ++ h2)
  | step_skip:
    forall s h,
    Step ((s,PSkip)::h) h.

  Definition MStep := clos_refl_trans _ Step.

  Definition Value (s:state) := s = nil.

  Definition BStep := BigStep _ Step Value.

  Definition L1_Safe (s:(history*proto)) := let (h, _) := s in H.Safe h.

  Definition Safe : state -> Prop := List.Forall L1_Safe.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Definition SafeStep (p:state * state) :=
    let (x,y) := p in Step x y /\ Safe x /\ Safe y.

  Inductive SafePath : state -> Prop :=
  | safe_path_some:
    forall a b w,
    Walk2 SafeStep a b w ->
    Safe a ->
    Value b ->
    SafePath a
  | safe_path_none:
    SafePath [].

  Lemma drf_to_safe:
    forall a,
    DRF a ->
    Safe a.
  Proof.
    unfold DRF; intros.
    apply H with (b:=a).
    apply rt_refl.
  Qed.

  Lemma s_step_fun:
    forall a l1 l2,
    SStep a l1 ->
    SStep a l2 ->
    l1 = l2.
  Proof.
    intros (h,p).
    generalize dependent h.
    induction p; intros;
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; auto.
    - assert (a0 = a) by eauto using M.a_step_fun; subst.
      reflexivity.
    - assert (h0 = h1) by eauto.
      subst.
      reflexivity.
    - inversion H5.
    - inversion H4.
    - assert (l0 = l) by eauto using r_step_fun.
      subst.
      reflexivity.
  Qed.

  Lemma step_fun:
    forall a b c,
    Step a b ->
    Step a c ->
    b = c.
  Proof.
    induction a; intros; inversion H; inversion H0; subst; clear H H0.
    + assert (h0 = h1) by eauto using s_step_fun.
      subst.
      reflexivity.
    + inversion H4.
    + inversion H7.
    + reflexivity.
  Qed.

  Lemma b_step_skip:
    forall h,
    BStep [(h, PSkip)] [].
  Proof.
    intros.
    apply big_step_cons with (y:=[]).
    + apply step_skip.
    + apply big_step_nil.
      reflexivity.
  Qed.

  Lemma big_step_to_clos_trans:
    forall x y,
    BStep x y ->
    clos_refl_trans _ Step x y.
  Proof.
    intros.
    induction H; 
      eauto using rt_trans, rt_step, rt_refl.
  Qed.

  Lemma safe_nil:
    Safe [].
  Proof.
    apply Forall_nil.
  Qed.

  Lemma safe_cons:
    forall x l,
    Safe l ->
    L1_Safe x ->
    Safe (x::l).
  Proof.
    intros.
    apply Forall_cons; auto.
  Qed.

  Let safe_skip:
    forall h,
    H.Safe h ->
    Safe [(h, PSkip)].
  Proof.
    repeat split; auto using step_skip, safe_nil, safe_cons.
  Qed.

  Let safe_step_skip:
    forall h,
    H.Safe h ->
    SafeStep ([(h, PSkip)], []).
  Proof.
    intros.
    unfold SafeStep.
    repeat split; auto using step_skip, safe_nil, safe_skip.
  Qed.

  Lemma safe_path_skip:
    forall h,
    H.Safe h ->
    SafePath [(h, PSkip)].
  Proof.
    intros.
    remember [(h, PSkip)] as v1.
    remember [] as v2.
    apply safe_path_some with (b:=v2) (w:=[(v1,v2)]); subst.
    + apply edge_to_walk2.
      auto using safe_step_skip.
    + auto using safe_skip.
    + reflexivity.
  Qed.

  Lemma safe_path_in_to_safe:
    forall l h p,
    SafePath l ->
    List.In (h, p) l ->
    H.Safe h.
  Proof.
    intros.
    inversion H; subst; clear H. {
      inversion H1; subst; clear H1.
      inversion H; subst; clear H.
      destruct x as (v1, v2).
      destruct H1 as (w', (?, ?)).
      subst.
      simpl in *. 
      apply walk_to_forall in H5.
      rewrite Forall_forall in *.
      assert (Hi: List.In (v1, v2) ((v1, v2) :: w')) by auto using in_eq.
      apply H5 in Hi.
      destruct Hi as (?, (?, ?)).
      unfold Safe in *.
      rewrite Forall_forall in *.
      apply H1 in H0.
      assumption.
    }
    contradiction.
  Qed.

  Lemma safe_path_inv_skip:
    forall h,
    SafePath [(h, PSkip)] ->
    H.Safe h.
  Proof.
    intros.
    assert (Hi: List.In (h, PSkip) [(h, PSkip)]) by auto using in_eq.
    apply safe_path_in_to_safe in Hi; auto.
  Qed.

  (*
  Lemma m_step_inv_skip:
    forall h l, 
    MStep [(h, PSkip)] l ->
    l = [] \/ l = [(h, PSkip)].
  Proof.
    intros.
    induction H using clos_refl_trans_ind_left.
    - intuition.
    - 
    
    inversion H; subst; clear H.
    - inversion H0; subst; clear H0. {
        inversion H3.
      }
      intuition.
    - intuition.
    - 
  Qed.
  *)
(*
  Inductive Reachable : proc -> list proc -> Prop :=
  | reachable_nil:
    forall h,
    Reachable (h, PSkip) [(h, PSkip)]
  | reachable_cons:
    forall a b l,
    Step a b ->
    Reachable b l ->
    Reachable a (a :: l).
*)

End Defs.
End L2.

Module PhaseOrdering (M:ACC).
  Module M1 := L1 M.
  Module M2 := L2 M.
  Module H := History M.

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

  Fixpoint flatten n p :=
  match p with
  | M1.PSkip => M2.PSkip
  | M1.PSync => M2.PSkip
  | M1.PAcc a => M2.PAcc (M.e_prefix_index n a)
  | M1.PSeq p1 p2 => M2.PSeq (flatten n p1) (flatten (add n (size p1)) p2)
  | M1.PFor x r p => M2.PDecl x r (flatten (add n (mul (NVar x) (size p))) p)  
  | M1.PLoop x r p => M2.PSkip
  (* PDecl x r (flatten p (add n (mul (NVar x) (size p))))  *)
  end.

  Definition phase_order n (s:M1.state) :=
    let (h, p) := s in (H.prefix_index n h, flatten (NNum n) p).

  Import Aniceto.Graphs.Graph.

(*
  Lemma drf_sync:
    forall tids s,
    DRF (s, PSync) <-> SafeSt s.
  Proof.
    split; intros.
    + eauto using drf_to_safe_st.
    + unfold DRF.
      intros.
      induction H0.
      - 
  Qed.
*)

  Lemma safe_path_seq:
    forall p1 h1 h2 n m p2,
    NStep (add (NNum n) (size p1)) m ->
    M2.SafePath [phase_order n (h1, p1)] ->
    M2.SafePath [phase_order m (h2, p2)] ->
    M2.SafePath [(H.prefix_index n h1, M2.PSeq (flatten (NNum n) p1) (flatten (add (NNum n) (size p1)) p2))].
  Proof.
    induction p1; intros; simpl in *.
    - give_up.
    - 
  Qed.

  Lemma safe_path_inv_seq:
    forall h p1 p2,
    M1.SafePath (h, M1.PSeq p1 p2) ->
    M1.SafePath (h, p1) /\ exists h', M1.SafePath (h', p2).
  Proof.
  Admitted.

  Theorem correctness:
    forall s e n,
    NStep e n ->
    M1.SafePath s <-> M2.SafePath [phase_order n s].
  Proof.
    intros s.
    destruct s as (h, p).
    generalize dependent h.
    induction p; intros; simpl.
    - split; intros.
      + apply M1.safe_path_to_h_safe in H0.
        apply M2.safe_path_skip.
        apply H.safe_prefix_index.
        assumption.
      + apply M2.safe_path_inv_skip in H0.
        apply H.safe_prefix_index in H0.
        apply M1.safe_path_skip.
        assumption.
    - split; intros.
      + apply M1.safe_path_to_h_safe in H0.
        apply M2.safe_path_skip.
        apply H.safe_prefix_index.
        assumption.
      + apply M2.safe_path_inv_skip in H0.
        apply M1.safe_path_sync.
        apply H.safe_prefix_index in H0.
        assumption.
    - give_up.
    - split; intros.
      + (*  M1.SafePath (h, M1.PSeq p1 p2) ->  M1.SafePath (h, p1) /\ exists h' M1.SafePath(h', p2) *)
        apply safe_path_inv_seq in H0.
        destruct H0 as (Hp1, (h', Hp2)).
        eapply IHp1 in Hp1; eauto.
        assert (Hx: exists m, NStep  (add (NNum n) (size p1)) m). {
          give_up.
        }
        destruct Hx as (m, Hx).
        eapply IHp2 with (n:=m) in Hp2; eauto.
        
  Admitted.
End PO.
End PhaseOrdering.