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
Require Aniceto.Graphs.Graph.

Section LinWalk2.
  Import Aniceto.Graphs.Graph.
  Variable A:Type.
  Variable Edge: A * A -> Prop.

  Lemma walk2_inv_3:
    forall v1 vn w,
    Walk2 Edge v1 vn w ->
    (w = (v1,vn)::nil /\ Edge (v1, vn)) \/
    (exists v2, Edge (v1, v2) /\ exists w' e', w = (v1, v2) :: e' :: w' /\ Walk2 Edge v2 vn (e' :: w')).
  Proof.
    intros.
    destruct w. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    destruct w. {
      apply walk2_inv_pair in H.
      destruct H.
      subst.
      intuition.
    }
    right.
    apply walk2_inv in H.
    destruct H as (v2, (?, (?, ?))).
    exists v2.
    intuition.
    exists w.
    subst.
    exists p0.
    intuition.
  Qed.

  Variable edge_fun: forall a b c,
    Edge (a, b) ->
    Edge (a, c) ->
    b = c.

  Variable irreflexive:
    forall x,
    ~ clos_trans A (fun a b => Edge (a, b)) x x.

  Let walk2_irreflexive:
    forall x w, ~ Walk2 Edge x x w.
  Proof.
    intros.
    intros N.
    apply walk2_to_clos_trans with (R:=fun a b=>Edge (a,b)) in N. {
      apply irreflexive in N.
      contradiction.
    }
    tauto.
  Qed.

  (** If the edge behaves like a function, then there is only one path to
      arrive at each node. *)
  Lemma walk2_linear_fun:
    forall w1 a b w2,
    Walk2 Edge a b w1 ->
    Walk2 Edge a b w2 ->
    w1 = w2.
  Proof.
    induction w1; intros. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    apply walk2_inv_3 in H.
    destruct H as [(Hr,?)|(v2,(He, (w, (e,(Hx, Hy)))))]. {
      inversion Hr; subst; clear Hr.
      apply walk2_inv_3 in H0.
      destruct H0 as [(Hr, ?)|(v2,(?,(w,(e,(Hx,Hy)))))]. {
        subst.
        reflexivity.
      }
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    inversion Hx; subst; clear Hx.
    apply walk2_inv_3 in H0.
    destruct H0 as [(?,?)|(v3,(Hf,(w',(e',(Hx,Hz)))))]. {
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    subst.
    assert (v3 = v2) by eauto.
    subst.
    apply IHw1 in Hz; auto.
    inversion Hz; subst; clear Hz.
    reflexivity.
  Qed.
End LinWalk2.

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
  | step_for:
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

  Definition Safe (h:(state*proto)) :=
    let (s, _) := h in
    forall a1 a2,
      List.In a1 s -> List.In a2 s -> M.Safe a1 a2.

  Definition MStep := clos_refl_trans _ Step.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Lemma drf_to_safe:
    forall a,
    DRF a ->
    Safe a.
  Proof.
    unfold DRF; intros.
    apply H with (b:=a).
    apply rt_refl.
  Qed.

  Lemma drf_inv_skip:
    forall h,
    DRF (h, PSkip) ->
    Safe (h, PSkip).
  Proof.
    intros.
    unfold DRF in *.
    assert (MStep (h, PSkip) (h, PSkip)). {
      unfold MStep.
      apply rt_refl.
    }
    auto.
  Qed.

  Inductive Reachable : state*proto -> list (state*proto) -> Prop :=
  | reachable_nil:
    forall h,
    Reachable (h, PSkip) [(h, PSkip)]
  | reachable_cons:
    forall a b l,
    Step a b ->
    Reachable b l ->
    Reachable a (a :: l).

  Lemma m_step_inv:
    forall h a,
    MStep (h, PSkip) a ->
    a = (h, PSkip).
  Proof.
    intros.
    induction H using clos_refl_trans_ind_left.
    + reflexivity.
    + subst.
      inversion H0.
  Qed.

  Lemma step_fun:
    forall a b c,
    Step a b ->
    Step a c ->
    b = c.
  Proof.
    intros (h, p).
    generalize dependent h.
    induction p; intros;
    inversion H; inversion H0; subst; clear H H0; auto.
    - assert (a0 = a) by eauto using M.a_step_fun.
      subst.
      reflexivity.
    - assert (Hx: (s2, p3) = (s3, p6)) by eauto.
      inversion Hx; subst; clear Hx.
      reflexivity.
    - inversion H5.
    - inversion H9.
    - assert (l0 = l) by eauto using r_step_fun.
      subst.
      reflexivity.
    - inversion H9; subst; clear H9.
      reflexivity.
    - inversion H9.
    - inversion H9.
  Qed.

  Lemma step_m_step_inv:
    forall a b c,
    Step a b ->
    MStep a c ->
    MStep b c \/ a = c.
  Proof.
    intros.
    induction H0 using clos_refl_trans_ind_left.
    + auto.
    + destruct IHclos_refl_trans. {
        left.
        apply rt_trans with (y:=y); auto using rt_step.
      }
      subst.
      assert (b = z) by eauto using step_fun.
      subst.
      left.
      apply rt_refl.
  Qed.

  Lemma m_step_in_reachable:
    forall l a b,
    MStep a b ->
    Reachable a l ->
    List.In b l.
  Proof.
    induction l; intros. {
      inversion H0.
    }
    inversion H0; subst; clear H0. {
      inversion H; subst; clear H.
      + inversion H0.
      + apply in_eq.
      + apply m_step_inv in H0.
        subst.
        apply m_step_inv in H1.
        subst.
        auto using in_eq.
    }
    simpl.
    apply step_m_step_inv with (b:=b0) in H; auto.
    destruct H. {
      right.
      eapply IHl; eauto.
    }
    subst.
    auto.
  Qed.

  Inductive Value: (state * proto) -> Prop :=
  | value_def:
    forall h,
    Value (h, PSkip).

  Theorem progress:
    forall a,
    Value a \/ exists b, Step a b.
  Proof.
    intros (h, p).
    generalize dependent h.
    induction p; intros.
    - left; auto using value_def.
    - eauto using step_sync.
    - destruct M.progress with (e:=e) as (v, Hr).
      eauto using step_acc.
    - destruct (IHp1 h) as [Hv|(b, Hr)].
      + inversion Hv; subst; clear Hv.
        eauto using step_seq_skip.
      + destruct b as (h2, p3).
        eauto using step_seq_step.
    - give_up.
  Admitted. 
(*
  Lemma reachable_exists:
    forall a,
    exists l, Reachable a l.
  Proof.
    intros.
  Qed.
*)
  Lemma in_reachable_m_step:
    forall l a b,
    Reachable a l ->
    List.In b l ->
    MStep a b.
  Proof.
    induction l; intros. {
      contradiction.
    }
    destruct H0. {
      subst.
      inversion H; subst; clear H; apply rt_refl.
    }
    inversion H; subst; clear H. {
      contradiction.
    }
    assert (MStep b0 b) by auto.
    apply rt_trans with (y:=b0); auto using rt_step.
  Qed.

  Inductive Reach a b : Prop :=
  | reach_def:
    forall l,
    List.In b l ->
    Reachable a l ->
    Reach a b.

  Lemma reach_iff:
    forall a b,
    MStep a b <-> Reach a b.
  Proof.
    split; intros.
    - give_up.
  Admitted.
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
    Step ((s,PSkip)::h) h.

  Definition MStep := clos_refl_trans _ Step.

  Definition L1_Safe (h:(state*proto)) :=
    let (s, _) := h in
    forall a1 a2,
      List.In a1 s -> List.In a2 s -> M.Safe a1 a2.

  Definition Safe := Forall L1_Safe.

  Definition DRF a := forall b, MStep a b -> Safe b.

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
  | M1.PAcc a => M2.PAcc (M.e_prefix_index a n)
  | M1.PSeq p1 p2 => M2.PSeq (flatten p1 n) (flatten p2 (add n (size p1)))
  | M1.PFor x r p => M2.PDecl x r (flatten p (add n (mul (NVar x) (size p))))  
  | M1.PLoop x r p => M2.PSkip
  (* PDecl x r (flatten p (add n (mul (NVar x) (size p))))  *)
  end.

  Fixpoint annotate l n :=
  match l with
  | [] => []
  | a :: l => M.a_prefix_index a n :: annotate l n
  end.

  Lemma drf_skip:
    forall h n,
    M1.DRF (h, M1.PSkip) <-> M2.DRF [(annotate h n, M2.PSkip)].
  Proof.
    split; intros.
    - apply M1.drf_inv_skip in H.
      unfold M2.DRF.
      intros.
      
      apply rt_step.
      unfold M1.DRF, M2.DRF in *; intros.
      inversion H0; subst; clear H0.
      + 
  Qed.

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

  Corollary correctness:
    forall h p e n,
    NStep e n ->
    M1.DRF (h,p) <-> M2.DRF [(annotate h n, flatten p e)].
  Proof.
    induction p; intros; simpl.
    - give_up.
    - give_up.
    - give_up.
  Admitted.
End PO.
End PhaseOrdering.