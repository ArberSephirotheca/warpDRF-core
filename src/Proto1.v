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


Import ListNotations.

Module L1 (M:ACC).
  Module H := History M.

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

  Notation history := H.history.

  Definition state := (history * proto) % type.

  Inductive Step: state -> state -> Prop :=
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

  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, PSkip).

  Definition BStep := BigStep _ Step Value.

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

  Definition Safe (s:state) := let (h, _) := s in H.Safe h.

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

  Lemma safe_to_safe_history:
    forall h p,
    Safe (h, p) -> H.Safe h.
  Proof.
    auto.
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

(*
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
  Admitted. *)
(*
  Lemma reachable_exists:
    forall a,
    exists l, Reachable a l.
  Proof.
    intros.
  Qed.
*)
  Definition SafeStep := fun (p:state*state) => let (x,y) := p in Step x y /\ Safe x /\ Safe y.

  Import Aniceto.Graphs.Graph.

  Inductive SafePath : state -> Prop :=
  | safe_path_some:
    forall a b w,
    Walk2 SafeStep a b w ->
    Safe a ->
    Value b ->
    SafePath a
  | safe_path_skip:
    forall h,
    H.Safe h ->
    SafePath (h, PSkip).

  Lemma safe_step_not_skip:
    forall h x,
    ~ SafeStep ((h, PSkip), x).
  Proof.
    intros.
    intros N.
    destruct N as (A, (B, C)).
    inversion A.
  Qed.

  Lemma safe_path_to_h_safe:
    forall h p,
    SafePath (h, p) ->
    H.Safe h.
  Proof.
    intros.
    inversion H; subst; clear H.
    - assumption.
    - assumption.
  Qed.

  Lemma safe_path_inv_step:
    forall h p1 p2,
    SafePath (h, PSeq p1 p2) ->
    (p1 = PSkip /\ SafePath (h, p2)) \/
    (exists h' p1', SafeStep ((h, p1) , (h', p1')) /\ SafePath (h', PSeq p1' p2)).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply walk2_inv_3 in H0.
    destruct H0 as [(?,(Ha, (Hb, Hc)))|(s, ((Ha,(Hb,Hc)),(w',(e',(?,Hw)))))]. {
      subst.
      inversion Ha; subst; clear Ha. {
        inversion H2.
      }
      left.
      inversion H2; subst; clear H2.
      intuition.
      apply safe_path_skip.
      assumption.
    }
    inversion Ha; subst; clear Ha. {
      right.
      exists s2.
      exists p3.
      repeat split; auto.
      eapply safe_path_some; eauto.
    }
    left.
    intuition.
    eapply safe_path_some; eauto.
  Qed.

  Lemma safe_path_sync:
    forall h,
    H.Safe h ->
    SafePath (h, PSync).
  Proof.
    intros.
    remember (h, PSync) as v1.
    remember (@nil M.A, PSkip) as v2.
    apply safe_path_some with (b:=([], PSkip)) (w:=[(v1,v2)]); subst.
    - apply edge_to_walk2.
      unfold SafeStep.
      repeat split.
      + apply step_sync.
      + assumption.
      + apply H.safe_nil.
    - assumption.
    - apply value_def.
  Qed.

End Defs.
End L1.