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

Module C1.
Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Acc: access_exp -> inst
  | Seq : inst -> inst -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.

  Fixpoint i_subst x v i :=
  match i with
  | Acc a => Acc (access_subst x v a)  
  | Seq p1 p2 => Seq (i_subst x v p1) (i_subst x v p2)
  | For y r p2 => if VAR.eq_dec x y then i else (For y (r_subst x v r) (i_subst x v p2)) 
  | Loop y r p2 => if VAR.eq_dec x y then i else (Loop x r (i_subst x v p2)) 
  | Skip => Skip
  end.

  Import Hist.

  Notation history := Hist.history.

  Definition state := (history * inst) % type.

  Variable TID_COUNT: nat.
  Variable TID : var.

  (** Parallelize an access for [n] tasks. *)

  Inductive GenAccess a: nat -> list (list access_val) -> Prop :=
  | gen_access_zero:
    forall v,
    access_step (access_subst TID 0 a, NNum 0) v ->
    GenAccess a 0 [v]
  | gen_access_succ:
    forall n v l,
    GenAccess a n l ->
    access_step (access_subst TID (S n) a, NNum (S n)) v ->
    GenAccess a (S n) (v::l).

  Inductive Step: state -> state -> Prop :=
  | step_acc:
    forall s e v,
    GenAccess e TID_COUNT v ->
    Step (s, Acc e) (List.flat_map id v ++ s, Skip)
  | step_seq_step:
    forall s1 s2 p1 p2 p3,
    Step (s1, p1) (s2, p2) ->
    Step (s1, Seq p1 p3) (s2, Seq p2 p3)
  | step_seq_skip:
    forall s p,
    Step (s, Seq Skip p) (s, p)
  | step_for:
    forall x r p l s,
    RStep r l ->
    Step (s, For x r p) (s, Loop x l p)
  | step_loop_step:
    forall s x n l p,
    Step (s, Loop x (n::l) p) (s, Seq (i_subst x n p) (Loop x l p))
  | step_loop_skip:
    forall s x p,
    Step (s, Loop x [] p) (s, Skip).

  Inductive Value: state -> Prop :=
  | value_def:
    forall h,
    Value (h, Skip).

(*  Definition BStep := BigStep _ Step Value. *)

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

  Definition Safe (s:state) := let (h, _) := s in Hist.Safe h.

  Definition MStep := clos_refl_trans _ Step.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Definition BStep := BigStep _ Step Value.
(*
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
(*
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
*)
(*
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
*)
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
(*
  Inductive SafePath : state -> state -> Prop :=
  | safe_path_some:
    forall a h,
    Reaches SafeStep a (h, PSkip) ->
    SafePath a (h, PSkip)
  | safe_path_skip:
    forall h,
    H.Safe h ->
    SafePath (h, PSkip) (h, PSkip).

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
    forall h1 h2 p,
    SafePath (h1, p) h2 ->
    H.Safe h1.
  Proof.
    intros.
    inversion H; subst; clear H.
    - apply reaches_to_in_fst in H0.
      destruct H0 as ((v1, v2), (Hi, Hj)).
      inversion Hj; simpl in *; subst;
        destruct Hi as (?, (?, ?));
        auto.
    - assumption.
  Qed.
*)*)
End C1.
End C1.

Module Examples.
  Section Defs.
  Import C1.
  (* BAD: *)
  (* for x < n {
       [tid + x] 
     } *)

  Definition TID := variable 0.

  Definition TID_NUM := 2.

  Notation b_step := (BStep TID_NUM TID).
  Notation step := (Step TID_NUM TID).

  Let x := variable 1.
  Let i1 := Acc (add (NVar TID) (NVar x), BBool true).
  Definition BAD :=
    For x (NNum 0, NNum 2) i1.

  Lemma step1 : step ([], BAD) ([], Loop x [0;1] i1).
  Proof.
    apply step_for.
    apply r_step_def with (n1:=0) (n2:=2); auto using n_step_num.
    apply range_list_cons; auto.
    apply range_list_cons; auto.
    apply range_list_nil; auto.
  Qed.

  Lemma step2 : step ([], Loop x [0;1] i1) ([], Seq (i_subst x 0 i1) (Loop x [1] i1)).
  Proof.
    apply step_loop_step.
  Qed.

  Lemma step3 : step ([], Seq (i_subst x 0 i1) (Loop x [1] i1)) ([], Seq Skip (Loop x [1] i1)).
  Proof.
    apply step_seq_step.
    compute.
    remember ((NBin NPlus (NVar (variable 0)) (NNum 0), BBool true)) as e.
    Import OneDim.
    remember {|tid:=1; index := 1|} as a1.
    remember {|tid:=0; index := 0|} as a0.
    assert (GenAccess TID e TID_NUM [[a0]; [a1]]). {
      subst.
      apply gen_access_succ.
    }
    apply step_acc.
  Qed.

(*
  Goal BStep ([], BAD) ([], Skip).
    apply big_step_reaches.
    + apply Graph.reaches_def with (w:=[]).
      - apply Graph.walk2_def.
        * 
*)
  (* GOOD: *)
  (*
    for x < n {
      [x] if tid == x
    }
   *)

  Definition GOOD :=
    let x := variable 1 in
    For x (NNum 0, NNum 2) (
      Acc (NVar x, NRel NEq (NVar TID) (NVar x))
    ).

End Examples.
