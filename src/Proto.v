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
Import ListNotations.
(*
    Lemma clos_refl_trans_ind_left2 :
      forall (A:Type) (R:relation A) (x:A) (P:A -> Prop), P x ->
      (forall y z, P y -> R x y -> clos_refl_trans_1n A R y z -> P z) ->
  	forall z:A, clos_refl_trans_1n A R x z -> P z.
    Proof.
      intros.
      revert H H0.
      induction H1.
      - auto.
      - intros.
        apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n; auto; intros.
        + clear H2.
           eapply H2; eauto.
        intros.
        eapply H2; eauto using Coq.Relations.Relation_Operators.rt1n_refl.
        eauto using Coq.Relations.Relation_Operators.rt1n_trans. 
    Qed.
*)
    Lemma clos_refl_trans_ind_left :
      forall (A:Type) (R:relation A) (x:A) (P:A -> Prop), P x ->
  	(forall y z:A, clos_refl_trans A R x y -> P y -> R y z -> P z) ->
  	forall z:A, @clos_refl_trans A R x z -> P z.
    Proof.
      intros.
      revert H H0.
      induction H1; intros; auto with sets.
      - apply H1 with x; auto with sets.

      - apply IHclos_refl_trans2.
        + apply IHclos_refl_trans1; auto with sets.

        + intros.
          apply H0 with y0; auto with sets.
          apply rt_trans with y; auto with sets.
    Qed.

  Definition MappingRel {A:Type} (R:relation A) (f:A->A) :=
    forall a b,
    R a b <-> R (f a) (f b).

  Definition MappingProp {A:Type} (P:A -> Prop) (f:A->A) :=
     forall x,
     P x <-> P (f x).
 
  Definition Impl {A:Type} (R:relation A) (P:A -> Prop) :=
    forall a b,
    P a -> R a b -> P b.
(*
  Lemma safe_map_to_drf:
    forall f a,
    SafeMap f ->
    P a ->
    P (f a).
*)

  Definition RelProp {A:Type} (P:A -> Prop) R a :=
    forall b,
    clos_refl_trans A R a b ->
    P b.

  Definition RelFProp {A:Type} (P:A -> Prop) R (f:A->A) a :=
    forall b,
    clos_refl_trans A R (f a) (f b) ->
    P (f b).

  Lemma rel_prop_trans:
    forall A P R x y,
    RelProp P R x ->
    clos_refl_trans A R x y ->
    RelProp P R y.
  Proof.
    intros.
    induction H0 using clos_refl_trans_ind_left. {
      assumption.
    }
    unfold RelProp in *; intros.
    assert (clos_refl_trans A R x z). {
      eauto using rt_step, rt_trans.
    }
    assert (clos_refl_trans A R x b) by eauto using rt_trans.
    auto.
  Qed.

  Lemma rel_prop_refl:
    forall A P R a,
    @RelProp A P R a ->
    P a.
  Proof.
    unfold RelProp.
    intros.
    assert (clos_refl_trans A R a a) by auto using rt_refl.
    auto.
  Qed.

  Lemma clos_refl_trans_prop:
    forall (A:Type) (R:relation A) (P:A -> Prop) (f: A -> A),
    MappingRel R f ->
    MappingProp P f ->
    forall a,
    RelProp P R a ->
    RelFProp P R f a.
  Proof.
    intros ? ? ? ?.
    intros Hm.
    intros Hr.
    intros ? ?.
    intros ? Hy.
    remember (f b) as c.
    induction Hy using clos_refl_trans_ind_left.
    - assert (P a). {
        eapply rel_prop_refl; eauto.
      }
      apply Hr in H0.
      assumption.
    - subst.
      assert (clos_refl_trans A R (f a) (f b)). {
        apply rt_trans with (y:=y).
        + assumption.
        + auto using rt_step.
      }
      assert (P (f a)). {
        assert (Hpa: P a). {
          eapply rel_prop_refl; eauto.
        }
        apply Hr in Hpa.
        assumption.
      }
  Abort.      


Section Defs.

  Inductive nbin :=
  | NPlus
  | NMinus
  | NMult
  | NDiv
  | NMod.

  Inductive nexp :=
  | NNum : nat -> nexp
  | NVar : var -> nexp
  | NBin : nbin ->  nexp -> nexp -> nexp.

  Definition add := NBin NPlus.
  Definition sub := NBin NMinus.
  Definition mul := NBin NMult.
  Definition div := NBin NDiv.
  Definition mod := NBin NMod.

  Inductive nrel := NEq | NLe | NLt.

  Inductive brel := BOr | BAnd.

  Inductive bexp :=
  | BBool: bool -> bexp
  | NRel : nrel -> nexp -> nexp -> bexp
  | BRel : brel -> bexp -> bexp -> bexp
  | BNot : bexp -> bexp.

  Inductive mode := R | W.

  Definition mode_eqb m1 m2 :=
  match m1, m2 with
  | R, R | W, W => true
  | _, _ => false
  end.

  Definition range := (nexp * nexp) % type.

  Inductive proto :=
  | PSkip
  | PSync
  (* location @ range: mode *)
  | PAcc: loc -> list nexp -> mode -> proto
  | PSeq : proto -> proto -> proto
  (* Non-deterministic loop *)
  | PDecl : var -> range -> proto -> proto
  | PFor : var -> range -> proto -> proto.
End Defs.

Section SO.
  Record access := {
    access_index: list nexp;
    access_mode : mode; 
    access_tid : tid;
  }. 

  Inductive ModeConflict: mode -> mode -> Prop :=
  | mode_conflict_l:
    forall o,
    ModeConflict W o
  | mode_conflict_r:
    forall o,
    ModeConflict o W.

  Inductive Racy: access -> access -> Prop :=
  | racy_def:
    forall t1 t2 i m1 m2,
    t1 <> t2 ->
    ModeConflict m1 m2 ->
    Racy {| access_index := i; access_mode := m1; access_tid := t1 |}
         {| access_index := i; access_mode := m2; access_tid := t2 |}.

  Inductive SafeAcc: access -> access -> Prop :=
  | safe_acc_def_eq_task:
    forall t m1 m2 i1 i2,
    SafeAcc {| access_tid := t; access_mode := m1; access_index := i1 |}
            {| access_tid := t; access_mode := m2; access_index := i2 |}
  | safe_acc_def_r:
    forall t1 t2 i1 i2,
    SafeAcc {| access_tid := t1; access_mode := R; access_index := i1 |}
            {| access_tid := t2; access_mode := R; access_index := i2 |}
  | safe_acc_def_neq_index:
    forall t1 t2 i1 i2 m1 m2,
    i1 <> i2 ->
    SafeAcc {| access_tid := t1; access_mode := m1; access_index := i1 |}
            {| access_tid := t2; access_mode := m2; access_index := i2 |}.

  Definition history := list access.

  Definition state := Map_LOC.t history.

  Definition SafeHist h :=
    forall a1 a2, List.In a1 h -> List.In a2 h -> SafeAcc a1 a2. 

  Definition SafeSt s := forall l h, Map_LOC.MapsTo l h s -> SafeHist h.

  Definition Safe (a:state * proto) := let (s,_) := a in SafeSt s.

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

  Definition eval_nbin o :=
  match o with
  | NPlus => Nat.add
  | NMinus => Nat.sub
  | NMult => Nat.mul
  | NDiv => Nat.div
  | NMod => Nat.modulo
  end.

  Inductive NStep: nexp -> nat -> Prop :=
  | nstep_num:
    forall n,
    NStep (NNum n) n
  | nstep_bin:
    forall n1 n2 o e1 e2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep (NBin o e1 e2) (eval_nbin o n1 n2). 

  Definition eval_nrel (o:nrel) :=
  match o with
  | NEq => Nat.eqb
  | NLt => Nat.ltb
  | NLe => Nat.leb
  end.

  Definition eval_brel (o:brel) :=
  match o with
  | BOr => orb
  | BAnd => andb
  end.

  Inductive BStep: bexp -> bool -> Prop :=
  | bstep_bool:
    forall b,
    BStep (BBool b) b
  | bstep_nrel:
    forall e1 e2 n1 n2 o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    BStep (NRel o e1 e2) (eval_nrel o n1 n2)
  | bstep_brel:
    forall e1 e2 b1 b2 o,
    BStep e1 b1 ->
    BStep e2 b2 ->
    BStep (BRel o e1 e2) (eval_brel o b1 b2).

  Inductive RStep: range -> (nat * nat) -> Prop :=
  | rstep_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    RStep (e1, e2) (n1, n2).

  Fixpoint n_subst x (v:nat) e :=
  match e with
  | NBin o e1 e2 => NBin o (n_subst x v e1) (n_subst x v e2)
  | NVar y => if VAR.eq_dec x y then (NNum v) else e  
  | NNum n => NNum n
  end.

  Fixpoint b_subst x v e :=
  match e with
  | NRel o e1 e2 => NRel o (n_subst x v e1) (n_subst x v e2)
  | BRel o e1 e2 => BRel o (b_subst x v e1) (b_subst x v e2)
  | BNot b => BNot (b_subst x v b)
  | BBool b => BBool b
  end.

  Fixpoint i_subst x v l :=
  match l with
  | [] => []
  | n :: l => n_subst x v n :: i_subst x v l
  end.

  Definition NonemptyRange (r:nat * nat) := let (n1, n2) := r in n1 < n2. 

  Definition EmptyRange (r:nat * nat) := let (n1, n2) := r in n1 >= n2.

  Definition InRange n (r:nat * nat) := let (n1, n2) := r in n >= n1 /\ n < n2.

  Definition inc (r:nat * nat) :=
  let (n1, n2) := r in
  (NNum (S n1), NNum n2).

  Definition r_subst x v (r:range) :=
  let (n1, n2) := r in
  (n_subst x v n1, n_subst x v n2).

  Fixpoint p_subst x v p :=
  match p with
  | PAcc l i m => PAcc l (i_subst x v i) m  
  | PSeq p1 p2 => PSeq (p_subst x v p1) (p_subst x v p2)
  | PDecl y r p2 => if VAR.eq_dec x y then p else (PDecl y (r_subst x v r) (p_subst x v p2))
  | PFor y r p2 => if VAR.eq_dec x y then p else (PFor y (r_subst x v r) (p_subst x v p2)) 
  | PSkip => PSkip
  | PSync => PSync 
  end.


  Variable tids : list tid.

  Variable tid : var.

  Definition empty := Map_LOC.empty history.

  Inductive Step: (state * proto) -> (state * proto) -> Prop :=
  | step_sync:
    forall s,
    Step (s, PSync) (empty, PSkip)
  | step_acc:
    forall s m idx l,
    Step (s, PAcc l idx m) (p_add l idx m tids s, PSkip)
  | step_seq_step:
    forall s1 s2 p1 p2 p3,
    Step (s1, p1) (s2, p2) ->
    Step (s1, PSeq p1 p3) (s2, PSeq p2 p3)
  | step_seq_skip:
    forall s p,
    Step (s, PSeq PSkip p) (s, p)
  | step_decl_step:
    forall s x n1 n p r,
    RStep r n ->
    InRange n1 n ->
    Step (s, PDecl x r p) (s, p_subst x n1 p)
  | step_decl_skip:
    forall s x n p r,
    RStep r n ->
    EmptyRange n ->
    Step (s, PDecl x r p) (s, PSkip)
  | step_for_step:
    forall r n1 n2 s x p,
    RStep r (n1, n2) ->
    NonemptyRange (n1, n2) ->
    Step (s, PFor x r p) (s, PSeq (p_subst x n1 p) (PFor x (inc (n1, n2)) p))
  | step_for_skip:
    forall r r' s x p,
    RStep r r' ->
    EmptyRange r' ->
    Step (s, PFor x r p) (s, PSkip).

  Definition MStep := (clos_refl_trans _ Step).



  Inductive UnfoldFor (x:var) : (nat * nat) -> proto -> proto -> Prop := 
  | unfold_unfold_zero:
    forall n1 n2 p,
    n1 >= n2 ->
    UnfoldFor x (n1, n2) p PSkip
  | unfold_for_step:
    forall n1 n2 q p,
    n1 < n2 ->
    UnfoldFor x (S n1, n2) p q ->
    UnfoldFor x (n1, n2) p (PSeq (p_subst x n1 p) q).

  Lemma n_step_fun:
    forall n n1 n2,
    NStep n n1 ->
    NStep n n2 ->
    n1 = n2.
  Proof.
    induction n; intros;
    inversion H; inversion H0; subst; clear H H0.
    - trivial.
    - assert (n5 = n7) by eauto.
      assert (n6 = n8) by eauto.
      subst.
      trivial.
  Qed.  

  Lemma r_step_fun:
    forall r n1 n2,
    RStep r n1 ->
    RStep r n2 ->
    n1 = n2.
  Proof.
    intros.
    destruct n1, n2.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n = n1) by eauto using n_step_fun.
    assert (n0 = n2) by eauto using n_step_fun.
    subst.
    reflexivity.
  Qed.
  Section Asd.
    Import Coq.omega.Omega.
  Lemma unfold_inv_empty:
    forall n1 n2 x p q,
    n2 <= n1 ->
    UnfoldFor x (n1, n2) p q ->
    q = PSkip.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - trivial.
    - omega.
  Qed.
  
  Lemma step_for_inv_empty:
    forall s n1 n2 r x p a,
    n2 <= n1 ->
    RStep r (n1, n2) ->
    Step (s, PFor x r p) a ->
    a = (s, PSkip).
  Proof.
    intros.
    inversion H1; subst; clear H1; auto.
    apply r_step_fun with (n1:=(n1,n2)) in H7; auto.
    inversion H7; subst; clear H7.
    unfold NonemptyRange in *.
    omega.
  Qed.

  Lemma r_step_num:
    forall n1 n2,
    RStep (NNum n1, NNum n2) (n1, n2).
  Proof.
    intros.
    repeat constructor.
  Qed.

  Lemma step_for_simpl_r_step:
    forall r n1 n2 a x p s,
    RStep r (n1, n2) ->
    Step (s, PFor x r p) a ->  
    Step (s, PFor x (NNum n1, NNum n2) p) a.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - apply r_step_fun with (n1:=(n1, n2)) in H6; auto.
      inversion H6; subst; clear H6.
      apply step_for_step; auto using r_step_num.
    - apply r_step_fun with (n1:=(n1, n2)) in H6; auto; subst.
      eapply step_for_skip; eauto using r_step_num.
  Qed.

  Lemma step_for_inv_sub:
    forall n n1 n2 x p a s,
    n2 - n1 = S n ->
    Step (s, PFor x (NNum n1, NNum n2) p) a ->
    a = (s, PSeq (p_subst x n1 p) (PFor x (NNum (S n1), NNum n2) p)).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - unfold NonemptyRange in *.
      inversion H6; subst; clear H6.
      simpl.
      inversion H3; subst; clear H3.
      inversion H5; subst; clear H5.
      reflexivity.
    - assert (r' = (n1, n2)). {
        assert (Hx := r_step_num n1 n2).
        apply r_step_fun with (n1:=(n1, n2)) in H6; auto.
      }
      subst.
      unfold EmptyRange in *.
      apply Nat.sub_0_le in H7.
      rewrite H7 in *.
      inversion H.
  Qed.

  Lemma unfold_for_inv_sub:
    forall n1 n2 n a p x,
    n2 - n1 = S n ->
    UnfoldFor x (n1, n2) p a ->
    exists q, a = PSeq (p_subst x n1 p) q /\
    UnfoldFor x (S n1, n2) p q.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - apply Nat.sub_0_le in H5.
      rewrite H5 in *.
      inversion H.
    - exists q.
      intuition.
  Qed.
(*
  Lemma drf_mapping_1:
    forall s f,
    SafeStep s ->
    SafeMap f ->
    SafeStep (f s).
  Proof.
    unfold SafeStep, SafeMap; intros.
    destruct H as (safe, step).
    split; auto.
    intros.
  Qed.
*)
(*
  Lemma unfold_for_spec_1:
    forall n n1 n2 p q x,
    n2 - n1 = n ->
    UnfoldFor x (n1, n2) p q ->
    forall s a,
    Step (s, PFor x (NNum n1, NNum n2) p) a -> MStep (s, q) a.
  Proof.
    induction n; intros. {
      apply PeanoNat.Nat.sub_0_le in H.
      apply unfold_inv_empty in H0; auto.
      subst.
      apply step_for_inv_empty with (n1:=n1) (n2:=n2) in H1; subst;
        auto using r_step_num.
      apply rt_refl.
    }
    eapply step_for_inv_sub in H1; eauto; subst.
    eapply unfold_for_inv_sub in H0; eauto.
    destruct H0 as (q', (Hx, Hy)).
    subst.
    destruct n1. {
      rewrite Nat.sub_0_r in *.
      subst.
      eapply IHn; eauto.
    }
    eapply IHn; eauto.
    destruct n1. {
      rewrite Nat.sub_0_r in *.
      subst.
      SearchAbout(_ - 0 = _).
    inversion H; subst; clear H.
    destruct n1. {
      inversion H5; subst; clear H5.
      inversion H1; subst; clear H1. {
        inversion H2; subst; clear H2.
        + 
      }
      inversion H2; subst; clear H2.
    }
    inversion 
    intros H1 H2.
    induction H2; intros.
    - inversion H0; subst; clear H0.
      + apply r_step_fun with (n1:=(n1,n2)) in H8; auto.
        inversion H8; subst; clear H8.
        unfold NonemptyRange in *.
        omega.
      + apply r_step_fun with (n1:=(n1,n2)) in H8; auto.
    - 
    generalize dependent H0.
    generalize dependent H1.
    induction H1 using clos_refl_trans_ind_left; intros.
    - inversion H0; subst; clear H0.
      + inversion H2; subst; clear H2. {
          apply r_step_fun with (n1:=(n1, n2)) in H7; auto.
          inversion H7; subst; clear H7.
          unfold NonemptyRange in *.
          omega.
        }
        apply rt_refl.
      + 
  Qed.

  Lemma unfold_for_spec_1:
    forall x p n r q,
    RStep r n ->
    UnfoldFor x n p q ->
    forall s a b,
    Step (s, PFor x r p) a ->
    MStep a b ->
    MStep (s, q) b.
*)

  Inductive StepReach :  (state * proto) -> list (state * proto) -> Prop :=
  | step_reach_skip:
    forall s,
    StepReach (s, PSkip) []
  | step_reach_sync:
    forall s x,
    Step (s, PSync) x ->
    StepReach (s, PSync) [x]
  | step_reach_acc:
    forall m idx l x s,
    Step (s, PAcc l idx m) x ->
    StepReach (s, PAcc l idx m) [x]
  | step_reach_seq_skip:
    forall s p,
    StepReach (s, PSeq PSkip p) [(s, p)]
  | step_reach_seq_seq:
    forall s1 p1 p3 x,
    p1 <> PSkip ->
    StepReach (s1, p1) x ->
    StepReach (s1, PSeq p1 p3) (List.map (fun (b:state * proto) => let (s2,p2) := b in (s2, PSeq p2 p3)) x)
  | step_reach_decl_skip:
    forall r n x p s h,
    RStep r n ->
    EmptyRange n ->
    Step (s, PDecl x r p) h ->
    StepReach (s, PDecl x r p) [h]
  | step_reach_decl_step:
    forall r x p l1 l2 s n1 n2,
    StepReach (s, PDecl x (NNum (S n1), NNum n2) p) l1 ->
    RStep r (n1, n2) ->
    InRange n1 (n1, n2) ->
    StepReach (s, p_subst x n1 p) l2 ->
    StepReach (s, PDecl x r p) (l1++l2)
  | step_reach_for_skip:
    forall r n x p s h,
    RStep r n ->
    EmptyRange n ->
    Step (s, PFor x r p) h ->
    StepReach (s, PFor x r p) [h]
  | step_reach_for_step:
    forall r x p s n1 n2 l,
    RStep r (n1, n2) ->
    InRange n1 (n1, n2) ->
    StepReach (s, PSeq (p_subst x n1 p) (PFor x r p)) l ->
    StepReach (s, PFor x r p) l.

  Lemma step_reach_1:
    forall a b l,
    In b l ->
    StepReach a l ->
    Step a b.
  Proof.
    intros (s, p).
    generalize dependent s.
    induction p; intros;
    inversion H0; subst; clear H0.
    - contradiction.
    - destruct H; subst; auto.
      contradiction.
    - destruct H; subst; auto.
      contradiction.
    - destruct H; subst; try constructor.
      contradiction.
    - apply in_map_iff in H.
      destruct H as ((s2, p3), (Hx, Hy)).
      subst.
      eapply IHp1 in Hy; eauto.
      constructor; auto.
    - destruct H; subst; auto; contradiction.
    - apply in_app_or in H.
      give_up.
      (*
      destruct H as [Hx|Hx]. {
        apply step_decl.
        eapply IHp in H5; eauto.
      }*)
  Abort.
(*
  Inductive Reachable: state * proto -> state * proto -> Prop :=
  | reachable_refl:
    forall p,
    Reachable p p
  | reachable_sync:
    forall s,
    Reachable (s, PSync) (empty, PSkip)
  | reachable_seq_skip:
    forall s p2 x,
    Reachable (s, p2) x ->
    Reachable (s, PSeq PSkip p2) x
  | reachable_seq_step:
    forall s1 s1' p1 p1' p2 x,
    Step (s1, p1) (s1', p1') ->
    Reachable (s1', PSeq p1' p2) x ->
    Reachable (s1, PSeq p1 p2) x
  | reachable_acc:
    forall s m idx l,
    Reachable (s, PAcc l idx m) (p_add l idx m tids s, PSkip)
  | reachable_decl_skip:
    forall x r n s p,
    RStep r n ->
    EmptyRange n ->
    Reachable (s, PDecl x r p) (s, PSkip)
  | reachable_decl_step:
    forall x r s p n1 n,
    RStep r n ->
    InRange n1 n ->
    Reachable (s, PDecl x r p) (s, p_subst x n1 p)
  | rechable_for_skip:
    forall n x r p s,
    RStep r n ->
    EmptyRange n -> 
    Reachable (s, PFor x r p) (s, PSkip)
  | reachable_for_step:
    forall x r s p y lo hi,
    RStep r (lo,hi) ->
    InRange lo (lo, hi) ->
    Reachable (s, PSeq (p_subst x lo p) (PFor x r p)) y ->
    Reachable (s, PFor x r p) y.

  Lemma mstep_to_reachable:
    forall x y,
    MStep x y -> Reachable x y.
  Proof.
    intros.
    induction H.
    - inversion H; subst; clear H; repeat constructor.
      + econstructor; try eauto; constructor.
      + eapply reachable_decl_step; eauto.
      + econstructor; eauto.
      + econstructor; eauto.
        * unfold NonemptyRange, InRange in *.
          auto.
        * econstructor; eauto.
  Qed.

*)
(*
  Let reachable_sync_spec:
    forall s p,
    MStep (s, PSync) p <-> Reachable (s, PSync) p.
  Proof.
    split; intros.
    - induction H using clos_refl_trans_ind_left.
      + apply reachable_refl.
      + inversion IHclos_refl_trans; subst; clear IHclos_refl_trans;
        inversion H0; subst; clear H0.
        apply reachable_sync.
    - inversion H; subst; clear H.
      + apply rt_refl.
      + apply rt_step.
        apply step_sync.
  Qed.
*)
  
(*
  Lemma clos_refl_trans_ind_left2:
       forall (A : Type) (R : Relation_Definitions.relation A) (x : A) (P : A -> Prop),
       P x ->
       (forall y z : A, R x y -> P y -> clos_refl_trans A R y z -> P z) ->
       forall z : A, clos_refl_trans A R x z -> P z.
  Proof.
    intros A R x P Hp.
    intros.
    assert (Hx := clos_refl_trans_ind_left A R x P Hp).
    apply Hx; auto; clear Hx.
    intros.
    clear H0 z.
    apply clos_refl_trans_ind_left in Hp with (r:=.
    rewrite clos_rt_rt1n_iff in H1.
    inversion H1; subst; clear H1.
    - assumption.
    - apply clos_rt_rt1n_iff in H3.
      apply H0 with (y:=y); auto.
    
    induction H1.
    - eapply H0; eauto.
    induction H1 using clos_refl_trans_ind_left; auto.
    assert (Hx: clos_refl_trans A R0 x z). {
      rewrite clos_rt_rtn1_iff in *.
      apply Coq.Relations.Relation_Operators.rtn1_trans with (y:=y); auto.
    }
    rewrite clos_rt_rt1n_iff in Hx.
    inversion Hx; subst; clear Hx; auto.
    apply clos_rt_rt1n_iff in H4.
    eapply H0; eauto.
  Qed.
*)
(*  Require Import Coq.Program.Equality. *)
(*
  Let big_step_seq_spec:
    forall s p1 p2 p,
    MStep (s, PSeq p1 p2) p <-> Reachable (s, PSeq p1 p2) p.
  Proof.
    split; intros.
    - clear reachable_sync_spec.
      dependent induction H.
      + inversion H; subst; clear H. {
          eapply reachable_seq_step; eauto using reachable_refl.
        }
        apply reachable_seq_skip; auto using reachable_refl.
      + apply reachable_refl.
      + inversion H; subst; clear H. {
          assert (Hx := IHclos_refl_trans1 s p1 p2).
      inversion H; subst; clear H. {
        apply 
        apply IHclos_refl_trans_1n.
        * apply reachable_sync_spec.
        * inversion H
       using clos_refl_trans_ind_left2; auto using reachable_refl.
      inversion H; subst; clear H.
      + apply reachable_seq_step with (p1' := p3) (s1':=s2); auto.
        
      
      clos_refl_trans_ind_left
      clos_refl_trans_ind_right
      induction H using clos_refl_trans_ind_left; auto using reachable_refl.
      apply clos_rt_rt1n_iff in H.
      inversion H; subst; clear H.
      + apply reachable_refl.
      + 
      induction H.
      + destruct x.
        apply reachable_refl.
      + 
      induction H using clos_refl_trans_ind_left; auto using reachable_refl.
      
      inversion H; subst; clear H.
      + destruct z as (s', p').
        eapply reachable_seq_step; eauto.
      
      apply reachable_seq_step.
      inversion IHclos_refl_trans; subst; clear IHclos_refl_trans.
      + clear H.
        inversion H0; subst; clear H0. {
          apply reachable_seq_step.
          eapply reachable_seq_step; eauto.
  Qed.
  *)
  

  Definition DRF (a:state * proto) : Prop := forall b, MStep a b -> Safe b.

(*
  Definition SafeStep s :=
    SafeSt s /\ (forall p s' p', Step (s, p) (s', p') -> SafeSt s').

  Definition SafeMap f :=
    forall s, SafeSt s -> SafeSt (f s).
*)

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

End SO.

Section PO.
  Fixpoint size p :=
  match p with
  | PAcc _ _ _
  | PSkip => NNum 0
  | PSync => NNum 1
  | PDecl x n p => size p
  | PSeq p1 p2 => add (size p1) (size p2)
  | PFor x (lo, hi) p => mul (sub hi lo) (size p) 
  end.

  Fixpoint flatten p n :=
  match p with
  | PSkip => PSkip
  | PSync => PSkip
  | PAcc l i m => PAcc l (n::i) m
  | PDecl x r p => PDecl x r (flatten p n)
  | PSeq p1 p2 => PSeq (flatten p1 n) (flatten p2 (add n (size p1)))
  | PFor x r p => PDecl x r (flatten p (add n (mul (NVar x) (size p))))  
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