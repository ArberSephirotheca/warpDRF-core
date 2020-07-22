(**
  Implements a predicate semantics similar to what is seen in
  GPUVerify OOPSLA12.
  *)

Require Import Coq.Classes.RelationPairs.
Require Import Coq.Lists.List.

Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import Tasks.
Require Import RangeList.
Require Hist.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).

  Inductive inst :=
  | Skip: inst
  | MemAcc: cond_access -> inst
  | Seq: inst -> inst -> inst
  | If: bexp -> inst -> inst -> inst
  | For: var -> range -> inst -> inst.

  Definition tdata := list (Map_VAR.t nat).

  Definition multi_subst {A:Type} (f:var -> nexp -> A -> A) (m:Map_VAR.t nat) :=
    @Map_VAR.fold nat A (fun x v e => f x (NNum v) e) m.

  Inductive TdAdd : tdata -> var -> nexp -> tdata -> Prop :=
  | td_add_nil:
    forall x n,
    TdAdd [] x n []
  | td_add_cons:
    forall x n td td' d n',
    TdAdd td x n td' ->
    NStep (multi_subst n_subst d n) n' ->
    TdAdd (d :: td) x n (Map_VAR.add x n' d :: td').

  Inductive StepAccess: tdata -> cond_access -> list (list access_val) -> Prop :=
  | step_access_nil:
    forall a,
    StepAccess [] a []
  | step_access_cons:
    forall a l l' v m,
    StepAccess l a l' ->
    CStep (multi_subst cond_access_subst m a, NNum (length l)) v ->
    StepAccess (m::l) a (v::l').
(*
  Definition MapsToAll x l m :=
    Map (fun m' n => @Map_VAR.MapsTo nat x n m') l m.
*)
  Inductive ThreadLocal: tdata -> nat -> Map_VAR.t nat -> Prop :=
  | thread_local_eq:
    forall x n d td,
    Map_VAR.MapsTo x n d ->
    ThreadLocal (d::td) (length td) d
  | maps_to_cons:
    forall t td d d',
    ThreadLocal td t d ->
    ThreadLocal (d'::td) t d.

  Definition MapsTo td t x n :=
    exists d, ThreadLocal td t d /\ Map_VAR.MapsTo x n d.

  Definition EvalForN td t e n :=
    exists d, ThreadLocal td t d /\ NStep (multi_subst n_subst d e) n.

  Definition EvalForR td t (r:range) (r':nat * nat) :=
    let (e1, e2) := r in
    let (n1, n2) := r' in
    EvalForN td t e1 n1 /\ EvalForN td t e2 n2.

  Definition HasIter (td: tdata) (r:range) : Prop :=
   exists t n1 n2, EvalForR td t r (n1, n2) /\ n1 < n2. 

  Definition EmptyIter td r :=
    forall t n1 n2, EvalForR td t r (n1, n2) -> n1 >= n2.

  Inductive Step: list (tdata * inst * bexp) * history -> list (tdata * inst * bexp) * history -> Prop :=

  | step_skip:
    forall m p l h,
    Step ((m, Skip, p)::l, h) (l,h)

  | step_access:
    (*
      Evaluate 'a' conditionally with 'p' using 'm'.
      The result is v.
    
      m(a,p) --> v
      ------------
      (m,a,p)::l, h --> l, (concat v) U h
    *)
    forall p b a h v l m,
    StepAccess m (a,b_and b p) v ->
    Step ((m, MemAcc (a,b), p)::l, h) (l, List.concat v ++ h)

  | step_seq:
    (*
      Evaluating sequence retains the same condition on each instruction.
      
      (m, i;; j, p)::l, h  -->  (m, i, p)::(m, j, p)::l, h
     *)
    forall p h i j l m,
    Step ((m, Seq i j, p)::l, h) ((m, i, p)::(m, j, p)::l, h)

  | step_if:
    (*
      A conditional 'if b then i else j'  adds condition 'b' to the then-branch
      and 'not b' to the else branch.
       
      (m, if b i j, p)::l, h --> (m, i, b & p) :: (m, i, ! b & p) :: l, h
     *) 
    forall p b i j h l m,
    Step ((m, If b i j, p)::l, h)
         ((m, i, BRel BAnd p b)::(m, j, BRel BAnd p (BNot b))::l, h)

  | step_for_seq:
    (*
      If there exists at least one task 't' where evaluating 'n1'
      results in a natural that is smaller than evaluating 'n2' for
      that same task 't'.
      
      Unfolding a loop corresponds to declaring a local variable 'x'
      which may depend on thread-local data, followed by running the
      loop with the successor of the lower bound, and 
    
      exists t, m(t) |- n1: n1'   m(t) |- n2 : n2'    n1' < n2'
      -------------------------------------------------------
      (m, for x (n1, n2) i, p) :: l, h
      -->
      (m[x := n1], i, p & n1 < n2) ::
      (m, for x (1 + n1, n2) i, p) :: l, h
     *)
    forall n1 n2 l i x h p m m',
    HasIter m (n1,n2) ->
    TdAdd m x n1 m' ->
    Step ((m, For x (n1,n2) i,p)::l, h)
         ((m', i, (b_and p (n_lt n1 n2)))::
          (m, For x (add (NNum 1) n1, n2) i,p)::l, h)
  | step_for_skip:
    (*
      forall t, m(t, n1) >= m(t, n2)
      -----------------------------------
      (m, for x (n1, n2) i, p) :: l, h --> l, h
    *)
    forall n1 n2 l i x h p m,
    EmptyIter m (n1,n2) ->
    Step ((m, For x (n1,n2) i,p)::l, h)
         (l, h)
  .


  Inductive PRun: tdata -> inst -> bexp -> history -> Prop :=

  | p_run_skip:
    forall td p,
    PRun td Skip p []

  | p_run_access:
    forall p b a v td,
    StepAccess td (a,b_and b p) v ->
    PRun td (MemAcc (a,b)) p (List.concat v)

  | p_run_seq:
    forall p i j td h1 h2,
    PRun td i p h1 ->
    PRun td j p h2 ->
    PRun td (Seq i j) p (h1 ++ h2)

  | p_run_if:
    forall p b i j h1 h2 td,
    PRun td i (BRel BAnd p b) h1 ->
    PRun td j (BRel BAnd p (BNot b)) h2 ->
    PRun td (If b i j) p (h1 ++ h2)

  | p_run_for_seq:
    forall n1 n2 h1 h2 i x p td td',
    HasIter td (n1,n2) ->
    TdAdd td x n1 td' ->
    PRun td' i (b_and p (n_lt n1 n2)) h1 ->
    PRun td (For x (add (NNum 1) n1, n2) i) p h2 ->
    PRun td (For x (n1, n2) i) p (h1 ++ h2)

  | p_run_for_skip:
    forall n1 n2 i x p td,
    EmptyIter td (n1,n2) ->
    PRun td (For x (n1,n2) i) p []
  .

  Fixpoint inline_if (p:bexp) (i:inst) : inst :=
    match i with
    | Skip => Skip
    | MemAcc (a, b) => MemAcc (a, b_and b p)
    | Seq i j => Seq (inline_if p i) (inline_if p j)
    | If b i j =>
      Seq (inline_if (b_and p b) i)
          (inline_if (b_and p (BNot b)) j)
    | For x r i => For x r (inline_if p i)
    end
  .


  Fixpoint inline_cond (p:bexp) (i:inst) : inst :=
    match i with
    | Skip => Skip
    | MemAcc (a, b) => MemAcc (a, b_and b p)
    | Seq i j => Seq (inline_cond p i) (inline_cond p j)
    | If b i j => If b (inline_cond p i) (inline_cond p j)
    | For x r i => For x r (inline_cond p i)
    end
  .

  Inductive Run: tdata -> inst -> history -> Prop :=

  | run_skip:
    forall td,
    Run td Skip []

  | run_access:
    forall a v td,
    StepAccess td a v ->
    Run td (MemAcc a) (List.concat v)

  | run_seq:
    forall i j td h1 h2,
    Run td i h1 ->
    Run td j h2 ->
    Run td (Seq i j) (h1 ++ h2)

  | run_if:
    forall b i j h1 h2 td,
    Run td (inline_if b i) h1 ->
    Run td (inline_if (BNot b) j) h2 ->
    Run td (If b i j) (h1 ++ h2)

  | run_for_seq:
    forall n1 n2 h1 h2 i x td td',
    HasIter td (n1,n2) ->
    TdAdd td x n1 td' ->
    Run td' (inline_if (n_lt n1 n2) i) h1 ->
    Run td (For x (add (NNum 1) n1, n2) i) h2 ->
    Run td (For x (n1, n2) i) (h1 ++ h2)

  | run_for_skip:
    forall n1 n2 i x td,
    EmptyIter td (n1,n2) ->
    Run td (For x (n1,n2) i) []
  .
End Defs.


Section Props.
  Context {A:Access}.

  Lemma multi_subst_cond_access_rw:
    forall d a b,
    multi_subst cond_access_subst d (a, b) =
    (multi_subst access_subst d a, multi_subst b_subst d b).
  Proof.
    intros d.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    generalize dependent a.
    generalize dependent b.
    clear Heql d.
    induction l; simpl; intros. {
      reflexivity.
    }
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_b_subst_brel_rw:
    forall d o b1 b2,
    multi_subst b_subst d (BRel o b1 b2)
    =
    BRel o (multi_subst b_subst d b1) (multi_subst b_subst d b2).
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    generalize dependent b1.
    generalize dependent b2.
    generalize dependent o.
    clear Heql d.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_b_subst_not_rw:
    forall d e,
    multi_subst b_subst d (BNot e)
    =
    BNot (multi_subst b_subst d e).
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    generalize dependent e.
    clear Heql d.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_b_subst_nrel_rw:
    forall d o e1 e2,
    multi_subst b_subst d (NRel o e1 e2)
    =
    NRel o (multi_subst n_subst d e1) (multi_subst n_subst d e2).
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    generalize dependent e1.
    generalize dependent e2.
    generalize dependent o.
    clear Heql d.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_n_subst_bin_rw:
    forall d o e1 e2,
    multi_subst n_subst d (NBin o e1 e2)
    =
    NBin o (multi_subst n_subst d e1) (multi_subst n_subst d e2).
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    generalize dependent e1.
    generalize dependent e2.
    generalize dependent o.
    clear Heql d.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_b_subst_bool_rw:
    forall d b,
    multi_subst b_subst d (BBool b) = BBool b.
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    clear Heql d.
    induction l; intros; simpl. {
      reflexivity.
    }
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma multi_n_subst_num_rw:
    forall d n,
    multi_subst n_subst d (NNum n) = NNum n.
  Proof.
    intros.
    unfold multi_subst.
    intros.
    rewrite Map_VAR.fold_1.
    remember (Map_VAR.elements (elt:=nat) d) as l.
    clear Heql d.
    induction l; intros; simpl. {
      reflexivity.
    }
    rewrite IHl.
    reflexivity.
  Qed.

  Definition BEquiv1 d e1 e2 :=
    BEq (multi_subst b_subst d e1) (multi_subst b_subst d e2).

  Lemma b_equiv1_refl d:
    forall e,
    BEquiv1 d e e.
  Proof.
    unfold BEquiv1.
    intros.
    reflexivity.
  Qed.

  Lemma b_equiv1_sym d:
    forall e1 e2,
    BEquiv1 d e1 e2 ->
    BEquiv1 d e2 e1.
  Proof.
    unfold BEquiv1.
    intros.
    symmetry.
    assumption.
  Qed.

  Lemma b_equiv1_trans d:
    forall e1 e2 e3,
    BEquiv1 d e1 e2 ->
    BEquiv1 d e2 e3 ->
    BEquiv1 d e1 e3.
  Proof.
    unfold BEquiv1.
    intros.
    transitivity (multi_subst b_subst d e2); auto.
  Qed.

  (** Register [BEq] in Coq's tactics. *)
  Section BEquiv1Setoid.
    Variable d : Map_VAR.t nat.
    Global Add Parametric Relation : _ (BEquiv1 d)
      reflexivity proved by (b_equiv1_refl d)
      symmetry proved by (b_equiv1_sym d)
      transitivity proved by (b_equiv1_trans d)
      as b_equiv1_setoid.

  End BEquiv1Setoid.

  Import Morphisms.

  Lemma n_step_multi_subst:
    forall d e n,
    NStep e n ->
    NStep (multi_subst n_subst d e) n.
  Proof.
    induction e; intros.
    - rewrite multi_n_subst_num_rw.
      assumption.
    - inversion H.
    - inversion H; subst; clear H.
      rewrite multi_n_subst_bin_rw.
      apply n_step_bin; auto.
  Qed.

  Lemma b_step_multi_subst:
    forall d e b,
    BStep e b ->
    BStep (multi_subst b_subst d e) b.
  Proof.
    induction e; intros.
    - rewrite multi_b_subst_bool_rw.
      assumption.
    - inversion H; subst; clear H.
      rewrite multi_b_subst_nrel_rw.
      auto using n_step_multi_subst, b_step_nrel.
    - rewrite multi_b_subst_brel_rw.
      inversion H; subst; clear H.
      auto using n_step_multi_subst, b_step_brel.
    - inversion H; subst; clear H.
      rewrite multi_b_subst_not_rw.
      auto using b_step_not.
  Qed.
(*
  Lemma b_step_multi_subst_eq:
    forall e1 e2 d b,
    BEquiv1 d e1 e2 ->
    BStep (multi_subst b_subst d e1) b ->
    BStep (multi_subst b_subst d e2) b.
  Proof.
    intros.
    apply H.
    assumption.
    induction e1; intros.
    - rewrite multi_b_subst_bool_rw in *.
      inversion H0; subst; clear H0.
      assert (Hx: BStep (BBool b0) b0) by auto using b_step_bool.
      apply H in Hx.
      auto using b_step_multi_subst.
    - rewrite multi_b_subst_nrel_rw in *.
    
    remember (multi_subst _ _ _) as m.
    generalize dependent e1.
    generalize dependent e2.
    generalize dependent b.
    induction m; intros.
    - inversion H0; subst; clear H0.
    induction e1; intros.
    - rewrite multi_b_subst_bool_rw in H0.
      inversion H0; subst; clear H0.
      assert (BStep e2 b0). {
        apply H.
        apply b_step_bool.
      }
      auto using b_step_multi_subst.
    - rewrite multi_b_subst_nrel_rw in H0.
      inversion H0; subst; clear H0.
  Qed.
*)
(*
  Global Instance multi_b_subst_proper_1 d: Proper ((BEquiv1 d) ==> (BEquiv1 d)) (multi_subst b_subst d).
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - split; intros.
      + 
  Qed.

  Global Instance b_equiv1_proper_1: Proper (eq ==> BEq ==> BEq ==> iff) BEquiv1.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - split; intros.
      + 
  Qed.
*)

  Lemma b_equiv1_and_true_l d:
    forall b,
    BEquiv1 d (BRel BAnd b (BBool true)) b.
  Proof.
    intros.
    unfold BEquiv1.
    split; intros.
    - rewrite multi_b_subst_brel_rw in H.
      rewrite multi_b_subst_bool_rw in H.
      rewrite b_eq_and_true in H.
      assumption.
    - rewrite multi_b_subst_brel_rw.
      rewrite multi_b_subst_bool_rw.
      rewrite b_eq_and_true.
      assumption.
  Qed.

  Lemma c_step_b_eq:
    forall d a b1 b2 n v,
    BEquiv1 d b1 b2 ->
    CStep (a, multi_subst b_subst d b1, n) v ->
    CStep (a, multi_subst b_subst d b2, n) v.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    + apply H in H5.
      auto using c_step_true.
    + apply H in H5.
      eauto using c_step_false.
  Qed.

  Definition BEquiv td b1 b2 :=
    forall d,
    List.In d td ->
    BEquiv1 d b1 b2.

  Lemma b_equiv_refl d:
    forall b,
    BEquiv d b b.
  Proof.
    unfold BEquiv; intros.
    reflexivity.
  Qed.

  Lemma b_equiv_sym d:
    forall b1 b2,
    BEquiv d b1 b2 ->
    BEquiv d b2 b1.
  Proof.
    unfold BEquiv.
    intros.
    symmetry.
    auto.
  Qed.

  Lemma b_equiv_trans td:
    forall b1 b2 b3,
    BEquiv td b1 b2 ->
    BEquiv td b2 b3 ->
    BEquiv td b1 b3.
  Proof.
    unfold BEquiv; intros.
    transitivity (b2); auto.
  Qed.

  (** Register [BEquiv] in Coq's tactics. *)
  Section BEquivSetoid.
    Variable td : list (Map_VAR.t nat).
    Global Add Parametric Relation : _ (BEquiv td)
      reflexivity proved by (b_equiv_refl td)
      symmetry proved by (b_equiv_sym td)
      transitivity proved by (b_equiv_trans td)
      as b_equiv_setoid.

  End BEquivSetoid.

  Lemma b_equiv_and_true_l d:
    forall b,
    BEquiv d (BRel BAnd b (BBool true)) b.
  Proof.
    unfold BEquiv.
    intros.
    apply b_equiv1_and_true_l.
  Qed.

  Lemma b_equiv_inv_cons_1:
    forall a td b1 b2,
    BEquiv (a :: td) b1 b2 ->
    BEquiv td b1 b2.
  Proof.
    unfold BEquiv; intros.
    auto using in_cons.
  Qed.

  Lemma b_equiv_inv_cons_2:
    forall a td b1 b2,
    BEquiv (a :: td) b1 b2 ->
    BEquiv1 a b1 b2.
  Proof.
    unfold BEquiv; intros.
    auto using in_eq.
  Qed.

  Lemma step_access_b_eq:
    forall td a v b1 b2,
    BEquiv td b1 b2 ->
    StepAccess td (a, b1) v ->
    StepAccess td (a, b2) v.
  Proof.
    induction td; intros; inversion H0; subst; clear H0.
    - apply step_access_nil.
    - apply step_access_cons.
      + eauto using b_equiv_inv_cons_1.
      + rewrite multi_subst_cond_access_rw in *.
        eapply c_step_b_eq; eauto using b_equiv_inv_cons_2.
  Qed.

  Global Instance p_run_proper_1 d: Proper (eq * (BEquiv d) ==> eq ==> iff) (StepAccess d).
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - destruct x as (a1, c1).
      destruct y as (a2, c2).
      destruct H as (?, Hb).
      unfold RelCompFun in *.
      simpl in *.
      subst.
      eauto using step_access_b_eq.
    - destruct x as (a1, c1).
      destruct y as (a2, c2).
      destruct H as (?, Hb).
      unfold RelCompFun in *.
      simpl in *.
      subst.
      symmetry in Hb.
      eauto using step_access_b_eq.
  Qed.
(*
  Lemma b_equiv_p_run:
    forall d i e1 l,
    PRun d i e1 l ->
    forall e2,
    BEquiv d e1 e2 ->
    PRun d i e2 l.
  Proof.
    intros d i e1 l H.
    induction H; intros.
    - apply p_run_skip.
    - apply p_run_access.
      eapply step_access_b_eq; eauto.
      rewrite H0.
      rewrite H0 in H.
  Qed.

  Global Instance p_run_proper_1 d: Proper (eq ==> eq ==> BEquiv d ==> eq ==> iff) PRun.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    - 
*)
(*
  Lemma inline_if_1:
    forall td i b m,
    PRun td i b m ->
    PRun td (inline_if b i) (BBool true) m.
  Proof.
    intros.
    induction H; simpl.
    - apply p_run_skip.
    - apply p_run_access.
      apply step_access_b_eq with (b1:=b_and b p); auto.
      rewrite b_equiv_and_true_l.
      reflexivity.
    - apply p_run_seq; auto.
    - unfold b_and.
      apply p_run_seq; auto.
    - eapply p_run_for_seq; eauto.
      admit.
    - eapply p_run_for_skip; eauto.
  Admitted.
*)
(*
  Lemma inline_if_2:
    forall td i b m,
    PRun td (inline_if b i) (BBool true) m ->
    PRun td j b m.
  Proof.
    intros td i b m H; induction 
    induction i; simpl; intros.
    - inversion H; subst; clear H.
      apply p_run_skip.
    - destruct c as (a, b').
      inversion H; subst; clear H.
      apply p_run_access.
      rewrite b_equiv_and_true_l in *.
      assumption.
    - inversion H; subst; clear H.
      apply p_run_seq; auto.
    - inversion H; subst; clear H.
      apply p_run_if; auto.
    - inversion H; subst; clear H.
      + eapply p_run_for_seq; eauto.
        * apply IHi
  Qed.
*)

  Lemma inline_if_inv_skip:
    forall b i,
    inline_if b i = Skip ->
    i = Skip.
  Proof.
    intros b [] Hi; simpl in Hi; inversion Hi.
    - reflexivity.
    - destruct c.
      inversion Hi.
  Qed.

  Lemma inline_if_inv_acc:
    forall b i a,
    inline_if b i = MemAcc a ->
    exists e p,
    i = MemAcc (e, p) /\ a = (e, BRel BAnd p b).
  Proof.
    intros.
    destruct i; intros; simpl in H; inversion H.
    destruct c as (e, b').
    inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma inline_if_inv_seq:
    forall b i i1 i2,
    inline_if b i = Seq i1 i2 ->
    exists i1' i2',
    (i = Seq i1' i2' /\ i1 = inline_if b i1' /\ i2 = inline_if b i2')
    \/
    (exists b',
      i = If b' i1' i2' /\
      i1 = inline_if (BRel BAnd b b') i1' /\
      i2 = inline_if (BRel BAnd b (BNot b')) i2').
  Proof.
    intros.
    destruct i; simpl in H; inversion H; subst.
    - destruct c; inversion H.
    - exists i3, i4.
      left.
      eauto.
    - exists i3, i4.
      eauto.
  Qed.

  Lemma inline_if_inv_if:
    forall b b' i' i j,
    inline_if b' i' <> If b i j.
  Proof.
    intros.
    intros N.
    destruct i'; simpl in *; inversion N.
    destruct c; inversion N.
  Qed.

  Lemma inline_if_inv_for:
    forall b i' r i1 x,
    inline_if b i' = For x r i1 ->
    exists i1',
    i' = For x r i1' /\ i1 = inline_if b i1'.
  Proof.
    intros.
    destruct i'; simpl in *; inversion H; subst; clear H.
    - destruct c; inversion H1.
    - eauto.
  Qed.

  Lemma inline_if_2:
    forall td b i p h,
    PRun td (inline_if b i) p h ->
    PRun td i (b_and b p) h.
  Proof.
    intros.
    remember (inline_if _ _) as j.
    generalize dependent b.
    generalize dependent i.
    induction H; intros; symmetry in Heqj.
    - apply inline_if_inv_skip in Heqj.
      subst.
      apply p_run_skip.
    - apply inline_if_inv_acc in Heqj.
      destruct Heqj as (e, (p', (Hx, Hy))).
      inversion Hy; subst; clear Hy.
      apply p_run_access.
      unfold b_and in *.
      admit.
    - apply inline_if_inv_seq in Heqj.
      destruct Heqj as (i1', (i2', [(?, (?, ?))|(b', (?, (?,?)))])); subst.
      + auto using p_run_seq.
      + unfold b_and in *.
        apply p_run_if.
        * assert (IHPRun1 := IHPRun1 _ _ eq_refl).
          admit.
        * assert (IHPRun2 := IHPRun2 _ _ eq_refl).
          admit.
    - apply inline_if_inv_if in Heqj.
      contradiction.
    - apply inline_if_inv_for in Heqj.
      destruct Heqj as (i', (?, ?)).
      subst.
      assert (IHPRun1 := IHPRun1 _ _ eq_refl).
      eapply p_run_for_seq; eauto.
      admit.
    - apply inline_if_inv_for in Heqj.
      destruct Heqj as (i1', (?, ?)).
      subst.
      auto using p_run_for_skip.
  Admitted.

  Lemma run_to_p_run:
    forall td i m b,
    Run td (inline_if b i) m ->
    PRun td i b m.
  Proof.
    intros.
    remember (inline_if _ _) as j.
    generalize dependent Heqj.
    generalize dependent b.
    generalize dependent i.
    induction H; intros; symmetry in Heqj.
    - apply inline_if_inv_skip in Heqj.
      subst.
      apply p_run_skip.
    - apply inline_if_inv_acc in Heqj.
      destruct Heqj as (e, (p, (?, ?))).
      subst.
      apply p_run_access; auto.
    - apply inline_if_inv_seq in Heqj.
      destruct Heqj as (i1', (i2', [(?,(?,?))|(b',(?,(?,?)))])); subst.
      * auto using p_run_seq.
      * auto using p_run_if.
    - apply inline_if_inv_if in Heqj.
      contradiction.
    - apply inline_if_inv_for in Heqj.
      destruct Heqj as (i1', (?, ?)).
      subst.
      assert (IHRun1 := IHRun1 _ _ eq_refl).
      assert (IHRun2 := IHRun2 (For x (add (NNum 1) n1, n2) i1') b eq_refl).
      eapply p_run_for_seq; eauto.
      apply inline_if_2.
      auto.
    - apply inline_if_inv_for in Heqj.
      destruct Heqj as (i1', (?, ?)).
      subst.
      eapply p_run_for_skip; auto.
  Qed.

  Lemma p_run_to_run:
    forall i td m b,
    PRun td i b m ->
    Run td (inline_if b i) m.
  Proof.
    intros i td m b H; induction H; simpl.
    - apply run_skip.
    - apply run_access; auto.
    - eauto using run_seq.
    - simpl.
      apply run_seq; auto.
    - eapply run_for_seq; eauto.
      admit.
    - apply run_for_skip; auto.
  Admitted.

  Fixpoint inline_bound n i :=
  match i with
  | Skip | MemAcc _ => i
  | Seq i j => Seq (inline_bound n i) (inline_bound n j)
  | If b i j => If b (inline_bound n i) (inline_bound n j)
  | For x (e1, e2) i =>
    For x (NNum 0, NNum n)
      (If
        (BRel BAnd
          (NRel NLe e1 (NVar x))
          (NRel NLt (NVar x) e2))
        (inline_bound n i)
        Skip)
  end.
(*

  Lemma undep_1:
    forall td i p h,
    PRun td i p h ->
    forall n j,
    Undep n i j ->
    PRun td j p h.
  Proof.
    intros td i h p H.
    induction H; intros.
    - inversion H; subst; clear H.
      apply p_run_skip.
    - inversion H0; subst; clear H0.
      auto using p_run_access.
    - inversion H1; subst; clear H1.
      eauto using p_run_seq.
    - inversion H1; subst; clear H1.
      apply p_run_if; eauto.
    - inversion H3; subst; clear H3.
      eapply p_run_seq; eauto.
  Qed.
  *)
End Props.
