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
Require Conc1.

Import ListNotations.

Module C2.
  Section Defs.
  Context {A:Access}.

  Inductive inst :=
  | Skip
  | Acc: access_exp * nexp -> inst -> inst
  | Decl : var -> range -> inst -> inst -> inst
  | Branch : var -> list nat -> inst -> inst -> inst.

  Inductive Var (x:var) : inst -> Prop :=
  | var_acc:
    forall p i,
    Var x i ->
    Var x (Acc p i)
  | var_decl_eq:
    forall r i1 i2,
    Var x (Decl x r i1 i2)
  | var_decl_r:
    forall r y i1 i2,
    Var x i2 ->
    Var x (Decl y r i1 i2)
  | var_decl_l:
    forall r i1 i2 y,
    Var x i1 ->
    Var x (Decl y r i1 i2)
  | var_branch_eq:
    forall l i1 i2,
    Var x (Branch x l i1 i2)
  | var_branch_l:
    forall y i1 i2 l,
    Var x i1 ->
    Var x (Branch y l i1 i2)
  | var_branch_r:
    forall y i1 i2 l,
    Var x i2 ->
    Var x (Branch y l i1 i2).

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Acc (a, e) j => Acc (access_subst x v a, n_subst x v e) (i_subst x v j)  
  | Decl y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Decl y (r_subst x v r) i2' (i_subst x v i3)
  | Branch y r i2 i3 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Branch y r i2' (i_subst x v i3)
  end.

  Fixpoint seq (i1 i2:inst) :=
  match i1 with
  | Skip => i2
  | Acc e i3 => Acc e (seq i3 i2)
  | Decl x r i3 i4 => Decl x r i3 (seq i4 i2)
  | Branch x r i3 i4 => Branch x r i3 (seq i4 i2)
  end.

  Notation history := Hist.history.

  Definition state1 := (history * inst) % type.

  Inductive state :=
  | Empty: state
  | Leaf: (history * inst) -> state
  | Par: state -> state -> state.

  Definition is_par p :=
  match p with
  | Par _ _ => true
  | _ => false
  end.

  Definition is_par_l_leaf s :=
   match s with
   | Par (Leaf (_, Skip)) _ => true
   | _ => false
   end.

  Inductive Step: state -> state -> Prop :=
  (* Leaf reduction *)

  | step_decl:
    forall x r c1 c2 l h,
    RStep r l ->
    Step (Leaf (h, Decl x r c1 c2)) (Leaf (h, Branch x l c1 c2))

  | step_acc:
    forall h e v c,
    access_step e v ->
    Step (Leaf (h, Acc e c)) (Leaf (v ++ h, c))

  (* Par reduction *)
  | step_par_l:
    (*

            s1 --> s2
      ---------------------
      s1 || s3 ==> s2 || s3

     *)
    forall s1 s2 s3,
    is_par s1 = false ->
    Step s1 s2 -> 
    Step (Par s1 s3) (Par s2 s3)

  | step_par_empty:
    (*

      {} || s ==> s

     *)
    forall s,
    Step (Par Empty s) s

  | step_par_r:
    (*

                     s1 --> s2
        -----------------------------------
        (h, skip) || s1 ==> (h, skip) || s2

     *)
    forall h s1 s2,
    Step s1 s2 ->
    Step (Par (Leaf (h, Skip)) s1) (Par (Leaf (h, Skip)) s2)

  | step_par_par:
    forall s1 s2 s3,
    Step (Par (Par s1 s2) s3) (Par s1 (Par s2 s3))


  (* Branch reduction *)
  | step_branch_nil:
    (*

    (h, x \in [] p) ==> {}

     *)
    forall h x i1 i2,
    Step (Leaf (h, Branch x [] i1 i2)) Empty
  | step_branch_cons:
    forall h x n l c1 c2,
    (*
    
    (h, x \in n::l p) ==> (h, p[x=n]) || (h, x \in l p)
    
     *)
    Step
      (Leaf (h, Branch x (n::l) c1 c2))
      (Par (Leaf (h, seq (i_subst x (NNum n) c1) c2)) (Leaf (h, Branch x l c1 c2))).

  Inductive Run: inst -> list history -> Prop :=
  | run_skip:
    Run Skip [[]]
  | run_access:
    forall i e v hs,
    access_step e v ->
    Run i hs ->
    Run (Acc e i) (prepend v hs)
  | run_decl:
    forall r l i1 i2 x hs,
    RStep r l ->
    Run (Branch x l i1 i2) hs ->
    Run (Decl x r i1 i2) hs
  | run_branch_cons:
    forall x n l i1 i2 hs1 hs2,
    Run (seq (i_subst x (NNum n) i1) i2) hs1 ->
    Run (Branch x l i1 i2) hs2 ->
    Run (Branch x (n::l) i1 i2) (hs1 ++ hs2)
  | run_branch_nil:
    forall x i1 i2 hs,
    Run i2 hs ->
    Run (Branch x [] i1 i2) hs.

  Inductive DoLoop : var -> list nat -> inst -> inst -> list (list history) -> Prop :=
  | do_loop_nil:
    forall i1 i2 x hs,
    Run i2 hs ->
    DoLoop x [] i1 i2 [hs]
  | do_loop_cons:
    forall x n l i1 i2 hss hs,
    Run (seq (i_subst x (NNum n) i1) i2) hs ->
    DoLoop x l i1 i2 hss ->
    DoLoop x (n::l) i1 i2 (hs::hss).

  Let run_branch_to_do_loop:
    forall x l i1 i2 hs,
    Run (Branch x l i1 i2) hs ->
    exists hss, hs = List.concat hss /\ DoLoop x l i1 i2 hss.
  Proof.
    intros.
    remember (Branch _ _ _ _).
    generalize dependent x.
    generalize dependent i1.
    generalize dependent i2.
    generalize dependent l.
    induction H; intros; inversion Heqi; subst; clear Heqi. {
      assert (IHRun2 := IHRun2 _ _ _ _ eq_refl).
      destruct IHRun2 as (hss, (?, Hd)).
      exists (hs1::hss).
      split. {
        simpl.
        subst.
        auto.
      }
      apply do_loop_cons; auto.
    }
    exists [hs].
    simpl.
    split. {
      auto with *.
    }
    auto using do_loop_nil.
  Qed.

  Let do_loop_inv_1:
    forall x l i1 i2 hss,
    DoLoop x l i1 i2 hss ->
    forall n,
    List.In n l ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      exists hs.
      auto using List.in_eq.
    }
    eapply IHl in H8; eauto.
    destruct H8 as (hs', (Hi,Hj)).
    eauto using in_cons.
  Qed.

  Let run_branch_inv:
    forall x l i1 i2 hs,
    Run (Branch x l i1 i2) hs ->
    exists hss, hs = List.concat hss /\
    forall n,
    List.In n l ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss.
  Proof.
    intros.
    apply run_branch_to_do_loop in H.
    destruct H as (hss, (?, Ha)).
    exists hss.
    split; auto.
    intros.
    eapply do_loop_inv_1; eauto.
  Qed.

  Lemma run_decl_inv:
    forall x e1 e2 i1 i2 hs,
    Run (Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\ (
    (n1 >= n2 /\ Run i2 hs)
    \/
    (
    exists hss, hs = List.concat hss /\
    forall n,
    n1 <= n < n2 ->
    exists hs, Run (seq (i_subst x (NNum n) i1) i2) hs /\ List.In hs hss)
     ).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst.
    exists n1.
    exists n2.
    repeat (split; auto).
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    apply run_branch_inv in H6.
    destruct H6 as (hss, (?, Hc)).
    exists hss.
    split; auto.
    intros.
    apply (Ha n) in H0.
    apply Hc in H0.
    assumption.
  Qed.


(*
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    ((n1 >= n2 /\ C2.Run i2 hs)
    \/
    forall n,
    n1 <= n < n2 ->
    exists hs2,
    incl hs2 hs /\ C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) hs2).
  Proof.
    intros.
    inversion H5; subst.
    exists n1.
    exists n2.
    split; auto.
    split; auto.
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    intros.
    apply (Ha n) in H.
    eapply in_branch_inv in H6; eauto.
  Qed.
*)
  Definition red_par f s1 s2 :=
    match s1, s2 with
    | Empty, s => Some s
    | Par s1' s2', _ => Some (Par s1' (Par s2' s2))
    | Leaf (_, Skip), _ =>
      match f s2 with
      | Some s2 => Some (Par s1 s2)
      | None => None
      end
    | _, _ =>
      match f s1 with
      | Some s1 => Some (Par s1 s2)
      | None => None
      end
    end.

  Inductive RedPar f: state -> state -> state -> Prop :=
  | red_par_1:
    forall s,
    RedPar f Empty s s
  | red_par_2:
    forall h s1 s2,
    f s1 = Some s2 ->
    RedPar f (Leaf (h, Skip)) s1 (Par (Leaf (h, Skip)) s2)
  | red_par_3:
    forall s1 s2 s3,
    RedPar f (Par s1 s2) s3 (Par s1 (Par s2 s3))
  | red_par_4:
    forall s1 s2 s3,
    is_par s1 = false ->
    f s1 = Some s3 ->
    RedPar f s1 s2 (Par s3 s2).

  Lemma red_par_inv_some:
    forall f s1 s2 s3,
    red_par f s1 s2 = Some s3 ->
    RedPar f s1 s2 s3.
  Proof.
    unfold red_par; intros.
    destruct s1.
    - inversion H.
      clear H.
      constructor.
    - destruct p as (?, []) eqn:Hy; subst;
        destruct s2; inversion H; subst; clear H; try constructor;
        destruct (f _) eqn:Hf; inversion H1; subst; clear H1; constructor; auto;
        intros N; inversion N.
    - inversion H; subst; clear H.
      constructor.
  Qed.

  Lemma some_to_red_par f (f_none: f Empty = None) (f_leaf_skip: forall h, f (Leaf (h, Skip)) = None) :
    forall s1 s2 s3,
    RedPar f s1 s2 s3 ->
    red_par f s1 s2 = Some s3.
  Proof.
    intros.
    inversion H; simpl; auto; clear H.
    - subst.
      rewrite H0.
      reflexivity.
    - subst.
      destruct s1; simpl in *; try rewrite H0; auto.
      + rewrite f_none in *.
        inversion H1.
      + destruct p as (h, []); simpl in *; destruct (f s2) eqn:He;
        try rewrite f_leaf_skip in *; try inversion H1; rewrite H2; auto.
      + inversion H0.
  Qed.


  Definition red_leaf (s:history * inst) :=
    let (h, c) := s in
    match c with
    | Acc e c1 =>
      match access_eval1 e with
      | Some v => Some (Leaf (v ++ h, c1))
      | None => None
      end
    | Decl x r c1 c2 =>
      match r_step r with
      | Some l => Some (Leaf (h, Branch x l c1 c2))
      | _ => None
      end
    | Branch x (n::l) c1 c2 =>
      Some (Par (Leaf (h, seq (i_subst x (NNum n) c1) c2)) (Leaf (h, Branch x l c1 c2)))
    | Branch _ [] _ _ => Some Empty 
    | Skip => None 
    end.

  Inductive RedLeaf: (history * inst) -> state -> Prop :=
  | red_leaf_acc:
    forall h e v c,
    access_eval1 e = Some v ->
    RedLeaf (h, Acc e c) (Leaf (v ++ h, c))
  | red_leaf_decl:
    forall h x r i1 i2 l,
    r_step r = Some l ->
    RedLeaf (h, Decl x r i1 i2) (Leaf (h, Branch x l i1 i2))
  | red_leaf_branch_cons:
    forall h l i1 i2 n x,
    RedLeaf (h, Branch x (n::l) i1 i2)
        (Par (Leaf (h, seq (i_subst x (NNum n) i1) i2)) (Leaf (h, Branch x l i1 i2)))
  | red_leaf_branch_nil:
    forall h x i1 i2,
    RedLeaf (h, Branch x [] i1 i2) Empty.

  Lemma red_leaf_inv_some:
    forall s1 s2,
    red_leaf s1 = Some s2 ->
    RedLeaf s1 s2.
  Proof.
    intros.
    destruct s1 as (h, []); simpl in *.
    - inversion H.
    - destruct (access_eval1 _) eqn:Hp; inversion H; subst; clear H.
      constructor; auto.
    - destruct (r_step _) eqn:Hr; inversion H; subst.
      constructor; auto.
    - destruct l; inversion H; subst; constructor.
  Qed.

  Fixpoint step (s:state) : option state :=
  match s with
  | Leaf s => red_leaf s
  | Par s1 s2 => red_par step s1 s2
  | Empty => None
  end.

  Inductive Value: state -> Prop :=
  | value_skip:
    forall h,
    Value (Leaf (h, Skip))
  | value_par:
    forall s1 s2,
    Value s1 ->
    Value s2 ->
    Value (Par s1 s2).

  Theorem step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    induction s1; intros; simpl in *.
    - inversion H.
    - apply red_leaf_inv_some in H.
      inversion H; subst; clear H; constructor;
        auto using b_step_to_prop, access_eval1_to_step, r_step_to_prop, n_step_to_prop.
    - apply red_par_inv_some in H.
      inversion H; subst; clear H; try (constructor; auto).
  Qed.

  Theorem prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    induction s1; intros; simpl; inversion H; clear H; simpl; auto; subst.
    - apply prop_to_r_step in H1.
      rewrite H1.
      reflexivity.
    - apply access_step_to_eval1 in H1.
      rewrite H1.
      reflexivity.
    - apply IHs1_1 in H4.
      apply some_to_red_par; auto.
      constructor; auto.
    - apply IHs1_2 in H3.
      rewrite H3.
      reflexivity.
  Qed.

  Definition BStep := BigStep _ Step Value.


  Lemma seq_inv_skip:
    forall i1 i2,
    seq i1 i2 = Skip ->
    i1 = Skip /\ i2 = Skip.
  Proof.
    intros.
    destruct i1; simpl in *; subst; auto;
    inversion H.
  Qed.

  Lemma seq_seq_rw:
    forall i1 i2 i3,
    seq (seq i1 i2) i3 = (seq i1 (seq i2 i3)).
  Proof.
    induction i1; intros; simpl in *.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite <- IHi1_2.
      reflexivity.
    - rewrite <- IHi1_2.
      reflexivity.
  Qed.

  Lemma seq_nil_rw:
    forall i,
    seq i Skip = i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
    - rewrite IHi2.
      reflexivity.
  Qed.

  Lemma run_seq:
    forall i1 hs1,
    Run i1 hs1 ->
    forall i2 hs2,
    Run i2 hs2 ->
    Run (seq i1 i2) (prod hs1 hs2).
  Proof.
    intros i1 hs1 H.
    induction H; intros.
    - simpl.
      rewrite prepend_nil.
      rewrite app_nil_r.
      assumption.
    - assert (Hx := IHRun _ _ H1).
      simpl.
      rewrite <- prepend_prod.
      apply run_access; auto.
    - apply IHRun in H1.
      simpl.
      eapply run_decl; eauto.
    - rewrite <- prod_app.
      simpl.
      apply run_branch_cons; eauto.
      remember (i_subst _ _ _).
      assert (Hx := IHRun1 _ _ H1).
      rewrite seq_seq_rw in *.
      assumption.
    - simpl.
      apply run_branch_nil.
      auto.
  Qed.

  Lemma run_fun:
    forall i hs1,
    Run i hs1 ->
    forall hs2, Run i hs2 ->
    hs1 = hs2.
  Proof.
    intros i hs1 H.
    induction H; intros.
    - inversion H; subst; clear H; auto.
    - inversion H1; subst; clear H1.
      erewrite IHRun; eauto.
      assert (v0 = v) by eauto using access_step_fun.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun; eauto.
      subst.
      erewrite IHRun; eauto.
    - inversion H1; subst; clear H1.
      erewrite IHRun1; eauto.
      erewrite IHRun2; eauto.
    - inversion H0; subst; clear H0.
      eauto.
  Qed.

  Ltac run_clean :=
    repeat match goal with
    | [ H: Run [] _ |- _ ] => inversion H; subst; clear H
    | [ H: Hist.Safe [] |- _ ] => clear H
    | [ H: Run [Skip] _ |- _ ] => inversion H; subst; clear H
    | [ H: Run _ _ Skip _ |- _] => inversion H; subst; clear H
    | [ H1: access_step ?e ?v1,
        H2: access_step ?e ?v2 |- _ ] =>
          let H := fresh in
          assert (H: v2 = v1) by eauto using access_step_fun;
          rewrite H in *; clear H;
          clear H1
    | [ H1: RStep ?r ?l1,
        H2:RStep ?r ?l2 |- _ ] =>
          let H := fresh in
          assert (H: l2 = l1) by eauto using r_step_fun;
          rewrite H in *; clear H;
          clear H1
    end.

  Lemma run_inv_seq_1:
    forall i1 hs1,
    Run i1 hs1 ->
    forall i2 hs2 hs,
    Run i2 hs2 ->
    Run (seq i1 i2) hs ->
    hs = prod hs1 hs2.
  Proof.
    intros i1 hs1 H.
    induction H; intros; simpl in *.
    - rewrite prepend_nil.
      rewrite app_nil_r.
      eapply run_fun; eauto.
    - inversion H2; subst; clear H2.
      run_clean.
      apply IHRun with (hs2:=hs2) in H7; auto.
      subst.
      rewrite prepend_prod.
      reflexivity.
    - inversion H2; subst; clear H2.
      run_clean.
      apply IHRun with (hs2:=hs2) in H9; auto.
    - inversion H2; subst; clear H2.
      assert (IHRun2 := IHRun2 _ _ _ H1 H10); subst.
      rewrite <- seq_seq_rw in H9.
      assert (IHRun1 := IHRun1 _ _ _ H1 H9).
      subst.
      rewrite <- prod_app.
      reflexivity.
    - inversion H1; subst; clear H1.
      eapply IHRun in H6; eauto.
  Qed.

  Lemma run_inv_seq_2:
    forall i1 i2 hs,
    Run (seq i1 i2) hs ->
    exists hs1 hs2, Run i1 hs1 /\ Run i2 hs2.
  Proof.
    intros i1 i2 hs H.
    remember (seq _ _) as i.
    generalize dependent i1.
    generalize dependent i2.
    induction H; intros; symmetry in Heqi.
    - apply seq_inv_skip in Heqi.
      destruct Heqi.
      subst.
      exists [[]].
      exists [[]].
      split; auto using run_skip.
    - destruct i1; simpl in *; try inversion Heqi; subst; try clear Heqi.
      + exists [[]].
        exists (prepend v hs).
        split; auto using run_skip, run_access.
      + edestruct IHRun as (hs1, (hs2, (?, ?))); eauto.
        exists (prepend v hs1).
        exists hs2.
        split; auto using run_access.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; eauto using run_skip, run_decl.
      }
      destruct (IHRun i0 (Branch x l i1 i3_2) eq_refl) as (hs1, (hs2, (Hr1, Hr2)));
      clear IHRun.
      exists hs1.
      exists hs2.
      split; eauto using run_decl.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        clear H1.
        exists [[]].
        exists (hs1 ++ hs2).
        split; auto using run_skip.
        apply run_branch_cons; auto.
      }
      remember (i_subst _ _ _).
      destruct (IHRun1 i0 (seq i i3_2)) as (hsa, (hsb, (Hr1, Hr2))). {
        rewrite seq_seq_rw.
        reflexivity.
      }
      clear IHRun1.
      destruct (IHRun2 i0 (Branch x l i1 i3_2) eq_refl) as (hsa1, (hsb1, (Hra, Hrb))).
      assert (hsb = hsb1) by eauto using run_fun.
      clear Hrb.
      exists (hsa ++ hsa1).
      exists hsb.
      subst.
      split; auto using run_branch_cons.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; auto using run_skip, run_branch_nil.
      }
      destruct (IHRun _ _ eq_refl) as (hs1, (hs2, (?, ?))).
      exists hs1.
      exists hs2.
      split; auto using run_branch_nil.
  Qed.

  Lemma run_inv_seq:
    forall i1 i2 hs,
    Run (seq i1 i2) hs ->
    exists hs1 hs2, hs = prod hs1 hs2 /\ Run i1 hs1 /\ Run i2 hs2.
  Proof.
    intros.
    destruct (run_inv_seq_2 i1 i2 hs) as (hs1, (hs2, (Hr1, Hr2))); auto.
    assert (hs = prod hs1 hs2). {
      eauto using run_inv_seq_1.
    }
    subst.
    exists hs1, hs2.
    repeat split; auto.
  Qed.

  Lemma i_subst_seq:
    forall x v i1 i2,
    i_subst x v (seq i1 i2) = seq (i_subst x v i1) (i_subst x v i2).
  Proof.
    induction i1; simpl; intros.
    - reflexivity.
    - destruct p as (a, e).
      simpl.
      rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - destruct p.
      simpl.
      rewrite access_subst_subst_eq.
      rewrite IHi.
      rewrite n_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      rewrite r_subst_subst_eq.
      reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        rewrite IHi2.
        subst.
        reflexivity.
      }
      rewrite IHi1.
      rewrite IHi2.
      reflexivity.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - destruct p.
      simpl.
      rewrite IHi; auto.
      rewrite n_subst_subst_neq; auto.
      rewrite access_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite IHi2; auto.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
      rewrite r_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec y v). {
        destruct (Set_VAR.MF.eq_dec x v). {
          subst.
          contradiction.
        }
        subst.
        rewrite IHi2; auto.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHi2; auto.
      }
      rewrite IHi2; auto.
      rewrite IHi1; auto.
  Qed.

  Inductive In (x:var) : inst -> Prop :=
  | in_acc_1:
    forall e n i,
    access_in x e ->
    In x (Acc (e, n) i)
  | in_acc_2:
    forall e n i,
    NIn x n ->
    In x (Acc (e, n) i)
  | in_acc_3:
    forall e n i,
    In x i ->
    In x (Acc (e, n) i)
  | in_decl_1:
    forall r i1 i2 y,
    RIn x r ->
    In x (Decl y r i1 i2)
  | in_decl_2:
    forall r i1 i2,
    In x (Decl x r i1 i2)
  | in_decl_3:
    forall r i1 i2 y,
    In x i1 ->
    In x (Decl y r i1 i2)
  | in_decl_4:
    forall r i1 i2 y,
    In x i2 ->
    In x (Decl y r i1 i2)
  | in_branch_1:
    forall l i1 i2,
    In x (Branch x l i1 i2)
  | in_branch_2:
    forall l y i1 i2,
    In x i1 ->
    In x (Branch y l i1 i2)
  | in_branch_3:
    forall l y i1 i2,
    In x i2 ->
    In x (Branch y l i1 i2).

  Lemma not_in_acc:
    forall x a n i,
    ~ In x (Acc (a, n) i) ->
    ~ In x i /\ ~ access_in x a /\ ~ NIn x n.
  Proof.
    intros.
    repeat split; intros N; contradict H;
      auto using in_acc_1, in_acc_2, in_acc_3.
  Qed.

  Lemma not_in_decl:
    forall x y r i1 i2,
    ~ In x (Decl y r i1 i2) ->
    x <> y /\ ~ RIn x r /\ ~ In x i1 /\ ~ In x i2.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst;
      auto using in_decl_1, in_decl_2, in_decl_3, in_decl_4.
  Qed.

  Lemma not_in_branch:
    forall x y r i1 i2,
    ~ In x (Branch y r i1 i2) ->
    x <> y /\ ~ In x i1 /\ ~ In x i2.
  Proof.
    intros.
    repeat split; intros N; contradict H; subst;
      auto using in_branch_1, in_branch_2, in_branch_3.
  Qed.

  Lemma i_subst_not_in:
    forall i x v,
    ~ In x i ->
    i_subst x v i = i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - destruct p.
      apply not_in_acc in H.
      destruct H as (H0, (H1, H2)).
      rewrite access_subst_not_in; auto.
      rewrite n_subst_not_in; auto.
      rewrite IHi; auto.
    - apply not_in_decl in H.
      destruct H as (H, (H1, (H2, H3))).
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      rewrite r_subst_not_in; auto.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - apply not_in_branch in H.
      destruct H as (H, (H1, H2)).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma i_subst_subst_trans:
    forall i x y v,
    ~ In x i ->
    i_subst x v (i_subst y (NVar x) i) =
    i_subst y v i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - destruct p.
      simpl.
      apply not_in_acc in H.
      destruct H as (H1, (H2, H3)).
      rewrite IHi; auto.
      rewrite access_subst_subst_trans; auto.
      rewrite n_subst_subst_trans; auto.
    - apply not_in_decl in H.
      destruct H as (H0, (H1, (H2, H3))).
      rewrite r_subst_subst_trans; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite IHi2; auto.
        rewrite i_subst_not_in; auto.
      }
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - apply not_in_branch in H.
      destruct H as (H, (H1, H2)).
      destruct (Set_VAR.MF.eq_dec x v); try contradiction.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite i_subst_not_in; auto.
        rewrite IHi2; auto.
      }
      rewrite IHi1; auto.
      rewrite IHi2; auto.
  Qed.

  Lemma in_i_subst_neq:
    forall i x y v,
    In x (i_subst y v i) ->
    x <> y ->
    ~ NIn x v ->
    In x i.
  Proof.
    induction i; simpl; intros.
    - inversion H.
    - destruct p.
      inversion H; subst; clear H.
      + apply access_in_subst_neq in H3; auto using in_acc_1.
      + apply in_n_subst_neq in H3; auto using in_acc_2.
      + apply IHi in H3; auto using in_acc_3.
    - inversion H; subst; clear H.
      + apply in_r_subst_neq in H3; auto using in_decl_1.
      + auto using in_decl_2.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto using in_decl_3.
        }
        apply IHi1 in H3; auto using in_decl_3.
      + apply IHi2 in H3; auto using in_decl_4.
    - inversion H; subst; clear H.
      + auto using in_branch_1.
      + destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          auto using in_branch_2.
        }
        apply IHi1 in H3; auto using in_branch_2.
      + apply IHi2 in H3; auto using in_branch_3.
  Qed.

End Defs.
End C2.

Module Compiler.
  Import Conc1.
  Section Defs.
  Context {A:Access}.
  Variable TID_COUNT: nat.
  Variable TID : var.

  Fixpoint proj (c:C1.inst) : C2.inst :=
    match c with
    | C1.Skip => C2.Skip
    | C1.Acc a c1 => C2.Acc (a, NVar TID) (proj c1)
    | C1.For x r c1 c2 => C2.Decl x r (proj c1) (proj c2)
    | C1.Loop x l c1 c2 => C2.Branch x l (proj c1) (proj c2) 
    end.

  Variable T1: var.
  Variable T2: var.

  Definition do_proj x i := C2.i_subst TID (NVar x) (proj i).

  Definition translate (c:C1.inst) : C2.inst :=
      (C2.Decl T1 (NNum 1, NNum TID_COUNT)
        (C2.Decl T2 (NNum 0, NVar T1)
          (C2.seq (do_proj T1 c) (do_proj T2 c))
        C2.Skip)
      C2.Skip).

(*
  Notation "i '[' x ':=' n ']'" := (C2.i_subst x n i) (at level 40).
  Notation "i '[' x ':=' n ']'" := (C1.i_subst x n i) (at level 40).
(*  Notation "'[[' i ']]'" := (proj i) (at level 40). *)
  Coercion NNum: nat >-> nexp.
*)

  Lemma in_to_in_proj:
    forall x i,
    C1.In x i ->
    C2.In x (proj i).
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H;
        auto using C2.in_acc_1, C2.in_acc_3, C2.in_decl_1, C2.in_decl_2, C2.in_decl_3,
          C2.in_decl_4, C2.in_branch_1, C2.in_branch_2, C2.in_branch_3.
  Qed.

  Lemma in_proj_to_in:
    forall x i,
    x <> TID ->
    C2.In x (proj i) ->
    C1.In x i.
  Proof.
    induction i; simpl; intros; inversion H0; subst; clear H0;
        auto using C1.in_acc_1, C1.in_acc_2, C1.in_for_1, C1.in_for_2, C1.in_for_3,
          C1.in_for_4, C1.in_loop_1, C1.in_loop_2, C1.in_loop_3.
    inversion H2; subst; clear H2.
    contradiction.
  Qed.

  Lemma i_subst_proj_rw:
    forall x i n,
    x <> TID ->
    proj (C1.i_subst x (NNum n) i) = C2.i_subst x (NNum n) (proj i).
  Proof.
    induction i; simpl; intros; destruct (Set_VAR.MF.eq_dec x TID); try contradiction.
    - reflexivity.
    - rewrite IHi; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
    - rewrite IHi2; auto.
      destruct (Set_VAR.MF.eq_dec x v). {
        auto.
      }
      rewrite IHi1; auto.
  Qed.

  Lemma var_eq_dec_rw_eq:
    forall x,
    exists e, Set_VAR.MF.eq_dec x x = @left _ _ e.
  Proof.
    intros.
    destruct (Set_VAR.MF.eq_dec x x).
    - exists e.
      reflexivity.
    - contradiction.
  Qed.

  Lemma proj_seq:
    forall i1 i2,
    proj (C1.seq i1 i2) = C2.seq (proj i1) (proj i2).
  Proof.
    induction i1; intros; simpl.
    - reflexivity.
    - rewrite IHi1.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
    - rewrite IHi1_2.
      reflexivity.
  Qed.

  Theorem run_m_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n hs1,
    n < TID_COUNT ->
    C2.Run (C2.i_subst TID (NNum n) (proj i)) hs1 ->
    ~ C1.Var TID i ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    intros i hs2 H.
    induction H; intros.
    - inversion H0; subst; clear H0.
      reflexivity.
    - inversion H2; subst; clear H2.
      apply C1.var_not_in_acc in H3.
      assert (IHRun := IHRun _ _ H1 H8 H3).
      subst.
      destruct (var_eq_dec_rw_eq TID) as (?, R).
      rewrite R in *; clear R.
      erewrite Hist.m_proj_prepend; eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (l0 = l). {
        assert (R: r_subst TID (NNum n) r = r). {
          apply r_subst_not_in.
          eapply r_step_to_not_in; eauto.
        }
        rewrite R in *.
        eauto using r_step_fun.
      }
      subst.
      assert (~ C1.Var TID (C1.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        eauto using C1.var_loop_to_for.
      }
      eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      assert (~ C1.Var TID (C1.Loop x l i1 i2)). {
        intros N.
        contradict H3.
        auto using C1.var_loop_cons.
      }
      apply IHRun2 in H11; auto; clear IHRun2.
      subst.
      rewrite Hist.m_proj_app.
      assert (Hist.m_proj n0 hs1 = hs3). {
        destruct (Set_VAR.MF.eq_dec TID x). {
          apply C1.var_not_in_loop in H3.
          destruct H3 as (?, _).
          contradiction.
        }
        apply IHRun1; auto; clear IHRun1.
        + rewrite C2.i_subst_subst_neq in H10; auto.
          rewrite <- C2.i_subst_seq in H10.
          rewrite <- i_subst_proj_rw in H10; auto.
          rewrite proj_seq in *.
          auto.
        + intros N.
          contradict H2.
          eauto using C1.var_iter_loop.
      }
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (~ C1.Var TID i2). {
        intros N.
        contradict H2.
        auto using C1.var_loop_3.
      }
      auto.
  Qed.

  Lemma run_do_proj (T:var):
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n hs1,
    n < TID_COUNT -> 
    C2.Run (C2.i_subst T (NNum n) (do_proj T i)) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T i ->
    T <> TID ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    unfold do_proj.
    intros.
    rewrite C2.i_subst_subst_trans in H1; auto.
    + eapply run_m_proj; eauto.
    + intros N.
      contradict H3.
      apply in_proj_to_in; auto.
  Qed.

  Variable t1_neq_tid: T1 <> TID.
  Variable t2_neq_tid: T2 <> TID.
  Variable t1_neq_t2: T1 <> T2.


  Lemma run_do_proj_do_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT ->
    n2 < TID_COUNT ->
    C2.Run
        (C2.i_subst T2 (NNum n1)
           (C2.i_subst T1 (NNum n2) (C2.seq (do_proj T1 i) (do_proj T2 i)))) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    prod (Hist.m_proj n2 hs2) (Hist.m_proj n1 hs2) = hs1.
  Proof.
    intros.
    rewrite C2.i_subst_seq in H2.
    rewrite C2.i_subst_seq in H2.
    apply C2.run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ C2.In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in.
    }
    assert (t2_nin_proj_i: ~ C2.In T2 (proj i)). {
      intros N.
      contradict H5.
      auto using in_proj_to_in.
    }
    (* Simplify Hra: *)
    assert (~ C2.In T2 (C2.i_subst T1 (NNum n2) (do_proj T1 i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto. {
        unfold do_proj in N.
        apply C2.in_i_subst_neq in N; auto.
        intros M.
        inversion M.
        subst.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hra; auto.
    eapply run_do_proj in Hra; eauto.
    subst.
    (* Simplify Hrb *)
    rewrite C2.i_subst_subst_neq in Hrb; auto.
    assert (~ C2.In T1 (C2.i_subst T2 (NNum n1) (do_proj T2 i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto. {
        unfold do_proj in N.
        apply C2.in_i_subst_neq in N; auto.
        intros M.
        inversion M.
        subst.
        contradiction.
      }
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hrb; auto.
    eapply run_do_proj in Hrb; eauto.
    subst.
    reflexivity.
  Qed.

  (*
  Lemma run_proj_proj:
    forall i hs2,
    C1SX.Run TID_COUNT TID i hs2 ->
    forall n1 n2 hs1,
    n1 < TID_COUNT -> 
    n2 < TID_COUNT -> 
    C2.Run 
      (C2.i_subst T2 (NNum n2)
          (C2.i_subst T1 (NNum n1)
             (C2.seq (C2.i_subst TID (NVar T1) (proj i))
                     (C2.i_subst TID (NVar T2) (proj i))))) hs1 ->
    ~ C1.Var TID i ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    prod (Hist.m_proj n1 hs2) (Hist.m_proj n2 hs2) = hs1.
  Proof.
    intros.
    rewrite C2.i_subst_seq in H2.
    rewrite C2.i_subst_seq in H2.
    apply C2.run_inv_seq in H2.
    destruct H2 as (hsa, (hsb, (?, (Hra, Hrb)))).
    subst.
    assert (t1_nin_proj_i: ~ C2.In T1 (proj i)). {
      intros N.
      contradict H4.
      auto using in_proj_to_in.
    }
    assert (t2_nin_proj_i: ~ C2.In T2 (proj i)). {
      intros N.
      contradict H5.
      auto using in_proj_to_in.
    }
    (* Simplify Hra: *)
    rewrite C2.i_subst_subst_trans in Hra; auto.
    assert (~ C2.In T2 (C2.i_subst TID (NNum n1) (proj i))). {
      intros N.
      contradict t2_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto.
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hra; auto.
    eapply run_m_proj in Hra; eauto.
    subst.
    (* Simplify Hrb *)
    rewrite C2.i_subst_subst_neq in Hrb; auto.
    rewrite C2.i_subst_subst_trans in Hrb; auto.
    assert (~ C2.In T1 (C2.i_subst TID (NNum n2) (proj i))). {
      intros N.
      contradict t1_nin_proj_i.
      apply C2.in_i_subst_neq in N; auto.
      intros M.
      inversion M.
    }
    rewrite C2.i_subst_not_in in Hrb; auto.
    eapply run_m_proj in Hrb; eauto.
    subst.
    reflexivity.
  Qed.
*)
  Lemma in_branch_inv:
    forall l hs x i1 i2,
    C2.Run (C2.Branch x l i1 i2) hs ->
    forall n,
    List.In n l ->
    exists hs2,
    incl hs2 hs /\ C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) hs2.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H0; subst; clear H0;
        inversion H; subst; clear H. {
      exists hs1.
      repeat split; auto using incl_app_refl_l.
    }
    assert (IHl := IHl hs2 x i1 i2 H8 _ H1).
    destruct IHl as (hs3, (Hinc, Hr)).
    exists hs3.
    split; auto.
    apply incl_appr.
    auto.
  Qed.

  Lemma in_decl_inv:
    forall e1 e2 hs x i1 i2,
    C2.Run (C2.Decl x (e1, e2) i1 i2) hs ->
    exists n1 n2,
    NStep e1 n1 /\
    NStep e2 n2 /\
    ((n1 >= n2 /\ C2.Run i2 hs)
    \/
    forall n,
    n1 <= n < n2 ->
    exists hs2,
    incl hs2 hs /\ C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) hs2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H5; subst.
    exists n1.
    exists n2.
    split; auto.
    split; auto.
    apply range_list_inv in H4.
    destruct H4 as [(Ha,Hb)| (Hl, Ha)]. {
      subst.
      inversion H6; subst; clear H6.
      auto.
    }
    right.
    intros.
    apply (Ha n) in H.
    eapply in_branch_inv in H6; eauto.
  Qed.


  Variable tid_ge_2: TID_COUNT > 2.

  Theorem a_pair_incl
      (i:C1.inst)
      (T1_nin_i: ~ C1.In T1 i)
      (T2_nin_i: ~ C1.In T2 i)
      (TID_nvar_i: ~ C1.Var TID i)
    :
    forall hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    C2.Run (translate i) hs2 ->
    Hist.APairIncl hs1 hs2.
  Proof.
    unfold translate.
    intros.
    unfold Hist.APairIncl.
    intros.
    apply C2.run_decl_inv in H1.
    destruct H1 as (n1, (n2, (Hn1, (Hn2, Hx)))).
    inversion Hn1; subst; clear Hn1.
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    subst.
    clear Hn2.
    destruct Hx as [(N,Hx)|(hss, (?, Hx))]. {
      Import Omega.
      omega.
    }
    subst.
    assert (x_lt_tc: access_tid x < TID_COUNT) by eauto.
    assert (y_lt_tc: access_tid y < TID_COUNT) by eauto.
    (* Check the tids of both accesses. *)
    assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
      by omega.
    destruct Ht as [Ht | [Ht|Ht]].
    - (* x = y *)
      (*
      assert (Hwhat: access_tid x = 0 \/ 1 <= access_tid x) by omega.
      destruct Hwhat. {
        assert (Ha : 1 <= 1 < TID_COUNT) by omega.
        assert (Hx := Hx 1 Ha).
        destruct Hx as (hs, (Hx,Hy)).
        apply C2.run_inv_seq in Hx.
        destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
        inversion Hr2; subst; clear Hr2.
        rewrite prod_nil_nil_r in *.
        simpl in *.
        (*
        destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
        *)
        destruct (Set_VAR.MF.eq_dec T1 T2) as [N| _]; try contradiction.
        (*
        apply C2.run_decl_inv in Hr1.
        destruct Hr1 as (nn1, (nn2, (Hnn1, (Hnn2, Hr1)))).
        inversion Hnn1; subst; clear Hnn1.
        inversion Hnn2; subst; clear Hnn2.
        destruct Hr1 as [(?, _)|(hssr, (?,Hr1))]. {
          omega.
        }
        subst.
        assert (Hw : 0 <= 0 < 1) by omega.
        assert (Hr1 := Hr1 0 Hw).
        destruct Hr1 as (hrs, (Hr1, Hr2)).
        apply C2.run_inv_seq in Hr1.
        destruct Hr1 as (hrr1, (hrr2, (?, (Hr1, Hr3)))).
        inversion Hr3; subst; clear Hr3.
        rewrite prod_nil_nil_r in *.
        eapply run_proj_proj in Hr1; eauto with *.
        subst.
        eapply m_pair_in_concat; eauto.
        eapply m_pair_in_concat; eauto.
        apply m_pair_in_prod_r. {
          
        }
        (* MIn (Hist.m_proj 0) *)
        *)
      }
      *)
      Import Omega.
      assert (Ha : 1 <= access_tid x < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid x) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
    - (* x < y *)
      Import Omega.
      (* Satisfy outer-forall and unpax the existential in Hx *)
      assert (Ha : 1 <= access_tid y < TID_COUNT) by omega.
      assert (Hx := Hx (access_tid y) Ha).
      destruct Hx as (hs, (Hx,Hy)).
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      simpl in *.
      destruct (Set_VAR.MF.eq_dec T1 T1) as [_| N]; try contradiction.
      apply C2.run_decl_inv in Hr1.
      destruct Hr1 as (n1, (n2, (Hn1, (Hn2, [(N, Hr1)|(Hss, (?, Hx))])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid(y) = 0 /\ tid(y) > 0 *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      (* Satisfy the outer forall and unpax the existential in Hx *)
      assert (Hb : 0 <= access_tid x < access_tid y) by omega.
      assert (Hx := Hx (access_tid x) Hb).
      destruct Hx as (hs, (Hx,Hz)).
      destruct (Set_VAR.MF.eq_dec T1 T2) as [e|_]. {
        subst.
        contradiction.
      }
      (* Now we want to handle the seq in Hx *)
      apply C2.run_inv_seq in Hx.
      destruct Hx as (hx1, (hx2, (?, (Hr1, Hr2)))).
      inversion Hr2; subst; clear Hr2.
      rewrite prod_nil_nil_r in *.
      eapply run_do_proj_do_proj in Hr1; eauto.
      subst.
      eapply m_pair_in_concat; eauto.
      eapply m_pair_in_concat; eauto.
  Qed.
*)
(*
  Theorem m_pair_incl (tid_ge_2: TID_COUNT > 2) (t1_neq_t2: T1 <> T2)
      (t1_neq_tid: T1 <> TID)
      (t2_neq_tid: T2 <> TID)
      (in_heap: forall x i hs, C2.Run i hs -> MIn x hs -> access_tid x < TID_COUNT)
      i
      (T1_nin_i: ~ C1.In T1 i)
      (T2_nin_i: ~ C1.In T2 i)
      (TID_nvar_i: ~ C1.Var TID i)
    :
    forall hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    C2.Run (translate i) hs2 ->
    MPairIncl hs1 hs2.
  Proof.
    Import Omega.
    intros hs1 H.
    induction H; unfold MPairIncl; intros.
    - apply m_in_nil_nil in H0.
      contradiction.
    - apply m_in_prepend_inv in H2.
      apply m_in_prepend_inv in H3.
      destruct H2 as [H2|H2], H3 as [H3|H3];
        try (
          apply m_in_concat in H2;
          eapply Hist.m_in_gen_access_inv in H2; eauto;
          destruct H2 as (n1, (l1, (H_lt1, (H_acc1, H_in1)))));
        try (
          apply m_in_concat in H3;
          eapply Hist.m_in_gen_access_inv in H3; eauto;
          destruct H3 as (n2, (l2, (H_lt2, (H_acc2, H_in2))))
        ).
      + 
        eapply Hist.m_in_gen_access_inv in H3; eauto.
        
      
      unfold translate in *.
      (* Check the tids of both accesses. *)
      assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
        by omega.
      destruct Ht as [Ht | Ht]. {
        give_up.
      }
      C2.DoLoop
      assert (Horig := H1).
      (* Get the smallest task *)
      assert (Hx := in_decl_inv _ _ _ _ _ _ H1); clear H1.
      destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
        inversion Hn1; subst; clear Hn1.
        assert (n2 = TID_COUNT). {
        inversion Hn2; subst; clear Hn2.
        reflexivity.
      }
      subst.
      omega.
      }
      assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    clear Hn2.
    inversion Hn1; subst; clear Hn1.
    subst.
    (* Simplify the expression under Ha *)
    simpl in Ha.
    destruct (Set_VAR.MF.eq_dec T1 T1) as [e|e]; try contradiction; clear e.
    destruct (Set_VAR.MF.eq_dec T1 T2) as [e|e]; try contradiction; clear e.
    destruct Ht. {
      assert (Hlt:  1 <= access_tid y < TID_COUNT). {
        assert (access_tid y < TID_COUNT). {
          eapply in_heap; eauto.
          eapply m_in_def; eauto using pair_in_to_in_r.
        }
        omega.
      }
      assert (Ha := Ha (access_tid y) Hlt).
      destruct Ha as (hs3, (Hinc, Ha)).
      (* We have a run-object, now use in_decl_inv *)
      assert (Hx := in_decl_inv _ _ _ _ _ _ Ha); clear Ha.
      destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid y <= 0 /\ tid y >= 1 -> False *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      assert (Hlt2: 0 <= access_tid x < access_tid y) by omega.
      assert (Ha := Ha (access_tid x) Hlt2).
      destruct Ha as (hs4, (Hinc2, Ha)).
      apply C2.run_inv_seq in Ha.
      destruct Ha as (Ha_hs1, (Ha_hs2, (?, (Ha,Hb)))).
      subst.
      inversion Hb; subst; clear Hb.
      rewrite C2.i_subst_seq in Ha.
      rewrite C2.i_subst_seq in Ha.
      assert (t1_nin_proj_i: ~ C2.In T1 (proj i)). {
        intros N.
        contradict T1_nin_i.
        apply in_proj_to_in; auto.
      }
      assert (t2_nin_proj_i: ~ C2.In T2 (proj i)). {
        intros N.
        contradict T2_nin_i.
        apply in_proj_to_in; auto.
      }
      (* Simplify Ha in terms of y *)
      assert (R:
         C2.i_subst T2 (NNum (access_tid x))
             (C2.i_subst T1 (NNum (access_tid y)) (C2.i_subst TID (NVar T1) (proj i)))
         =
             C2.i_subst TID (NNum (access_tid y)) (proj i)
      ). {
        rewrite C2.i_subst_subst_trans; auto.
        assert (~ C2.In T2 (C2.i_subst TID (NNum (access_tid y)) (proj i))). {
          intros N.
          contradict t2_nin_proj_i.
          apply C2.in_i_subst_neq in N; auto.
          intros M.
          inversion M.
        }
        rewrite C2.i_subst_not_in; auto.
      }
      rewrite R in *; clear R.
      (* Simplify Ha in terms of x *)
      assert (R:
           C2.i_subst T2 (NNum (access_tid x))
               (C2.i_subst T1 (NNum (access_tid y)) (C2.i_subst TID (NVar T2) (proj i)))
           =
               C2.i_subst TID (NNum (access_tid x)) (proj i)
        ). {
        rewrite C2.i_subst_subst_neq; auto.
        rewrite C2.i_subst_not_in; auto.
        rewrite C2.i_subst_subst_trans; auto.
        give_up.
      }
      rewrite R in *; clear R.
      apply C2.run_inv_seq in Ha.
      destruct Ha as (hs4, (hs5, (?, (Ha, Hb)))).
      subst.
      (*
      clear Horig.
      *)
      apply run_m_proj with (hs2:=hs1) in Ha; auto with *.
      apply run_m_proj with (hs2:=hs1) in Hb; auto with *.
      subst.
    (*
    var tid, [tid] -> var tid, ([tid], tid) 
     *)

  Qed.
*)
  Variable tid_ge_2: TID_COUNT > 2.
  Variable in_heap: forall x i hs, C2.Run i hs -> MIn x hs -> access_tid x < TID_COUNT.
  Theorem correctness:
    forall i hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    C2.Run (translate i) hs2 ->
    Hist.MSafe hs1 ->
    ~ C1.In T1 i ->
    ~ C1.In T2 i ->
    ~ C1.Var TID i -> 
    Hist.MSafeStrong hs2.
  Proof.
    Import Omega.
    intros.
    rename H2 into T1_nin_i.
    rename H3 into T2_nin_i. 
    rename H4 into TID_nvar_i.
    unfold Hist.MSafeStrong.
    intros.
    unfold translate, do_proj in *.
    apply Exists_exists in H2.
    destruct H2 as (l, (Hi, Hj)).
    (* Check the tids of both accesses. *)
    assert (Ht: access_tid x = access_tid y \/ access_tid x < access_tid y \/ access_tid x > access_tid y)
      by omega.
    destruct Ht as [Ht | Ht]. {
      auto using access_safe_eq_tid.
    }
    assert (Horig := H0).
    (* Get the smallest task *)
    assert (Hx := in_decl_inv _ _ _ _ _ _ H0); clear H0.
    destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
      inversion Hn1; subst; clear Hn1.
      assert (n2 = TID_COUNT). {
        inversion Hn2; subst; clear Hn2.
        reflexivity.
      }
      subst.
      omega.
    }
    assert (n2 = TID_COUNT). {
      inversion Hn2; subst; clear Hn2.
      reflexivity.
    }
    clear Hn2.
    inversion Hn1; subst; clear Hn1.
    subst.
    (* Simplify the expression under Ha *)
    simpl in Ha.
    destruct (Set_VAR.MF.eq_dec T1 T1) as [e|e]; try contradiction; clear e.
    destruct (Set_VAR.MF.eq_dec T1 T2) as [e|e]; try contradiction; clear e.
    destruct Ht. {
      assert (Hlt:  1 <= access_tid y < TID_COUNT). {
        assert (access_tid y < TID_COUNT). {
          eapply in_heap; eauto.
          eapply m_in_def; eauto using pair_in_to_in_r.
        }
        omega.
      }
      assert (Ha := Ha (access_tid y) Hlt).
      destruct Ha as (hs3, (Hinc, Ha)).
      (* We have a run-object, now use in_decl_inv *)
      assert (Hx := in_decl_inv _ _ _ _ _ _ Ha); clear Ha.
      destruct Hx as (n1, (n2, (Hn1, (Hn2, [(Ha,Hb)|Ha])))). {
        inversion Hn1; subst; clear Hn1.
        inversion Hn2; subst; clear Hn2.
        (* tid y <= 0 /\ tid y >= 1 -> False *)
        omega.
      }
      inversion Hn1; subst; clear Hn1.
      inversion Hn2; subst; clear Hn2.
      assert (Hlt2: 0 <= access_tid x < access_tid y) by omega.
      assert (Ha := Ha (access_tid x) Hlt2).
      destruct Ha as (hs4, (Hinc2, Ha)).
      apply C2.run_inv_seq in Ha.
      destruct Ha as (Ha_hs1, (Ha_hs2, (?, (Ha,Hb)))).
      subst.
      eapply run_proj_proj in Ha; eauto with *.
      subst.
      inversion Hb; subst; clear Hb.
      
    (*
    var tid, [tid] -> var tid, ([tid], tid) 
     *)

  Qed.

  End Defs.

End Compiler.

Module Examples.
  Import Compiler.
  Import C2.

  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match C2.step s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.

  Fixpoint hists s :=
  match s with
  | Par (Leaf (h, i)) s2 => h :: hists s2
  | _ => []
  end.

  Definition run_h steps s := hists (snd (run steps s)).


  Definition HELLO1 n := Leaf ([],
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    )
    Skip
  ).

  Definition HELLO1_VAL t :=  Par (Leaf ([{| OneDim.tid := t; OneDim.index := 0 |}], Skip))
         (Par (Leaf ([{| OneDim.tid := t; OneDim.index := 1 |}], Skip))
          Empty).

  Goal snd (run 300 (HELLO1 (NNum 9))) = HELLO1_VAL 9.
    auto.
  Qed.

  Definition HELLO2 := Leaf ([],
    Decl (variable "tid") (NNum 0, NNum 2) (
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), (NVar (variable "tid"))) Skip
    ) Skip
    )
    Skip
  ).

  (**
  
    var t \in (0, 2) {
      var x \in (0, 2) {
        [x] by t
      }
    }
  
    *)

  
  Compute run 24 HELLO2.

  Infix "||" := Par.
  Notation "{}" := Empty.
  Notation "x 'by' y" := {| OneDim.tid := y; OneDim.index := x |} (at level 50, left associativity).


  Definition HELLO3 n := Leaf ([],
    Decl (variable "x") (NNum 0, NNum 2) (
      Acc ((NVar (variable "x"), BBool true), n) Skip
    ) (Acc ((NNum 9, BBool true), NNum 9) Skip)
  ).
  
  Compute run 17 (HELLO3 (NNum 10)).


  Definition GOOD1 :=
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.GOOD1.

  Compute GOOD1.

  Definition body x :=
    Decl (variable "x") (NNum 0, NNum 2)
        (Acc (NVar (variable "x"), NRel NEq x (NVar (variable "x")), x) Skip) Skip.

  Compute Conc1.Examples.GOOD1.
  Compute GOOD1.

  Compute run_h 40 (Leaf ([], GOOD1)). (* 39 *)

  (* ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip) *)

  Definition GOOD2 :=
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.GOOD2.

  Compute run 10 (Leaf ([], GOOD2)). (* 10 *)

  Definition BAD := 
    translate 2 Conc1.Examples.TID (variable "T1") (variable "T2") Conc1.Examples.BAD.
(*
  Compute BAD.
*)
  Compute (run_h 36 (Leaf ([], BAD))). (* 35 *)

  Compute hists (snd (run 36 (Leaf ([], BAD)))).
  (*
        [{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}]
  *)

End Examples.
