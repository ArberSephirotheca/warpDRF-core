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
(*
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
    Run (C1.seq i1 i2) hs ->
    exists hs1 hs2, Run i1 hs1 /\ Run i2 hs2.
  Proof.
    intros i1 i2 hs H.
    remember (C1.seq _ _) as i.
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
        exists (prepend (List.concat v) hs).
        split; auto using run_skip, run_access.
      + edestruct IHRun as (hs1, (hs2, (?, ?))); eauto.
        exists (prepend (List.concat v) hs1).
        exists hs2.
        split; auto using run_access.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; eauto using run_skip, run_for.
      }
      destruct (IHRun i0 (C1.Loop x l i1 i3_2) eq_refl) as (hs1, (hs2, (Hr1, Hr2)));
      clear IHRun.
      exists hs1.
      exists hs2.
      split; eauto using run_for.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        clear H1.
        exists [[]].
        exists (hs1 ++ hs2).
        split; auto using run_skip.
        apply run_loop_cons; auto.
      }
      remember (C1.i_subst _ _ _).
      destruct (IHRun1 i0 (C1.seq i i3_2)) as (hsa, (hsb, (Hr1, Hr2))). {
        rewrite seq_seq_rw.
        reflexivity.
      }
      clear IHRun1.
      destruct (IHRun2 i0 (C1.Loop x l i1 i3_2) eq_refl) as (hsa1, (hsb1, (Hra, Hrb))).
      assert (hsb = hsb1) by eauto using run_fun.
      clear Hrb.
      exists (hsa ++ hsa1).
      exists hsb.
      subst.
      split; auto using run_loop_cons.
    - destruct i3; simpl in *; try inversion Heqi; subst; try clear Heqi. {
        exists [[]].
        exists hs.
        split; auto using run_skip, run_loop_nil.
      }
      destruct (IHRun _ _ eq_refl) as (hs1, (hs2, (?, ?))).
      exists hs1.
      exists hs2.
      split; auto using run_loop_nil.
  Qed.

  Lemma run_inv_seq:
    forall i1 i2 hs,
    Run (C1.seq i1 i2) hs ->
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
*)
End Defs.
End C2.

Module Compiler.
  Import Conc1.
  Section Defs.
  Context {A:Access}.
  Variable TID_COUNT: nat.
  Variable TID : var.

  Fixpoint proj (t:nexp) (c:C1.inst) : C2.inst :=
    match c with
    | C1.Skip => C2.Skip
    | C1.Acc a c1 => C2.Acc (a, t) (proj t c1)
    | C1.For x r c1 c2 => C2.Decl x r (proj t c1) (proj t c2)
    | C1.Loop x l c1 c2 => C2.Branch x l (proj t c1) (proj t c2) 
    end.

  Variable T1: var.
  Variable T2: var.

  Definition do_proj x c :=
    proj (NVar x) (C1.i_subst TID (NVar x) c).


  Definition translate (c:C1.inst) : C2.inst :=
      (C2.Decl T1 (NNum 1, NNum TID_COUNT)
        (C2.Decl T2 (NNum 0, NVar T1)
          (C2.seq (do_proj T1 c) (do_proj T2 c))
        C2.Skip)
      C2.Skip).

  Lemma i_subst_proj_rw:
    forall x n1 n2 i,
    C2.i_subst x (NNum n1) (proj (NNum n2) i) = proj (NNum n2) (C1.i_subst x (NNum n1) i).
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi.
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      reflexivity.
    - rewrite IHi1.
      rewrite IHi2.
      destruct (Set_VAR.MF.eq_dec x v). {
        reflexivity.
      }
      reflexivity.
  Qed.
  Lemma proj_seq:
    forall n i1 i2,
    proj n (C1.seq i1 i2) = C2.seq (proj n i1) (proj n i2).
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
    C2.Run (proj (NNum n) (C1.i_subst TID (NNum n) i)) hs1 ->
    Hist.m_proj n hs2 = hs1.
  Proof.
    intros i hs2 H.
    induction H; intros.
    - inversion H0; subst; clear H0.
      reflexivity.
    - inversion H2; subst; clear H2.
      assert (IHRun := IHRun _ _ H1 H7).
      subst.
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
      eauto.
    - simpl in *.
      inversion H2; subst; clear H2.
      apply IHRun2 in H10; auto; clear IHRun2.
      subst.
      rewrite Hist.m_proj_app.
      destruct (Set_VAR.MF.eq_dec TID x). {
        subst.
        assert (Hist.m_proj n0 hs1 = hs3). {
          apply IHRun1; auto.
          rewrite C1.i_subst_seq.
          rewrite C1.i_subst_subst_eq.
          rewrite i_subst_proj_rw in *.
          rewrite proj_seq in *.
          assumption.
        }
        subst.
        reflexivity.
      }
      assert (Hist.m_proj n0 hs1 = hs3). {
        apply IHRun1; auto.
        rewrite C1.i_subst_seq.
        rewrite i_subst_proj_rw in *.
        rewrite proj_seq in *.
        rewrite C1.i_subst_subst_neq in H9; auto.
      }
      subst.
      auto.
    - inversion H1; subst; clear H1.
      auto.
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
