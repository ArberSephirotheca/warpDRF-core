Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
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
(* Require SymExe. *)
Require Import Tasks.
Require Conc1.
Import ListNotations.
Module C1 := Conc1.
Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
  Notation history := (list access_val).
  Definition t := (history * C1.inst) % type.

  Inductive Red: t -> list t -> Prop :=
  | red_acc:
    forall e v h c, 
    Hist.GenAccess TID e TID_COUNT v ->
    Red (h, C1.Acc e c) [(List.concat v ++ h, c)]
  | red_for:
    forall h x r l c1 c2,
    RStep r l ->
    Red (h, C1.For x r c1 c2) [(h, C1.Loop x l c1 c2)]
  | red_branch_cons:
    forall h l c1 c2 n x,
    Red (h, C1.Loop x (n::l) c1 c2) [(h, C1.i_subst x (NNum n) c1); (h, C1.Loop x l c1 c2) ]
  | red_branch_nil:
    forall h x c1 c2,
    Red (h, C1.Loop x [] c1 c2) [(h, c2)].

  Inductive Run: C1.inst -> list history -> Prop :=
  | run_skip:
    Run C1.Skip [[]]
  | run_access:
    forall i e v hs,
    Hist.GenAccess TID e TID_COUNT v ->
    Run i hs ->
    Run (C1.Acc e i) (prepend (List.concat v) hs)
  | run_for:
    forall r l i1 i2 x hs,
    RStep r l ->
    Run (C1.Loop x l i1 i2) hs ->
    Run (C1.For x r i1 i2) hs
  | run_loop_cons:
    forall x n l i1 i2 hs1 hs2,
    Run (C1.seq (C1.i_subst x (NNum n) i1) i2) hs1 ->
    Run (C1.Loop x l i1 i2) hs2 ->
    Run (C1.Loop x (n::l) i1 i2) (hs1 ++ hs2)
  | run_loop_nil:
    forall x i1 i2 hs,
    Run i2 hs ->
    Run (C1.Loop x [] i1 i2) hs.


  Definition is_value (s:t) :=
    let (h, p) := s in
    match p with
    | C1.Skip => true
    | _ => false
    end.

  Definition red (s:t) :=
  let (h, c) := s in
  match c with
  | C1.Acc e c =>
    match Hist.gen_access TID e TID_COUNT with
    | Some l => Some [(List.concat l ++ h, c)]
    | None => None
    end
  | C1.For x r c1 c2 =>
    match r_step r with
    | Some l => Some [(h, C1.Loop x l c1 c2)]
    | _ => None
    end
  | C1.Loop x (n::l) c1 c2 => Some [(h, C1.i_subst x (NNum n) c1); (h, C1.Loop x l c1 c2)]
  | C1.Loop _ [] _ c => Some [(h,c)]
  | C1.Skip => None
  end.

  Lemma red_to_prop:
    forall a s,
    red a = Some s -> Red a s.
  Proof.
    intros.
    destruct a as (h, i).
    simpl in *.
    destruct i.
    - inversion H.
    - destruct (Hist.gen_access _ _ _) eqn:Hg; inversion H; subst.
      constructor; auto using Hist.gen_access_to_prop.
    - destruct (r_step r) eqn:Hr; inversion H; subst; clear H.
      constructor; auto using r_step_to_prop.
    - destruct l; inversion H; constructor.
  Qed.

  Lemma prop_to_red:
    forall a s,
    Red a s ->
    red a = Some s.
  Proof.
    intros.
    destruct a as (h, []); simpl; inversion H; subst; clear H; auto.
    - apply Hist.prop_to_gen_access in H4.
      rewrite H4.
      reflexivity.
    - apply prop_to_r_step in H6.
      rewrite H6.
      reflexivity.
  Qed.

  Lemma red_to_value_false:
    forall a s,
    red a = Some s ->
    is_value a = false.
  Proof.
    intros.
    destruct a as (h, []); simpl in *; auto.
    inversion H.
  Qed.

  Lemma value_true_to_leaf:
    forall a, is_value a = true -> red a = None.
  Proof.
    intros.
    destruct a as (h, []); inversion H.
    auto.
  Qed.
(*
  Instance C1_Lang : Lang t := {
    AStep := Red;
    a_is_value := is_value;
    red_leaf := red;
    red_leaf_to_a_step := red_to_prop;
    a_step_to_red_leaf := prop_to_red;
    step_to_is_value_false := red_to_value_false;
    (*step_is_value_true := value_true_to_leaf;*)
  }.
  Definition Step := @SymExe.Step _ C1_Lang.
  Definition Value := Forall C1.Value.
  Definition BStep := BigStep _ Step Value.
  Notation C1_Step := C1.Step.
*)
  Ltac run_clean :=
    repeat match goal with
    | [ H: Run [] _ |- _ ] => inversion H; subst; clear H
    | [ H: Hist.Safe [] |- _ ] => clear H
    | [ H: Run [C1.Skip] _ |- _ ] => inversion H; subst; clear H
    | [ H: C1.Run _ _ C1.Skip _ |- _] => inversion H; subst; clear H
    | [ H1: Hist.GenAccess ?x ?a ?n ?v1,
        H2:Hist.GenAccess ?x ?a ?n ?v2 |- _ ] =>
          let H := fresh in
          assert (H: v2 = v1) by eauto using Hist.gen_access_fun;
          rewrite H in *; clear H;
          clear H1
    | [ H1: RStep ?r ?l1,
        H2:RStep ?r ?l2 |- _ ] =>
          let H := fresh in
          assert (H: l2 = l1) by eauto using r_step_fun;
          rewrite H in *; clear H;
          clear H1
    end.

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
      assert (v0 = v) by eauto using Hist.gen_access_fun.
      subst.
      erewrite IHRun; eauto.
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

  Lemma seq_inv_skip:
    forall i1 i2,
    C1.seq i1 i2 = C1.Skip ->
    i1 = C1.Skip /\ i2 = C1.Skip.
  Proof.
    intros.
    destruct i1; simpl in *; subst; auto;
    inversion H.
  Qed.

  Lemma seq_seq_rw:
    forall i1 i2 i3,
    C1.seq (C1.seq i1 i2) i3 = (C1.seq i1 (C1.seq i2 i3)).
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
    Run (C1.seq i1 i2) (prod hs1 hs2).
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
      eapply run_for; eauto.
    - rewrite <- prod_app.
      simpl.
      apply run_loop_cons; eauto.
      remember (C1.i_subst _ _ _).
      assert (Hx := IHRun1 _ _ H1).
      rewrite seq_seq_rw in *.
      assumption.
    - simpl.
      apply run_loop_nil.
      auto.
  Qed.

  Lemma run_inv_seq_1:
    forall i1 hs1,
    Run i1 hs1 ->
    forall i2 hs2 hs,
    Run i2 hs2 ->
    Run (C1.seq i1 i2) hs ->
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


  Coercion NNum: nat >-> nexp.  
  Infix "⇓" := Run (at level 80).
  Notation "⊢" := Hist.Safe.
  Notation "⊨" := Hist.MSafe.
  Infix "*⊆" := AllIncl (at level 80).
  Infix "⊆*" := InclAll (at level 80).
  Infix "*⊆*" := AllInclAll (at level 70).
  Infix "×" := prod (at level 50).
  Infix "↓" := C1.Run (at level 80).
  Notation "i '[' x ':=' n ']'" := (C1.i_subst x n i) (at level 40).

  Lemma run_inv_loop_all_incl_all:
    forall x l i1 i2 hs2,
    Run (C1.Loop x l i1 i2) hs2 ->
    forall hs1,
    Run i2 hs1 ->
    AllInclAll hs1 hs2.
  Proof.
    intros x l i1 i2 hs2 H.
    remember (C1.Loop _ _ _ _).
    generalize dependent i1.
    generalize dependent i2.
    generalize dependent l.
    induction H; intros; inversion Heqi; subst; clear Heqi. {
      assert (IHRun2 := IHRun2 _ _ _ eq_refl _ H1).
      apply all_incl_all_app_r; auto.
    }
    assert (hs = hs1) by eauto using run_fun; subst.
    apply all_incl_all_refl.
  Qed.

  Lemma run_to_all_incl:
    forall i h,
    C1.Run i h ->
    forall hs,
    Run i hs ->
    AllIncl hs h.
  Proof.
    intros i h H; induction H; intros.
    - inversion H; subst; clear H.
      auto using all_incl_nil_nil.
    - inversion H1; subst; clear H1.
      run_clean.
      assert (AllIncl hs0 h) by auto.
      auto using all_incl_prepend.
    - inversion H1; subst; clear H1.
      run_clean.
      auto.
    - inversion H1; subst; clear H1.
      apply run_inv_seq in H8.
      destruct H8 as (hs3, (hs4, (?, (Hr1, Hr2)))); subst.
      assert (IHRun1 := IHRun1 _ Hr1).
      assert (IHRun2 := IHRun2 _ H9).
      apply C1.run_inv_loop in H0.
      destruct H0 as (ha, (hb, (Ha, (Hb, ?)))).
      subst.
      eapply run_inv_loop_all_incl_all in Hr2; eauto.
      apply all_incl_app.
      + apply all_incl_prod.
        * auto using all_incl_appl.
        * apply all_incl_appr.
          apply all_incl_all_incl_all with (ls2:=hs2); auto.
      + auto using all_incl_appr.
    - inversion H0; subst; clear H0.
      auto.
  Qed.

  Theorem completeness:
    forall i h,
    C1.Run i h ->
    forall hs,
    Run i hs ->
    Hist.Safe h ->
    Hist.MSafe hs.
  Proof.
    intros.
    assert (AllIncl hs h) by eauto using run_to_all_incl.
    eauto using Hist.safe_to_msafe.
  Qed.

  Lemma run_nonempty:
    forall i hs,
    Run i hs ->
    hs <> [].
  Proof.
    intros.
    induction H.
    - intros N; inversion N.
    - destruct hs. {
        contradiction.
      }
      simpl.
      intros N; inversion N.
    - assumption.
    - destruct hs1. {
        contradiction.
      }
      intros N; inversion N.
    - assumption.
  Qed.

  Lemma run_to_incl_all:
    forall i h,
    C1.Run i h ->
    forall hs,
    Run i hs ->
    InclAll h hs.
  Proof.
    intros i h H; induction H; intros.
    - apply incl_all_nil.
    - inversion H1; subst; clear H1; run_clean.
      assert (hs0 <> []) by eauto using run_nonempty.
      apply IHRun in H6; clear IHRun.
      apply incl_all_app.
      + auto using incl_all_prepend_l.
      + auto using incl_all_prepend_r.
    - inversion H1; subst; clear H1; run_clean.
      auto.
    - inversion H1; subst; clear H1; run_clean.
      apply run_inv_seq in H8.
      destruct H8 as (hs3, (hs4, (?, (Hr1, Hr2)))); subst.
      assert (hs4 <> nil) by eauto using run_nonempty.
      assert (IHRun1 := IHRun1 _ Hr1).
      assert (IHRun2 := IHRun2 _ H9).
      eapply run_inv_loop_all_incl_all in Hr2; eauto.
      apply incl_all_app.
      + apply incl_all_app_l.
        auto using incl_all_prod_l.
      + apply incl_all_app_r.
        auto.
    - inversion H0; subst; clear H0.
      auto.
  Qed.

  Theorem soundness:
    forall i h,
    C1.Run i h ->
    forall hs,
    Run i hs ->
    Hist.MSafe hs ->
    Hist.Safe h.
  Proof.
    intros.
    assert (InclAll h hs) by eauto using run_to_incl_all.
    eauto using Hist.msafe_to_safe.
  Qed.

  Corollary correctness:
    forall i h hs,
    C1.Run i h ->
    Run i hs ->
    Hist.MSafe hs <-> Hist.Safe h.
  Proof.
    intros.
    split; eauto using completeness, soundness.
  Qed.

End Defs.

Module Examples.
  Import Conc1.Examples.
(*
  Definition step := 
  (* Helper function *)
  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match step s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.

  Let i1 := C1.Acc (add (NVar TID) (NVar (variable "x")), BBool true) C1.Skip.
  Definition BAD :=
    C1.For (variable "x") (NNum 0, NNum 2) i1 C1.Skip.

  Compute run 8 [([], BAD)].

  Definition GOOD1 :=
    let x := variable "x" in
    C1.For x (NNum 0, NNum 2) (
      C1.Acc (NVar x, NRel NEq (NVar TID) (NVar x)) C1.Skip
    ) C1.Skip.

  Compute run 8 [([], GOOD1)].
*)
End Examples.

