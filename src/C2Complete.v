Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Sets.Ensembles.
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
Require Import SetTh.
Import ListNotations.
Require Import Conc2.
Require Import RangeList.
Require Import C2Compiler.
Section Compiler.
  Import Conc1.
  Section Defs.
  Context {A:Access}.
  Variable TID_COUNT: nat.
  Variable TID : var.
  Variable T1: var.
  Variable T2: var.
  Variable t1_neq_tid: T1 <> TID.
  Variable t2_neq_tid: T2 <> TID.
  Variable t1_neq_t2: T1 <> T2.
  Variable tid_ge_2: TID_COUNT > 2.
  
  Ltac remove_eq ta tb :=
  destruct (Set_VAR.MF.eq_dec ta tb);
    try contradiction; simpl in *.

  Lemma access_step_subst_1:
    forall t1 t2 e v,
    ~ access_in T1 e ->
    ~ access_in T2 e ->
    access_step
       (access_subst T2 (NNum t2)
          (access_subst T1 (NNum t1) (access_subst TID (NVar T1) e)), 
       NNum t1) v ->
    access_step
       (access_subst TID (NNum t1) e, NNum t1) v.
  Proof.
    intros.
    rename H1 into Hx.
    rewrite access_subst_subst_trans in Hx; auto.
    rewrite access_subst_subst_neq in Hx; auto.
    rewrite access_subst_not_in with (x:=T2) in Hx; auto.
  Qed.

  Lemma m_in_prepend_iff:
    forall A x l ls,
    ls <> [] ->
    MIn (A:=A) x (prepend l ls) <-> (List.In x l \/ MIn x ls).
  Proof.
    intros.
    split; intros.
    - apply m_in_prepend_inv in H0.
      assumption.
    - destruct H0. {
        apply m_in_prepend_l; auto.
      }
      apply m_in_prepend; auto.
  Qed.

  Definition Member {A} l a := In (A:=A) a l.

  Inductive PMember {A : Type} {B: Type} (P: B -> list A -> Prop) (ls : B) (a:A)  : Prop :=
 | p_member_def :
    forall l,
    P ls l -> Member l a -> PMember P ls a.

  Definition MMember {A} := PMember (@Member (list A)).
  Definition MMMember {A} := PMember (@MMember (list A)).
  Lemma not_in_mmember:
    forall A (x:A),
    ~ MMember [] x.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    unfold Member in *.
    contradiction.
  Qed.

  Lemma not_in_mmmember:
    forall A (x:A),
    ~ MMMember [] x.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    apply not_in_mmember in H.
    assumption.
  Qed.

  Lemma mmember_app_l:
    forall A (x:A) l1 l2,
    MMember l1 x ->
    MMember (l1 ++ l2) x.
  Proof.
    unfold MMember.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    eapply p_member_def; eauto using in_or_app.
  Qed.

  Lemma mmember_app_r:
    forall A (x:A) l1 l2,
    MMember l2 x ->
    MMember (l1 ++ l2) x.
  Proof.
    unfold MMember.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    eapply p_member_def; eauto using in_or_app.
  Qed.

  Lemma mmember_def_2:
    forall A (x:A) l ls,
    In x l ->
    In l ls ->
    MMember ls x.
  Proof.
    intros.
    apply p_member_def with (l0:=l); auto.
  Qed.

  Lemma mmember_def:
    forall A (x:A) l ls,
    Member l x ->
    Member ls l ->
    MMember ls x.
  Proof.
    apply mmember_def_2.
  Qed.


  Lemma mmember_inv_app:
    forall A (x:A) l1 l2,
    MMember (l1 ++ l2) x ->
    MMember l1 x \/ MMember l2 x.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold Member in *.
    apply in_app_or in H0.
    destruct H0. {
      left.
      eauto using mmember_def.
    }
    right.
    eauto using mmember_def.
  Qed.

  Lemma mmember_inv_concat:
    forall A (x:A) ls,
    MMember (List.concat ls) x ->
    exists l, List.In l ls /\ MMember l x.
  Proof.
    induction ls; simpl; intros.
    - apply not_in_mmember in H.
      contradiction.
    - apply mmember_inv_app in H.
      destruct H. {
        exists a.
        auto.
      }
      apply IHls in H.
      destruct H as (l, (Hi, Hm)).
      exists l.
      auto.
  Qed.

  Lemma mmmember_def:
    forall A (x:A) l1 l2 ls,
    Member l1 x ->
    Member l2 l1 ->
    Member ls l2 ->
    MMMember ls x.
  Proof.
    intros.
    apply p_member_def with (l:=l1); auto.
    eauto using mmember_def.
  Qed.

  Lemma mmmember_to_mmember:
    forall A ls (x:A),
    MMMember ls x ->
    MMember (List.concat ls) x.
  Proof.
    induction ls; intros.
    - apply not_in_mmmember in H.
      contradiction.
    - inversion H; subst; clear H.
      simpl.
      inversion H0; subst; clear H0.
      inversion H; subst; clear H. {
        apply mmember_app_l.
        eauto using mmember_def.
      }
      apply mmember_app_r.
      apply IHls.
      eauto using mmmember_def.
  Qed.

  Lemma mmmember_eq:
    forall A a x ls,
    @MMember A a x ->
    MMMember (a :: ls) x.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply mmmember_def with (l2:=a); eauto.
    apply in_eq.
  Qed.

  Lemma mmmember_cons:
    forall A a x ls,
    @MMMember A ls x ->
    MMMember (a :: ls) x.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply mmmember_def; eauto.
    apply in_cons; auto.
  Qed.

  Lemma mmember_to_mmmember:
    forall A ls (x:A),
    MMember (List.concat ls) x ->
    MMMember ls x.
  Proof.
    induction ls; intros. {
      apply not_in_mmember in H.
      contradiction.
    }
    simpl in *.
    apply mmember_inv_app in H.
    destruct H. {
      auto using mmmember_eq.
    }
    apply IHls in H.
    auto using mmmember_cons.
  Qed.

  Lemma mmember_iff_mmmember:
    forall A ls (x:A),
    MMember (List.concat ls) x <-> MMMember ls x.
  Proof.
    split; auto using mmember_to_mmmember, mmmember_to_mmember.
  Qed.


  Lemma mmember_concat_rw:
    forall A ls,
    Equiv (MMember (List.concat ls)) (@MMMember A ls).
  Proof.
    auto using equiv_def, mmmember_to_mmember, mmember_to_mmmember.
  Qed.

  Lemma mmember_rw:
    forall A ls (x:A),
    MMember ls x <-> MIn x ls.
  Proof.
    split; intros.
    - inversion H; subst; clear H.
      eauto using m_in_def.
    - inversion H; subst; clear H.
      eauto using mmember_def.
  Qed.

  Lemma mmember_prepend_iff:
    forall A l ls (x:A),
    ls <> [] ->
    MMember (prepend l ls) x <-> Member l x \/ MMember ls x.
  Proof.
    intros.
    repeat rewrite mmember_rw.
    apply m_in_prepend_iff; assumption.
  Qed.

  Lemma mmember_prepend_rw:
    forall A (l:list A) ls,
    ls <> [] ->
    Equiv (MMember (prepend l ls)) (Either (Member l) (MMember ls)).
  Proof.
    intros.
    apply equiv_def; intros a Ha.
    - apply mmember_prepend_iff in Ha; auto.
    - apply mmember_prepend_iff in Ha; auto.
  Qed.

  Lemma member_concat_rw:
    forall A ls,
    Equiv (Member (List.concat ls)) (@MMember A ls).
  Proof.
    intros.
    apply equiv_def; unfold Member; intros.
    - rewrite mmember_rw.
      auto using in_concat_to_m_in.
    - rewrite mmember_rw in *.
      auto using m_in_to_in_concat.
  Qed.

  Lemma incl_mmember_nil_nil:
    forall A P,
    @Incl A (MMember [[]]) P.
  Proof.
    intros.
    apply incl_def.
    intros.
    rewrite mmember_rw in H.
    apply m_in_nil_nil in H.
    contradiction.
  Qed.

  Lemma incl_mmember_nil:
    forall A P,
    @Incl A (MMember []) P.
  Proof.
    intros.
    apply incl_def.
    intros.
    rewrite mmember_rw in H.
    apply m_in_nil in H.
    contradiction.
  Qed.
(*
  Lemma c2_branch:
    forall f l i1 i2 x hs hs',
    hs' = ((List.concat (List.map f l)) ++ hs) ->
    (forall n, List.In n l -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)) ->
    C2.Run i2 hs ->
    C2.Run (C2.Branch x l i1 i2) hs'.
  Proof.
    induction l; intros; subst.
    - simpl.
      apply C2.run_branch_nil; auto.
    - simpl.
      rewrite app_assoc_reverse.
      Search (_ ++ _ ++ _).
      apply C2.run_branch_cons. {
        auto using in_eq.
      }
      apply IHl with (hs:=hs); auto.
      intros.
      apply H0.
      auto using in_cons.
  Qed.
*)
  Notation history := (list access_val).
  Definition mk_empty_1 n1 n2 : list history :=
    List.concat (map (fun _ => [[]]) (range_list n1 n2)) ++ [[]].

  Lemma run_skip_1:
    forall n1 n2,
    C2.Run (C2.Decl T2 (NNum n1, NNum n2) C2.Skip C2.Skip) (mk_empty_1 n1 n2).
  Proof.
    intros.
    apply C2.run_decl with (l:=range_list n1 n2).
    - apply C2.r_step_range_list.
    - apply C2.run_branch_map_def with (f:=fun x => [[]]) (hs:=[[]]).
      + rewrite prod_nil_nil_r.
        reflexivity.
      + intros.
        simpl.
        apply C2.run_skip.
      + apply C2.run_skip.
  Qed.

  Definition mk_empty_2 n1 n2 : list history :=
    List.concat (map (fun n => mk_empty_1 0 n) (range_list n1 n2))
     ++ [[]].
   

  Lemma run_skip:
    C2.Run (translate TID_COUNT TID T1 T2 C1.Skip) (mk_empty_2 1 TID_COUNT).
  Proof.
    unfold translate.
    simpl.
    apply C2.run_decl with (l:=range_list 1 TID_COUNT).
    - apply C2.r_step_range_list.
    - apply C2.run_branch_map_def with (f:=fun n => mk_empty_1 0 n) (hs:=[[]]).
      + rewrite prod_nil_nil_r.
        reflexivity.
      + intros.
        simpl.
        remove_eq T1 T1.
        remove_eq T1 T2.
        apply run_skip_1.
      + apply C2.run_skip.
  Qed.

  Definition add {A:Type} f (a:nat) (v:A) :=
    (fun n => if PeanoNat.Nat.eq_dec n a then v else f n).

  Lemma add_eq_rw:
    forall A f a (hs1:A),
    add f a hs1 a = hs1.
  Proof.
    unfold add; intros.
    destruct (PeanoNat.Nat.eq_dec a a). {
      reflexivity.
    }
    contradiction.
  Qed.

  Lemma add_neq_rw:
    forall A f a b (x:A),
    a <> b ->
    add f a x b = f b.
  Proof.
    unfold add.
    intros.
    destruct (PeanoNat.Nat.eq_dec b a). {
      subst.
      contradiction.
    }
    reflexivity.
  Qed.

  Lemma map_add_rw_not_in:
    forall A a f l (x:A),
    ~ List.In a l ->
    map (add f a x) l = map f l.
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    assert (a <> a0). {
      intros N.
      subst.
      contradict H.
      auto using in_eq.
    }
    rewrite add_neq_rw; auto.
    assert (Hi : ~ In a l). {
      intros N.
      contradict H.
      auto using in_cons.
    }
    assert (IHl := IHl x Hi).
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma c2_run_branch_inv:
    forall l i1 i2 x hs',
    C2.Run (C2.Branch x l i1 i2) hs' ->
    NoDup l ->
    exists f hs,
    hs' = ((List.concat (List.map f l)) ++ hs) /\ C2.Run i2 hs
    /\
    (forall n, List.In n l -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      simpl.
      exists (fun x => []).
      exists hs'.
      repeat split; auto.
      intros.
      contradiction.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply IHl in H8; auto.
    destruct H8 as (f, (hs3, (?,(?,Hr)))).
    subst.
    exists (add f a hs1).
    exists hs3.
    simpl.
    repeat split; auto.
    - rewrite add_eq_rw.
      rewrite app_assoc.
      rewrite map_add_rw_not_in; auto.
    - intros.
      destruct H. {
        subst.
        rewrite add_eq_rw.
        assumption.
      }
      assert (a <> n). {
        intros N; subst.
        contradiction.
      }
      rewrite add_neq_rw; auto.
  Qed.

  Definition branch_iter {A:Type} n1 n2 f :=
    List.concat (@List.map nat (list A) f (range_list n1 n2)).


(*
  Lemma c2_run_decl_inv:
    forall n1 n2 i1 i2 x hs',
    C2.Run (C2.Decl x (NNum n1, NNum n2) i1 i2) hs' ->
    exists f hs,
    hs' = branch_iter n1 n2 f ++ hs /\
    C2.Run i2 hs /\
    (forall n, n1 <= n < n2 -> C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)).
  Proof.
    intros.
    unfold branch_iter.
    inversion H; subst; clear H.
    apply r_step_to_range_list in H5.
    subst.
    apply c2_run_branch_inv in H6.
    destruct H6 as (f, (hs1, (?, (Hr1, Hr2)))).
    subst.
    exists f.
    exists hs1.
    repeat split; auto.
    intros.
    apply Hr2.
    - apply range_list_in_iff; assumption.
    - auto using range_list_no_dup.
  Qed.
*)
  Lemma subst_t1_tid_eq:
    forall v e,
    ~ C2.In T1 e ->
    C2.i_subst T1 v (C2.i_subst TID (NVar T1) e) =
    C2.i_subst TID v e.
  Proof.
    intros.
    rewrite C2.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_tid_eq:
    forall v e,
    ~ C2.In T2 e ->
    C2.i_subst T2 v (C2.i_subst TID (NVar T2) e) =
    C2.i_subst TID v e.
  Proof.
    intros.
    rewrite C2.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_neq:
    forall e n1 n2,
    ~ C2.In T2 e ->
    C2.i_subst T2 (NNum n2) (C2.i_subst TID (NNum n1) e)
    =
    C2.i_subst TID (NNum n1) e.
  Proof.
    intros.
    rewrite C2.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply C2.in_i_subst_neq in N; auto.
    intros M.
    inversion M.
  Qed.

  Lemma subst_t1_t2_neq:
    forall v e,
    ~ C2.In T1 e ->
    C2.i_subst T1 v (C2.i_subst TID (NVar T2) e)
    = 
    C2.i_subst TID (NVar T2) e.
  Proof.
    intros.
    rewrite C2.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply C2.in_subst_inv_in in N; auto.
  Qed.


  Lemma rw_1 e (t1_nin: ~ C2.In T1 (proj TID e)):
    forall n1,
        C2.i_subst T1 (NNum n1)
           (C2.Decl T2 (NNum 0, NVar T1)
              (C2.seq (do_proj TID T1 e)
                 (do_proj TID T2 e)) C2.Skip)
   =
       C2.Decl T2 (NNum 0, NNum n1)
        (C2.seq (C2.i_subst TID (NNum n1) (proj TID e))
                (do_proj TID T2 e)) C2.Skip.
  Proof.
    intros.
    simpl.
    remove_eq T1 T2.
    remove_eq T1 T1.
    rewrite C2.i_subst_seq.
    unfold do_proj in *.
    rewrite subst_t1_tid_eq; auto.
    rewrite subst_t1_t2_neq; auto.
  Qed.

  Lemma nin_t1_tid:
    ~ NIn T1 (NVar TID).
  Proof.
    intros N.
    inversion N.
    contradiction.
  Qed.

  Lemma rw_2:
    forall e n1 n2,
    ~ C1.In T2 e ->
    C2.i_subst T2 (NNum n2)
       (C2.seq
          (C2.i_subst TID (NNum n1) (proj TID e))
          (do_proj TID T2 e))
    = 
    C2.seq
      (C2.i_subst TID (NNum n1) (proj TID e))
      (C2.i_subst TID (NNum n2) (proj TID e)).
  Proof.
    intros.
    rewrite C2.i_subst_seq.
    assert (~ C2.In T2 (proj TID e)). {
      intros N.
      eapply in_proj_to_in in N; eauto.
    }
    rewrite subst_t2_neq; auto.
    unfold do_proj.
    rewrite subst_t2_tid_eq; auto.
  Qed.

(*
  Lemma c2_decl:
     forall f n1 n2 i1 i2 x hs hs',
     hs' = List.concat (map f (range_list n1 n2)) ++ hs ->
     (forall n,
      n1 <= n < n2 ->
      C2.Run (C2.seq (C2.i_subst x (NNum n) i1) i2) (f n)) ->
    C2.Run i2 hs -> C2.Run (C2.Decl x (NNum n1, NNum n2) i1 i2) hs'.
  Proof.
    intros.
    apply C2.run_decl with (range_list n1 n2).
    - apply r_step_range_list.
    - apply c2_branch with (f:=f) (hs:=hs); auto.
      intros.
      apply range_list_in_iff in H2.
      auto.
  Qed.
*)
  Lemma map_rw_repeat:
    forall A B m l,
    @map A B (fun _ : A => m) l = List.repeat m (List.length l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma concat_eq_rw:
    forall A B m l,
    @List.concat (list B) (map (fun _ : A => [m]) l) = List.repeat m (List.length l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Definition summation :=
  List.fold_right Nat.add 0.

  Lemma repeat_app:
    forall A (x:A) n1 n2,
    repeat x (n1 + n2) = repeat x n1 ++ repeat x n2.
  Proof.
    induction n1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHn1.
    reflexivity.
  Qed.

  Lemma concat_eq_nil_rw:
    forall (l:list nat),
    List.concat (map (fun n => repeat (@nil nat) n) l) =
    List.repeat [] (summation l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    rewrite repeat_app.
    reflexivity.
  Qed.

(*
  Lemma div2_add:
    forall n1 n2,
    Nat.Even n1 ->
    Nat.Even n2 -> 
    Nat.div2 (n1 + n2) = Nat.div2 n1 + Nat.div2 n2.
  Proof.
    induction n1; intros. {
      reflexivity.
    }
    (* n1 = S n *)
    simpl.
    destruct n1. {
      (* n1 = 2 *)
      assert (Ho: Nat.Odd 1). {
        apply Nat.odd_spec.
        reflexivity.
      }
      Search (Nat.Odd _).
      apply Nat.Even_Odd_False in Ho; auto.
      contradiction.
    }
    Search (Nat.Even).
  Qed. 
*)
(*
  Lemma asdf:
    forall n,
    n + Nat.div2 (n * S n) = Nat.div2 (n + n * S (S n)).
  Proof.
    intros.
    repeat rewrite Nat.mul_succ_r.
    Search (Nat.div2(_ + _)).
    induction n; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    rewrite <- IHn.
    clear IHn.
    destruct n. {
      simpl.
      reflexivity.
    }
    simpl.
    Search (Nat.div2 _).
  Qed.
  *)
  (*
  Lemma summation_count:
    forall n,
    summation (count n) = Nat.div2 ((S n) * n).
  Proof.
    induction n; intros. {
      reflexivity.
    }
    remember (summation (count (S _))) as m.
    simpl in Heqm.
    rewrite IHn in Heqm; clear IHn.
    rewrite Heqm; clear Heqm.
    simpl.
    destruct n. {
      simpl.
    }
    destruct n. {
      simpl.
      reflexivity.
    }
    simpl.
    
    simpl.
    assert (n = (2*n)/2). {
      simpl.
      rewrite Nat.add_0_r.
      Search (Nat.divmod).
      Nat.div
      rewrite Nat.divmod.
      Search (_ + 0).
    }
    omega.
  Qed.

  Lemma summation_range_list:
    forall 0 n,
    summation (range_list 0 n) = (n * (S (n2 - n1))) / 2.
  Proof.

  Lemma summation_range_list:
    forall n1 n2,
    summation (range_list n1 n2) = ((n2 - n1) * (S (n2 - n1))) / 2.
  Proof.
    intros.
    remember (range_list n1 n2).
    generalize dependent n1.
    generalize dependent n2.
    induction l; intros; symmetry in Heql; apply range_list_to_prop in Heql;
      inversion Heql; subst; clear Heql.
    - assert (R: n2 - n1 = 0) by auto with *.
      rewrite R.
      reflexivity.
    - apply prop_to_range_list in H4.
      symmetry in H4.
      apply IHl in H4; clear IHl.
      remember (summation (a :: l)) as l1.
      simpl in Heql1.
      rewrite H4 in Heql1.
      rewrite Heql1.
      destruct n2. {
        simpl.
        inversion H3.
      }
      rewrite Nat.sub_succ.
      
      Search (S _ - S _).
      simpl.
      simpl.
  Qed.*)
(*
  Lemma concat_eq_nil_rw:
    forall A B f l,
    @List.concat (list B) (map (fun n : A => repeat [] (f n)) l) = List.repeat [] (List.length l * (List.length l - 1)).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.
  *)
  Import C2Notations.
(*
  Lemma c2_run_trans_inv_1 e hs (t1_nin: ~ C1.In T1 e) (t2_nin: ~ C1.In T2 e):
    C2.Run (translate e) hs ->
    exists hss, 
    hs = List.concat hss /\
    forall n1,
      1 <= n1 < TID_COUNT ->
      exists hssb,
      In (List.concat hssb) hss /\
      (forall n2,
       0 <= n2 < n1 ->
       exists hb hc,
         C2.Run (C2.i_subst TID (NNum n1) (proj e)) hb /\
         C2.Run (C2.i_subst TID (NNum n2) (proj e)) hc /\
         In (prod hb hc) hssb /\ In (List.concat hssb) hss)

  .
  Proof.
    intros.
    unfold translate in *.
    apply C2.run_decl_inv_eq in H; auto with *.
    destruct H as (hss, (Ha, Hb)).
    exists hss; split; auto.
    assert (
      forall n1,
     1 <= n1 < TID_COUNT ->
     exists hssb,
    In (List.concat hssb) hss /\
    forall n2 : nat,
     0 <= n2 < n1 ->
     exists hb hc,
       C2.Run (C2.i_subst TID (NNum n1) (proj e)) hb /\
       C2.Run (C2.i_subst TID (NNum n2) (proj e)) hc /\
       In (prod hb hc) hssb /\ In (List.concat hssb) hss
    ). {
      intros n1 Hc.
      assert (Hb := Hb _ Hc).
      destruct Hb as (hsc, (Hb, Hd)).
      assert (X:~ C2.In T1 (proj e)). {
        intros N.
        contradict t1_nin.
        auto using in_proj_to_in.
      }
      rewrite rw_1 in Hb; auto.
      apply C2.run_inv_seq in Hb.
      destruct Hb as (hs1, (hs2, (?, (Hb, He)))).
      inversion He; subst; clear He.
      rewrite prod_nil_nil_r in *.
      apply C2.run_decl_inv_eq in Hb; auto with *.
      destruct Hb as (hssb, (?, Hb)).
      subst.
      assert (forall n2,
         0 <= n2 < n1 ->
        exists hb hc,
        C2.Run (C2.i_subst TID (NNum n1) (proj e)) hb /\
        C2.Run (C2.i_subst TID (NNum n2) (proj e)) hc /\
        In (prod hb hc) hssb /\
        In (List.concat hssb) hss
         
         ). {
        intros n2 Ha.
        assert (Hb := Hb _ Ha).
        destruct Hb as (hs, (Hb,He)).
        apply C2.run_inv_seq in Hb.
        destruct Hb as (ha, (hb, (?, (Hb, Hf)))).
        inversion Hf; subst; clear Hf.
        rewrite prod_nil_nil_r in *.
        rewrite rw_2 in Hb; auto.
        apply C2.run_inv_seq in Hb.
        destruct Hb as (hb, (hc, (Hb, (Hf,Hg)))).
        subst.
        exists hb.
        eauto.
      }
      subst.
      eauto.
    }
    auto.
  Qed.
*)


  Lemma run_trans_inv e  (t1_nin: ~ C1.In T1 e) (t2_nin: ~ C1.In T2 e) hs:
    C2.Run (translate TID_COUNT TID T1 T2 e) hs ->
    exists f1,
    hs = List.concat (C2.branch_iter 1 TID_COUNT f1) ++ [[]]
    /\
    forall n1,
    1 <= n1 < TID_COUNT ->
    exists f2,
    f1 n1 = List.concat (C2.branch_iter 0 n1 f2) ++ [[]] /\
    forall n2,
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      C2.Run (C2.i_subst TID (NNum n1) (proj TID e)) hs1 /\
      C2.Run (C2.i_subst TID (NNum n2) (proj TID e)) hs2

  .
  Proof.
    intros.
    unfold translate in *.
    apply C2.run_decl_inv_map in H.
    destruct H as (ms, (m, (?, (Hs, H)))).
    inversion Hs; subst; clear Hs.
    Search (prod _ [[]]).
    rewrite prod_nil_nil_r.
    apply C2.decl_map_inv in H.
    destruct H as (f1, (R1, Hf)).
    exists f1.
    rewrite R1.
    split; auto.
    intros n1 Ha.
    apply Hf in Ha; clear Hf.
    assert (X:~ C2.In T1 (proj TID e)). {
      intros N.
      contradict t1_nin.
      eauto using in_proj_to_in.
    }
    rewrite rw_1 in Ha; auto.
    apply C2.run_decl_inv_map in Ha.
    destruct Ha as (ms2, (hs, (R2,(Ha,Hc)))).
    apply C2.decl_map_inv in Hc.
    destruct Hc as (f2, (R3, Hc)). 
    inversion Ha; subst; clear Ha.
    exists f2.
    rewrite R2.
    assert (forall n2, 
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      C2.Run (C2.i_subst TID (NNum n1) (proj TID e)) hs1 /\
      C2.Run (C2.i_subst TID (NNum n2) (proj TID e)) hs2
    ). {
      intros n2 Hb.
      apply Hc in Hb; clear Hc.
      rewrite rw_2 in Hb; auto.
      apply C2.run_inv_seq in Hb.
      destruct Hb as (hsa, (hsb, (?,(Hr,Hs)))).
      eauto.
    }
    rewrite prod_nil_nil_r.
    eauto.
  Qed.

  Lemma concat_map_eq_repeat:
    forall A m n1 n2,
    @List.concat (list A) (map (fun _ : nat => [m]) (range_list n1 n2)) =
    repeat m (n2 - n1).
  Proof.
    intros.
    rewrite concat_eq_rw.
    rewrite range_list_fun_length.
    reflexivity.
  Qed.
(*
  Lemma prod_cons_l:
    forall A l1 l2 x,
    @prod A l1 (x :: l2) = prod l1 [x] ++ prod l1 l2.
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl1.
  Qed.
*)
(*
  Fixpoint interleave {A:Type} (l1 l2:list A): list A :=
  match l1, l2 with
  | x1::l1, x2::l2 => x1::x2::(@interleave A l1 l2)
  | [], _ => l2
  | _, _ => l1
  end.
  *)
  (*
  Lemma map_app_prod:
    forall A B (f1:A->list B) f2 l,
    map (fun x => f1 x ++ f2 x) l = interleave (map f1 l) (map f2 l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    Search (prod _ (_ :: _)).
    rewrite IHl.
    assert (
      prod l1 l2 =
      prepend (f1 a) l2 ++ prod l1 (f2 a :: l2)
    )
    simpl.
  Qed.
*)
(*
  Lemma branch_iter_eq_func:
    forall A f1 f2 n1 n2,
    (forall n, n1 <= n < n2 -> f1 n = f2 n) ->
    @branch_iter A n1 n2 f1 = branch_iter n1 n2 f2.
  Proof.
    intros.
    unfold branch_iter.
    rewrite map_rw_func with (f4:=f2); auto.
    intros.
    auto using range_list_inv_in_2.
  Qed.
*)
(*

  Lemma map_mem_equiv_func:
    forall A f1 f2 l,
    (forall (x:A), List.In x l -> f1 x == f2 x) ->
    List.concat (map f1 l) == List.concat (map f2 l).
  Proof.
    induction l; intros; auto; simpl in *. {
      reflexivity.
    }
    assert (Hx: (forall x : A0, In x l -> f1 x == f2 x)) by auto.
    assert (IHl := IHl Hx).
    rewrite IHl.
    assert (R: f1 a == f2 a) by auto.
    rewrite R.
    reflexivity.
  Qed.
*)
(*
  Lemma branch_iter_equiv_func:
    forall f1 f2 n1 n2,
    (forall n, n1 <= n < n2 -> f1 n == f2 n) ->
    branch_iter n1 n2 f1 == branch_iter n1 n2 f2.
  Proof.
    intros.
    unfold branch_iter.
    rewrite (map_mem_equiv_func _ f1 f2).
    - reflexivity.
    - intros.
      apply range_list_inv_in_2 in H0.
      auto.
  Qed.
*)
  Lemma mk_empty_1_rw:
    forall n1 n2,
    mk_empty_1 n1 n2 == [].
  Proof.
    intros.
    unfold mk_empty_1.
    rewrite concat_eq_rw.
    rewrite C2.mem_equiv_nil_rw.
    rewrite C2.mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Lemma mk_empty_2_rw:
    forall n1 n2,
    mk_empty_2 n1 n2 == [].
  Proof.
    unfold mk_empty_2.
    intros.
    rewrite C2.mem_equiv_cons_nil_rw.
    rewrite app_nil_r.
    remember (map _ _).
    destruct (list_eq_nil l) as [R|Hne]. {
      rewrite R.
      reflexivity.
    }
    apply C2.mem_equiv_concat_refl_rw; auto.
    intros.
    subst.
    apply in_map_iff in H.
    destruct H as (n, (?, Hi)).
    subst.
    rewrite mk_empty_1_rw.
    reflexivity.
  Qed.
(*
  Lemma branch_iter_absorb:
    forall n1 n2 m,
    n1 < n2 ->
    branch_iter n1 n2 (fun _ : nat => m) == m.
  Proof.
    intros.
    unfold branch_iter.
    rewrite map_rw_repeat.
    rewrite range_list_fun_length.
    rewrite C2.mem_equiv_concat_repeat_rw. {
      reflexivity.
    }
    auto with *.
  Qed.
*)

  Lemma t1_not_in_proj_skip:
    ~ C2.In T1 (proj TID C1.Skip).
  Proof.
    simpl.
    intros N.
    inversion N.
  Qed.

  Lemma repeat_nil_rw_1:
    forall {A} n,
    repeat (@nil A) n ++ [[]] = [] :: repeat [] n.
  Proof.
    induction n; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma mk_empty_1_spec:
    forall n1 n2,
    mk_empty_1 n1 n2 = @repeat history [] (S (n2 - n1)).
  Proof.
    intros.
    unfold mk_empty_1.
    rewrite concat_eq_rw.
    simpl.
    rewrite range_list_fun_length.
    rewrite repeat_nil_rw_1.
    reflexivity.
  Qed.

  Lemma mk_empty_2_spec:
    forall n1 n2,
    exists n,
    mk_empty_2 n1 n2 = @repeat history [] (S n).
  Proof.
    intros.
    unfold mk_empty_2.
    remember (range_list n1 n2).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    induction Heql.
    - simpl.
      exists 0.
      reflexivity.
    - destruct IHHeql as (n, Hr).
      exists (S (low - 0) + n).
      simpl.
      rewrite app_assoc_reverse.
      rewrite Hr; clear Hr.
      rewrite mk_empty_1_spec.
      rewrite PeanoNat.Nat.sub_0_r.
      repeat rewrite <- repeat_app.
      rewrite PeanoNat.Nat.add_succ_r.
      reflexivity.
  Qed.
(*
  Lemma prepend_equiv:
    forall m1 m2 m3 m4,
    m1 == m3 ->
    m2 == m4 ->
    prepend m1 m2 == prepend m3 m4.
*)
  Lemma mem_equiv_cons_eq_nil:
    forall h,
    [h] == [] ->
    h = [].
  Proof.
    intros.
    (*unfold C2.MemEquiv in H.*)
    destruct h as [|a h]. {
      reflexivity.
    }
    assert (Hi: MPairIn (a,a) [a::h]). {
      apply m_pair_in_eq.
      apply pair_in_refl.
      apply in_eq.
    }
    apply H in Hi.
    apply m_pair_in_nil in Hi.
    contradiction.
  Qed.

  Lemma mequiv_cons_nil_inv:
    forall h,
    ([] :: h) == [] ->
    h == [].
  Proof.
    induction h; intros. {
      reflexivity.
    }
    split; intros. {
      assert (Hi: MPairIn p ([] :: a :: h)) by auto using m_pair_in_cons.
      apply H in Hi.
      assumption.
    }
    apply m_pair_in_nil in H0.
    contradiction.
  Qed.

  Lemma mem_equiv_nil_to_repeat:
    forall h,
    h == [] ->
    exists n,
    h = repeat [] n.
  Proof.
    induction h; intros. {
      exists 0.
      reflexivity.
    }
    destruct a. {
      apply mequiv_cons_nil_inv in H.
      apply IHh in H.
      destruct H as (n, H).
      exists (S n).
      simpl.
      rewrite H.
      reflexivity.
    }
    assert (Hi: MPairIn (a,a) ((a::a0)::h)). {
      apply m_pair_in_eq.
      apply pair_in_refl.
      apply in_eq.
    }
    apply H in Hi.
    apply m_pair_in_nil in Hi.
    contradiction.
  Qed.

  Lemma prod_repeat_rw:
    forall m n,
    m == prod (repeat [] (S n)) m.
  Proof.
    induction n. {
      simpl.
      rewrite prepend_nil.
      rewrite app_nil_r.
      reflexivity.
    }
    simpl in *.
    rewrite prepend_nil in *.
    rewrite <- IHn.
    rewrite C2.mem_equiv_app_refl_rw.
    reflexivity.
  Qed.

  Lemma prod_absorb_l:
    forall m1,
    m1 <> [] ->
    m1 == [] ->
    forall m2,
    m2 == prod m1 m2.
  Proof.
    intros.
    apply mem_equiv_nil_to_repeat in H0.
    destruct H0 as (n, Hr).
    subst.
    destruct n. {
      contradiction.
    }
    apply prod_repeat_rw.
  Qed.

  Lemma prod_mk_empty_2_rw:
    forall m,
    m == prod (mk_empty_2 1 TID_COUNT) m.
  Proof.
    intros.
    apply prod_absorb_l.
    - unfold mk_empty_2.
      destruct (List.concat _). {
        intros N.
        inversion N.
      }
      intros N; inversion N.
    - apply mk_empty_2_rw.
  Qed.

  Lemma c2_run_acc_inv_1 e hs i (t1_nin: ~ C1.In T1 (C1.Acc e i)) (t2_nin: ~ C1.In T2 (C1.Acc e i)):
    C2.Run (translate TID_COUNT TID T1 T2 (C1.Acc e i)) hs ->
    exists f1,
    hs = branch_iter 1 TID_COUNT f1 ++ [[]]
    /\
    forall n1 n2,
    1 <= n1 < TID_COUNT ->
    0 <= n2 < n1 ->
    exists f2 hs1 hs2,
    f1 n1 = branch_iter 0 n1 f2 ++ [[]] /\
    f2 n2 = prod hs1 hs2/\
    C2.Run
        (C2.Acc (access_subst TID (NNum n1) e, NNum n1)
           (C2.i_subst TID (NNum n1) (proj TID i))) hs1 /\
    C2.Run
        (C2.Acc (access_subst TID (NNum n2) e, NNum n2)
           (C2.i_subst TID (NNum n2) (proj TID i))) hs2
   .
  Proof.
    intros.
    (* ---- *)
    apply run_trans_inv in H; auto.
    destruct H as (f1, (?, Hf)).
    exists f1.
    split; auto.
    intros n1 n2 Hn1 Hn2.
    assert (Hf := Hf _ Hn1).
    destruct Hf as (f2, (?, Hf2)).
    exists f2.
    assert (Hf2 := Hf2 _ Hn2).
    destruct Hf2 as (hs1, (hs2, (?, (Hr1, Hr2)))).
    simpl in *.
    remove_eq TID TID.
    exists hs1.
    exists hs2.
    auto.
  Qed.

  Lemma translate_seq e1 (t1_nin1: ~ C1.In T1 e1) (t2_nin1: ~ C1.In T2 e1):
    forall e2,
    ~ C1.In T1 e2 ->
    ~ C1.In T2 e2 ->
    forall m1,
    C2.Run (translate TID_COUNT TID T1 T2 (C1.seq e1 e2)) m1 ->
    exists m2,
    m1 == m2 /\ C2.Run (C2.seq (translate TID_COUNT TID T1 T2 e1) (translate TID_COUNT TID T1 T2 e2)) m2.
  Proof.
    induction e1; intros e2 t1_nin2 t2_nin2 m1 Hr.
    - simpl in Hr.
      assert (Hx := Hr).
      exists (prod (mk_empty_2 1 TID_COUNT) m1).
      split. {
        apply prod_mk_empty_2_rw.
      }
      apply C2.run_seq; auto using run_skip.
    - simpl in Hr.
      apply c2_run_acc_inv_1 in Hr.
      + destruct Hr as (f1, (?, Hf)).
        subst.
        rewrite 
      apply run_translate_inv in Hr.
      remove_eq TID TID.
      apply run_trans_inv in Hr.
      + destruct Hr as (f1, (?, Hf)).
        subst.
        simpl.
        exists (List.concat (C2.branch_iter 1 TID_COUNT f1) ++ [[]]).
        split. {
          reflexivity.
        }
        remove_eq TID TID.
        remove_eq TID TID.
        simpl.
        apply C2.run_seq.
        (*
        apply C2.run_decl_map_def with (f:=f) .
        Search (C2.seq _ C2.Skip).
        rewrite C2.seq_nil_rw.
      unfold translate in Hr.
      simpl in Hr.
      Search (C2.seq _ C2.Skip).*)
  Admitted.


(*

  Lemma c2_run_acc_inv_2 e hs i (t1_nin: ~ C1.In T1 (C1.Acc e i)) (t2_nin: ~ C1.In T2 (C1.Acc e i)):
    C2.Run (translate (C1.Acc e i)) hs ->
    exists f1,
    hs = branch_iter 1 TID_COUNT f1 ++ [[]]
    /\
    forall n1 n2,
    1 <= n1 < TID_COUNT ->
    0 <= n2 < n1 ->
    exists f2 v1 v2 hr1 hr2,
    f1 n1 = branch_iter 0 n1 f2 ++ [[]] /\
    f2 n2 = prod (prepend v1 hr1) (prepend v2 hr2) /\
    access_step (access_subst TID (NNum n1) e, NNum n1) v1 /\
    access_step (access_subst TID (NNum n2) e, NNum n2) v2 /\
    C2.Run (C2.i_subst TID (NNum n1) (proj i)) hr1 /\
    C2.Run (C2.i_subst TID (NNum n2) (proj i)) hr2
   .
  Proof.
   Search (prod (prepend _ _) _).
   rewrite <- prepend_prod.
  Qed.
  *)
(*
  Lemma translate_acc_inv:
    forall e i hs,
    C2.Run (translate (C1.Acc e i)) hs ->
    exists hs1 hs2,
    hs = prod hs1 hs2 /\
    C2.Run (translate (C1.Acc e C1.Skip)) hs1 /\
    C2.Run (translate i) hs2.
  Proof.
    induction i; intros.
    - exists (prod hs (mk_empty_2 1 TID_COUNT)).
      exists (mk_empty_2 1 TID_COUNT).
      repeat split; auto using c2_run_skip.
      + 
      unfold translate in *.
      simpl in *.
      rewrite prod_nil_nil_r.
      repeat split; auto.
      unfold translate.
  Qed.
*)
  Lemma m_in_branch_iter:
    forall A x n n1 n2 f,
    n1 <= n < n2 ->
    MIn x (f n) ->
    @MIn A x (branch_iter n1 n2 f).
  Proof.
    intros.
    unfold branch_iter.
    apply range_list_in in H.
    apply m_in_concat with (l:=f n); auto.
    apply in_map.
    auto.
  Qed.

  Lemma i_subst_inv_nil:
    forall x v i,
    C2.i_subst x v i = C2.Skip ->
    i = C2.Skip.
  Proof.
    intros.
    destruct i; simpl in *.
    - reflexivity.
    - destruct p.
      inversion H.
    - inversion H.
    - inversion H.
  Qed.

  Lemma completeness_1
      (i:C1.inst)
      (T1_nin_i: ~ C1.In T1 i)
      (T2_nin_i: ~ C1.In T2 i)
    :
    forall hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    C2.Run (translate i) hs2 ->
    Incl (MMember hs2) (MMember hs1).
  Proof.
    intros hs1 H.
    induction H; intros.
    - apply incl_mmember_nil_nil.
    - destruct (list_eq_nil hs) as [N|hs_not_nil]. {
        subst.
        simpl.
        apply incl_mmember_nil.
      }
      rewrite mmember_prepend_rw; auto.
      rewrite member_concat_rw.
      rewrite incl_l_either_iff.
      split. {
        apply c2_run_acc_inv_1 in H2; auto.
        destruct H2 as (f1, (?, Hf1)).
        subst.
        clear IHRun. (* We don't need IHRun *)
        (* Show that all members of v are in hss *)
        (* 1. simplify defs *)
        apply incl_def; intros.
        rewrite mmember_rw in *.
        Search (MIn _ (_ ++ _)).
        apply m_in_app_l.
        (* At this point we know that the access is in the output of 
             Hist.GenAccess TID e TID_COUNT v
           So, we need to find out which task has created it. *)
        apply Hist.m_in_gen_access_inv with (v0:=x) in H; auto.
        destruct H as (t, (vs, (Ht, (Ha, (Hi, Hj))))).
        (* Knowing that some task performed the access, we need to
           figure out whether it was T1 or T2.
           If t = 0, then t = T2, otherwise t = T1. *)
        assert (Hd: t = 0 \/ 1 <= t) by omega.
        destruct Hd. {
          (* t = T2 *)
          (* In this case, we can pick any other task, say T1 = 1 *)
          assert (Hx1: 1 <= 1 < TID_COUNT) by omega.
          assert (Hx2: 0 <= 0 < 1 ) by omega.
          assert (Hf1 := Hf1 1 0 Hx1 Hx2); subst.
          destruct Hf1 as (f2, (hs1, (hs2, (?, (?, (Hr1, Hr2)))))).
          inversion Hr2; subst; clear Hr2.
          assert (v0 = vs) by eauto using access_step_fun.
          subst.
          apply m_in_branch_iter with (n:=1); auto.
          rewrite H.
          apply m_in_app_l.
          apply m_in_branch_iter with (n:=0); auto.
          rewrite H3.
          destruct (list_eq_nil hs1). {
            subst.
            apply C2.run_inv_nil in Hr1.
            contradiction.
          }
          apply m_in_prod_r; auto.
          assert (hs0 <> []). {
            intros N; subst.
            apply C2.run_inv_nil in H8.
            contradiction.
          }
          apply m_in_prepend_l; auto.
        }
        (* t = T1 *)
        (* In this case, we can pick any other task for T1 = 0 *)
        give_up.
      }
      (* Show that all members of hs are in hss *)
      (* We have that the access is in hs, so we must use the IH *)
      apply incl_def; intros.
      rewrite mmember_rw in *.
      assert (R: (C1.Acc e i) = C1.seq (C1.Acc e C1.Skip) i) by auto.
      rewrite R in H2; clear R.
      apply translate_seq in H2; auto.
      + destruct H2 as (m, (Hm, Hr)).
        apply C2.run_inv_seq in Hr.
        destruct Hr as (ma, (mb, (?, (Hr1, Hr2)))).
        assert (Hx := Hr2).
        apply IHRun in Hx.
        * subst.
          rewrite Hm.
          assert (ma <> nil). {
            intros N; subst.
            apply C2.run_inv_nil in Hr1.
            assumption.
          }
          apply m_in_prod_r; auto.
          give_up.
        * give_up.
        * give_up.
        * give_up.
      + give_up.
      + give_up.
      + give_up.
      + give_up.
    - give_up.
    - give_up.
    - give_up.
  Admitted.

(*
  Variable tid_ge_2: TID_COUNT > 2.
  Variable in_heap: forall x i hs, C2.Run i hs -> MIn x hs -> access_tid x < TID_COUNT.
*)
  Theorem completeness:
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
    intros.
    eapply Hist.m_safe_to_m_safe_strong; eauto.
    apply completeness_1.
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

Section Compiler.

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