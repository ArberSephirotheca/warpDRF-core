Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.Sets.Ensembles.
Require Coq.omega.Omega.
Require Import Recdef.
Require Import Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Access.
Require Import Util.
Require LoopFree.
Require Import SetTh.
Import ListNotations.
Require Import Tasks.
Require Import SymHist.
Require Import RangeList.
Require Import SHCompiler.
Require Import MultiHist.
Require Conc.
Section Compiler.
  Section Defs.
  Context {A:Access}.
  Context {T:Tasks}.
 
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
    rewrite access_subst_subst_neq in Hx; auto using t2_neq_tid.
    rewrite access_subst_not_in with (x:=T2) in Hx; auto.
  Qed.

  Notation history := (list access_val).
  Definition mk_empty_1 n1 n2 : list history :=
    List.concat (map (fun _ => [[]]) (range_list n1 n2)) ++ [[]].

  Lemma run_skip_1:
    forall n1 n2,
    SymHist.Run (SymHist.Decl T2 (NNum n1, NNum n2) SymHist.Skip SymHist.Skip) (mk_empty_1 n1 n2).
  Proof.
    intros.
    apply SymHist.run_decl with (l:=range_list n1 n2).
    - apply SymHist.r_step_range_list.
    - apply SymHist.run_branch_map_def with (f:=fun x => [[]]) (hs:=[[]]).
      + rewrite prod_nil_nil_r.
        reflexivity.
      + intros.
        simpl.
        apply SymHist.run_skip.
      + apply SymHist.run_skip.
  Qed.

  Definition mk_empty_2 n1 n2 : list history :=
    List.concat (map (fun n => mk_empty_1 0 n) (range_list n1 n2))
     ++ [[]].
   

  Lemma run_skip:
    SymHist.Run (translate Conc.Skip) (mk_empty_2 1 TID_COUNT).
  Proof.
    unfold translate.
    simpl.
    apply SymHist.run_decl with (l:=range_list 1 TID_COUNT).
    - apply SymHist.r_step_range_list.
    - apply SymHist.run_branch_map_def with (f:=fun n => mk_empty_1 0 n) (hs:=[[]]).
      + rewrite prod_nil_nil_r.
        reflexivity.
      + intros.
        simpl.
        remove_eq T1 T1.
        remove_eq T1 T2.
        apply run_skip_1.
      + apply SymHist.run_skip.
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
    assert (Hi : ~ List.In a l). {
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
    SymHist.Run (SymHist.Branch x l i1 i2) hs' ->
    NoDup l ->
    exists f hs,
    hs' = ((List.concat (List.map f l)) ++ hs) /\ SymHist.Run i2 hs
    /\
    (forall n, List.In n l -> SymHist.Run (SymHist.seq (SymHist.i_subst x (NNum n) i1) i2) (f n)).
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
    SymHist.Run (SymHist.Decl x (NNum n1, NNum n2) i1 i2) hs' ->
    exists f hs,
    hs' = branch_iter n1 n2 f ++ hs /\
    SymHist.Run i2 hs /\
    (forall n, n1 <= n < n2 -> SymHist.Run (SymHist.seq (SymHist.i_subst x (NNum n) i1) i2) (f n)).
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
    ~ SymHist.In T1 e ->
    SymHist.i_subst T1 v (SymHist.i_subst TID (NVar T1) e) =
    SymHist.i_subst TID v e.
  Proof.
    intros.
    rewrite SymHist.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_tid_eq:
    forall v e,
    ~ SymHist.In T2 e ->
    SymHist.i_subst T2 v (SymHist.i_subst TID (NVar T2) e) =
    SymHist.i_subst TID v e.
  Proof.
    intros.
    rewrite SymHist.i_subst_subst_trans; auto.
  Qed.

  Lemma subst_t2_neq:
    forall e n1 n2,
    ~ SymHist.In T2 e ->
    SymHist.i_subst T2 (NNum n2) (SymHist.i_subst TID (NNum n1) e)
    =
    SymHist.i_subst TID (NNum n1) e.
  Proof.
    intros.
    rewrite SymHist.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply SymHist.in_i_subst_neq in N; auto using t2_neq_tid.
    intros M.
    inversion M.
  Qed.

  Lemma subst_t1_t2_neq:
    forall v e,
    ~ SymHist.In T1 e ->
    SymHist.i_subst T1 v (SymHist.i_subst TID (NVar T2) e)
    = 
    SymHist.i_subst TID (NVar T2) e.
  Proof.
    intros.
    rewrite SymHist.i_subst_not_in; auto.
    intros N.
    contradict H.
    apply SymHist.in_subst_inv_in in N; auto using t1_neq_t2, t1_neq_tid.
  Qed.


  Lemma rw_1 e (t1_nin: ~ SymHist.In T1 (proj e)):
    forall n1,
        SymHist.i_subst T1 (NNum n1)
           (SymHist.Decl T2 (NNum 0, NVar T1)
              (SymHist.seq (do_proj T1 e)
                 (do_proj T2 e)) SymHist.Skip)
   =
       SymHist.Decl T2 (NNum 0, NNum n1)
        (SymHist.seq (SymHist.i_subst TID (NNum n1) (proj e))
                (do_proj T2 e)) SymHist.Skip.
  Proof.
    intros.
    simpl.
    remove_eq T1 T2.
    remove_eq T1 T1.
    rewrite SymHist.i_subst_seq.
    unfold do_proj in *.
    rewrite subst_t1_tid_eq; auto.
    rewrite subst_t1_t2_neq; auto.
  Qed.

  Lemma nin_t1_tid:
    ~ NIn T1 (NVar TID).
  Proof.
    intros N.
    inversion N.
    tasks_absurd.
  Qed.

  Lemma rw_2:
    forall e n1 n2,
    ~ Conc.In T2 e ->
    SymHist.i_subst T2 (NNum n2)
       (SymHist.seq
          (SymHist.i_subst TID (NNum n1) (proj e))
          (do_proj T2 e))
    = 
    SymHist.seq
      (SymHist.i_subst TID (NNum n1) (proj e))
      (SymHist.i_subst TID (NNum n2) (proj e)).
  Proof.
    intros.
    rewrite SymHist.i_subst_seq.
    assert (~ SymHist.In T2 (proj e)). {
      intros N.
      eapply in_proj_to_in in N; eauto using t2_neq_tid.
    }
    rewrite subst_t2_neq; auto.
    unfold do_proj.
    rewrite subst_t2_tid_eq; auto.
  Qed.

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

  Import C2Notations.

  Lemma run_trans_inv e  (t1_nin: ~ Conc.In T1 e) (t2_nin: ~ Conc.In T2 e) hs:
    SymHist.Run (translate e) hs ->
    exists f1,
    hs = List.concat (SymHist.branch_iter 1 TID_COUNT f1) ++ [[]]
    /\
    forall n1,
    1 <= n1 < TID_COUNT ->
    exists f2,
    f1 n1 = List.concat (SymHist.branch_iter 0 n1 f2) ++ [[]] /\
    forall n2,
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      SymHist.Run (SymHist.i_subst TID (NNum n1) (proj e)) hs1 /\
      SymHist.Run (SymHist.i_subst TID (NNum n2) (proj e)) hs2

  .
  Proof.
    intros.
    unfold translate in *.
    apply SymHist.run_decl_inv_map in H.
    destruct H as (ms, (m, (?, (Hs, H)))).
    inversion Hs; subst; clear Hs.
    rewrite prod_nil_nil_r.
    apply SymHist.decl_map_inv in H.
    destruct H as (f1, (R1, Hf)).
    exists f1.
    rewrite R1.
    split; auto.
    intros n1 Ha.
    apply Hf in Ha; clear Hf.
    assert (X:~ SymHist.In T1 (proj e)). {
      intros N.
      contradict t1_nin.
      auto using in_proj_to_in, t1_neq_tid.
    }
    rewrite rw_1 in Ha; auto.
    apply SymHist.run_decl_inv_map in Ha.
    destruct Ha as (ms2, (hs, (R2,(Ha,Hc)))).
    apply SymHist.decl_map_inv in Hc.
    destruct Hc as (f2, (R3, Hc)). 
    inversion Ha; subst; clear Ha.
    exists f2.
    rewrite R2.
    assert (forall n2, 
      0 <= n2 < n1 ->
      exists hs1 hs2,
      f2 n2 = prod hs1 hs2 /\
      SymHist.Run (SymHist.i_subst TID (NNum n1) (proj e)) hs1 /\
      SymHist.Run (SymHist.i_subst TID (NNum n2) (proj e)) hs2
    ). {
      intros n2 Hb.
      apply Hc in Hb; clear Hc.
      rewrite rw_2 in Hb; auto.
      apply SymHist.run_inv_seq in Hb.
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

  Lemma mk_empty_1_rw:
    forall n1 n2,
    mk_empty_1 n1 n2 == [].
  Proof.
    intros.
    unfold mk_empty_1.
    rewrite concat_eq_rw.
    rewrite mem_equiv_nil_rw.
    rewrite mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Lemma mk_empty_2_rw:
    forall n1 n2,
    mk_empty_2 n1 n2 == [].
  Proof.
    unfold mk_empty_2.
    intros.
    rewrite mem_equiv_cons_nil_rw.
    rewrite app_nil_r.
    remember (map _ _).
    destruct (list_eq_nil l) as [R|Hne]. {
      rewrite R.
      reflexivity.
    }
    apply mem_equiv_concat_refl_rw; auto.
    intros.
    subst.
    apply in_map_iff in H.
    destruct H as (n, (?, Hi)).
    subst.
    rewrite mk_empty_1_rw.
    reflexivity.
  Qed.

  Lemma t1_not_in_proj_skip:
    ~ SymHist.In T1 (proj Conc.Skip).
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

  Lemma mem_equiv_cons_eq_nil:
    forall h,
    [h] == [] ->
    h = [].
  Proof.
    intros.
    (*unfold SymHist.MemEquiv in H.*)
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
    rewrite mem_equiv_app_refl_rw.
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

  Lemma c2_run_acc_inv_1 e hs i (t1_nin: ~ Conc.In T1 (Conc.Acc e i)) (t2_nin: ~ Conc.In T2 (Conc.Acc e i)):
    SymHist.Run (translate (Conc.Acc e i)) hs ->
    exists f1,
    hs = branch_iter 1 TID_COUNT f1 ++ [[]]
    /\
    forall n1 n2,
    1 <= n1 < TID_COUNT ->
    0 <= n2 < n1 ->
    exists f2 hs1 hs2,
    f1 n1 = branch_iter 0 n1 f2 ++ [[]] /\
    f2 n2 = prod hs1 hs2/\
    SymHist.Run
        (SymHist.Acc (access_subst TID (NNum n1) e, NNum n1)
           (SymHist.i_subst TID (NNum n1) (proj i))) hs1 /\
    SymHist.Run
        (SymHist.Acc (access_subst TID (NNum n2) e, NNum n2)
           (SymHist.i_subst TID (NNum n2) (proj i))) hs2
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

  Lemma translate_seq e1 (t1_nin1: ~ Conc.In T1 e1) (t2_nin1: ~ Conc.In T2 e1):
    forall e2,
    ~ Conc.In T1 e2 ->
    ~ Conc.In T2 e2 ->
    forall m1,
    SymHist.Run (translate (Conc.seq e1 e2)) m1 ->
    exists m2,
    m1 == m2 /\ SymHist.Run (SymHist.seq (translate e1) (translate e2)) m2.
  Proof.
    induction e1; intros e2 t1_nin2 t2_nin2 m1 Hr.
    - simpl in Hr.
      assert (Hx := Hr).
      exists (prod (mk_empty_2 1 TID_COUNT) m1).
      split. {
        apply prod_mk_empty_2_rw.
      }
      apply SymHist.run_seq; auto using run_skip.
    - simpl in Hr.
      apply c2_run_acc_inv_1 in Hr.
      + destruct Hr as (f1, (?, Hf)).
        subst.
  Admitted.

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
    SymHist.i_subst x v i = SymHist.Skip ->
    i = SymHist.Skip.
  Proof.
    intros.
    destruct i; simpl in *.
    - reflexivity.
    - destruct p.
      inversion H.
    - inversion H.
    - inversion H.
  Qed.

  Notation "'<[' x ']>'" := (translate x).
  Coercion NNum: nat >-> nexp.  
  Infix "⇓" := LoopFree.Run (at level 80).
  Notation "⊢" := Hist.Safe.
  Notation "⊨" := Hist.MSafe.
  (*
  Infix "*⊆" := AllIncl (at level 80).
  Infix "⊆*" := InclAll (at level 80).
  Infix "*⊆*" := AllInclAll (at level 70).
  *)
  Infix "×" := prod (at level 50).
  Infix "⤋" := SymHist.Run (at level 80).
  Notation "x *⊆* y" := (Incl (MMember x) (MMember y)) (at level 80).
  Notation "i '[' x ':=' n ']'" := (Conc.i_subst x n i) (at level 40).

  Lemma completeness_1
      (i:Conc.inst)
      (T1_nin_i: ~ Conc.In T1 i)
      (T2_nin_i: ~ Conc.In T2 i)
    :
    forall hs1,
    LoopFree.Run i hs1 ->
    forall hs2,
    (forall x, MIn x hs1 -> access_tid x < TID_COUNT) ->
    SymHist.Run (translate i) hs2 ->
    Incl (MMember hs2) (MMember hs1).
  Proof.
    intros hs1 H.
    induction H; intros.
    - Search (Conc.Skip). 
      assert (hs2 = mk_empty_2 1 TID_COUNT). {
        assert (Hx := run_skip).
        eauto using SymHist.run_fun.
      }
      subst.
      (*
      rewrite mk_empty_2_rw.
      *)
      admit.
      (*apply incl_mmember_nil_nil.*)
    - apply c2_run_acc_inv_1 in H2; auto.
      destruct H2 as (f1, (Heq, Hf)).
      subst.
      destruct (list_eq_nil hs) as [N|hs_not_nil]. {
        subst.
        simpl.
        apply incl_mmember_nil.
        admit.
      }
      rewrite mmember_prepend_rw; auto.
      rewrite member_concat_rw.
      (*
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
          assert (Hx1: 1 <= 1 < TID_COUNT) by auto using tid_count_1_lt with *.
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
            apply SymHist.run_inv_nil in Hr1.
            contradiction.
          }
          apply m_in_prod_r; auto.
          assert (hs0 <> []). {
            intros N; subst.
            apply SymHist.run_inv_nil in H8.
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
      assert (R: (Conc.Acc e i) = Conc.seq (Conc.Acc e Conc.Skip) i) by auto.
      rewrite R in H2; clear R.
      apply translate_seq in H2; auto.
      + destruct H2 as (m, (Hm, Hr)).
        apply SymHist.run_inv_seq in Hr.
        destruct Hr as (ma, (mb, (?, (Hr1, Hr2)))).
        assert (Hx := Hr2).
        apply IHRun in Hx.
        * subst.
          rewrite Hm.
          assert (ma <> nil). {
            intros N; subst.
            apply SymHist.run_inv_nil in Hr1.
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
    *)
  Admitted.

(*
  Variable tid_ge_2: TID_COUNT > 2.
  Variable in_heap: forall x i hs, SymHist.Run i hs -> MIn x hs -> access_tid x < TID_COUNT.
*)
(*
  Theorem completeness:
    forall i hs1,
    C1SX.Run TID_COUNT TID i hs1 ->
    forall hs2,
    SymHist.Run (translate i) hs2 ->
    Hist.MSafe hs1 ->
    ~ Conc.In T1 i ->
    ~ Conc.In T2 i ->
    ~ Conc.Var TID i -> 
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
      apply SymHist.run_inv_seq in Ha.
      destruct Ha as (Ha_hs1, (Ha_hs2, (?, (Ha,Hb)))).
      subst.
      eapply run_proj_proj in Ha; eauto with *.
      subst.
      inversion Hb; subst; clear Hb.
      
    (*
    var tid, [tid] -> var tid, ([tid], tid) 
     *)

  Qed.
*)
  End Defs.

End Compiler.
