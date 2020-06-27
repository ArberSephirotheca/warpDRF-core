Require Import Coq.Lists.List.

Require Import Var.
Require Import Util.
Require Import RangeList.
Require Import Access.
Require Import Exp.
Require Import MExp.
Require Import MultiHist.
Require Import SymHist.

Import ListNotations.
Import MHistNotations.

Section Defs.
  Context {A:Access}.
  Notation history := (list access_val).

  Inductive ERun: inst -> mexp -> Prop :=
  | e_run_skip:
    ERun Skip (One [])
  | e_run_access:
    forall i e v hs,
    access_step e v ->
    ERun i hs ->
    ERun (Acc e i) (Prod (One v) hs)
  | e_run_decl:
    forall r l i1 i2 x hs,
    RStep r l ->
    ERun (Branch x l i1 i2) hs ->
    ERun (Decl x r i1 i2) hs
  | e_run_branch_cons:
    forall x n l i1 i2 hs1 hs2,
    ERun (seq (i_subst x (NNum n) i1) i2) hs1 ->
    ERun (Branch x l i1 i2) hs2 ->
    ERun (Branch x (n::l) i1 i2) (Plus hs1 hs2)
  | e_run_branch_nil:
    forall x i1 i2 hs,
    ERun i2 hs ->
    ERun (Branch x [] i1 i2) hs.

  Definition FRun i m :=
    exists m', EEq m m' /\ ERun i m'.

  Infix "//" := FRun (at level 50).
  Infix ";;" := seq (at level 30).

  Lemma f_run_def:
    forall i m m',
    EEq m m' ->
    ERun i m' ->
    FRun i m.
  Proof.
    unfold FRun.
    eauto.
  Qed.

  Lemma f_run_eq:
    forall i m,
    ERun i m ->
    FRun i m.
  Proof.
    intros.
    assert (m == m) by reflexivity.
    unfold FRun; eauto.
  Qed.

  Lemma e_run_1:
    forall i e,
    ERun i e ->
    Run i (to_mem e).
  Proof.
    intros i e H.
    induction H; simpl.
    - auto using run_skip.
    - rewrite app_nil_r.
      auto using run_access.
    - eauto using run_decl.
    - eauto using run_branch_cons.
    - eauto using run_branch_nil.
  Qed.


  Lemma e_run_2:
    forall i h,
    Run i h ->
    exists e, ERun i e /\ MemEquiv h (to_mem e).
  Proof.
    intros i h H.
    induction H.
    - exists (One []).
      split.
      + apply e_run_skip.
      + simpl.
        reflexivity.
    - destruct IHRun as (e1, (Hr, R)).
      exists (Prod (One v) e1).
      split; auto using e_run_access.
      simpl.
      rewrite app_nil_r.
      repeat rewrite prepend_rw.
      apply mem_equiv_prod_r; eauto using run_not_nil, to_mem_not_nil.
      intros N.
      inversion N.
    - destruct IHRun as (e1, (Hr, R)).
      eauto using e_run_decl.
    - destruct IHRun1 as (e1, (Hr1, R1)).
      destruct IHRun2 as (e2, (Hr2, R2)).
      eexists.
      split.
      + apply e_run_branch_cons; eauto.
      + rewrite R1.
        rewrite R2.
        reflexivity.
    - destruct IHRun as (e1, (Hr1, R1)).
      eauto using e_run_branch_nil.
  Qed.

  Lemma e_run_inv_seq:
    forall i1 i2 m,
    ERun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ ERun i1 m1 /\ ERun i2 m2.
  Proof.
    intros.
    apply e_run_1 in H.
    apply run_inv_seq in H.
    destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
    assert (m1 <> []) by eauto using run_not_nil.
    assert (m2 <> []) by eauto using run_not_nil.
    apply e_run_2 in Hr1.
    apply e_run_2 in Hr2.
    destruct Hr1 as (m3, (Hr3, R3)).
    destruct Hr2 as (m4, (Hr4, R4)).
    exists m3.
    exists m4.
    split; auto.
    apply e_eq_iff_m_equiv.
    rewrite R1.
    simpl.
    apply mem_equiv_prod; auto using to_mem_not_nil.
  Qed.

  Lemma f_run_inv_seq:
    forall i1 i2 m,
    FRun (seq i1 i2) m ->
    exists m1 m2, m == m1 * m2 /\ FRun i1 m1 /\ FRun i2 m2.
  Proof.
    intros.
    destruct H as (m', (R1, Hr1)).
    apply e_run_inv_seq in Hr1.
    destruct Hr1 as (m1, (m2, (R2, (Hr1, Hr2)))).
    apply f_run_eq in Hr1.
    apply f_run_eq in Hr2.
    rewrite <- R1 in R2.
    eauto.
  Qed.

  Lemma f_run_1:
    forall i e,
    FRun i e ->
    exists e', e == e' /\ Run i (to_mem e').
  Proof.
    intros.
    destruct H as (m, (R, Hr)).
    apply e_run_1 in Hr.
    eauto.
  Qed.

  Lemma f_run_2: forall (i : inst) (h : list history),
    Run i h ->
    exists e, MemEquiv h (to_mem e) /\ FRun i e.
  Proof.
    intros.
    apply e_run_2 in H.
    destruct H as (e, (Hr, Hm)).
    eauto using f_run_eq.
  Qed.

  Lemma e_run_seq:
    forall i1 m1,
    ERun i1 m1 ->
    forall i2 m2,
    ERun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    apply e_run_1 in H.
    apply e_run_1 in H0.
    assert (Hr: Run (seq i1 i2) (prod (to_mem m1) (to_mem m2))) by eauto using run_seq.
    apply e_run_2 in Hr.
    destruct Hr as (e, (Hr1, Hm2)).
    apply f_run_def with (m':=e); auto.
    apply e_eq_iff_m_equiv.
    simpl.
    assumption.
  Qed.

  Import Morphisms.

  Global Instance f_run_proper_1: Proper (eq ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite H0 in R1.
      eauto using f_run_def.
    - destruct H1 as (m1, (R1, Hr1)).
      rewrite <- H0 in R1.
      eauto using f_run_def.
  Qed.

  Lemma f_run_seq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2 m3,
    FRun i2 m2 ->
    m3 == (Prod m1 m2) ->
    FRun (seq i1 i2) m3.
  Proof.
    intros.
    rewrite H1.
    destruct H as (m1', (R1, Hr1)).
    destruct H0 as (m2', (R2, Hr2)).
    rewrite R1.
    rewrite R2.
    eauto using e_run_seq.
  Qed.

  Lemma f_run_seq_eq:
    forall i1 m1,
    FRun i1 m1 ->
    forall i2 m2,
    FRun i2 m2 ->
    FRun (seq i1 i2) (Prod m1 m2).
  Proof.
    intros.
    eapply f_run_seq; eauto.
    reflexivity.
  Qed.

  Lemma e_run_fun:
    forall i e1,
    ERun i e1 ->
    forall e2,
    ERun i e2 ->
    e1 = e2.
  Proof.
    intros i e1 H.
    induction H; intros.
    - inversion H; subst; auto.
    - inversion H1; subst; clear H1.
      assert (v0 = v) by eauto using access_step_fun.
      subst.
      apply IHERun in H6.
      subst.
      reflexivity.
    - inversion H1; subst; clear H1.
      assert (l0 = l) by eauto using r_step_fun.
      subst.
      eauto.
    - inversion H1; subst; clear H1.
      apply IHERun1 in H8.
      apply IHERun2 in H9.
      subst.
      reflexivity.
    - inversion H0; subst; clear H0.
      eauto.
  Qed.

  Lemma f_run_fun:
    forall i e1,
    FRun i e1 ->
    forall e2,
    FRun i e2 ->
    e1 == e2.
  Proof.
    intros.
    destruct H as (m1, (R1, Hr1)).
    destruct H0 as (m2, (R2, Hr2)).
    transitivity m1; auto.
    assert (m2 = m1) by eauto using e_run_fun.
    subst.
    symmetry.
    assumption.
  Qed.

  Lemma f_run_branch_cons:
    forall x n l i1 i2 m1 m2 m3,
    FRun (seq (i_subst x (NNum n) i1) i2) m1 ->
    FRun (Branch x l i1 i2) m2 ->
    EEq m3 (m1 + m2) ->
    FRun (Branch x (n :: l) i1 i2) m3.
  Proof.
    intros.
    destruct H as (m1', (R1, Hr1)).
    destruct H0 as (m2', (R2, Hr2)).
    rewrite H1.
    rewrite R1.
    rewrite R2.
    eauto using f_run_eq, e_run_branch_cons. 
  Qed.

  Lemma f_run_branch_cons_eq:
    forall x n l i1 i2 m1 m2,
    FRun (seq (i_subst x (NNum n) i1) i2) m1 ->
    FRun (Branch x l i1 i2) m2 ->
    FRun (Branch x (n :: l) i1 i2) (m1 + m2).
  Proof.
    intros.
    apply f_run_branch_cons with (m1:=m1) (m2:=m2); auto.
    reflexivity.
  Qed.

  Lemma f_run_branch_nil:
    forall x i1 i2 m,
    FRun i2 m ->
    FRun (Branch x [] i1 i2) m.
  Proof.
    intros.
    destruct H as (m', (R1, Hr1)).
    rewrite R1.
    eauto using e_run_branch_nil, f_run_eq.
  Qed.

  Lemma f_run_decl:
    forall r l i1 i2 x m,
    RStep r l ->
    FRun (Branch x l i1 i2) m ->
    FRun (Decl x r i1 i2) m.
  Proof.
    intros.
    destruct H0 as (m', (Hr, R)).
    rewrite Hr.
    eauto using e_run_decl, f_run_eq.
  Qed.

  Lemma e_run_branch_seq_skip:
    forall x i1 m1 r,
    ERun (Branch x r i1 Skip) m1 ->
    forall i2 m2,
    ERun i2 m2 ->
    FRun (Branch x r i1 i2) (Prod m1 m2).
  Proof.
    intros x i1 m1 r H.
    remember (Branch _ _ _ _).
    generalize dependent Heqi.
    generalize dependent x.
    generalize dependent r.
    generalize dependent i1.
    induction H; intros; inversion Heqi; subst; clear Heqi.
    - rewrite seq_nil_rw in H.
      rewrite <- e_prod_plus_l.
      apply f_run_branch_cons_eq; eauto.
      apply f_run_seq_eq; auto using f_run_eq.
    - inversion H; subst; clear H.
      rewrite e_prod_nil_l.
      eauto using f_run_branch_nil, f_run_eq.
  Qed.

  Lemma e_run_decl_seq_skip:
    forall x r i1 i2 m1 m2,
    ERun (Decl x r i1 Skip) m1 ->
    ERun i2 m2 ->
    FRun (Decl x r i1 i2) (Prod m1 m2).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using e_run_branch_seq_skip, f_run_decl.
  Qed.
(*
  Inductive BranchMap x i: list nat -> list mexp -> Prop :=
  | branch_map_nil:
    BranchMap x i [] []
  | branch_map_cons:
    forall n l hss hs,
    ERun (i_subst x (NNum n) i) hs ->
    BranchMap x i l hss ->
    BranchMap x i (n::l) (hs::hss).
*)
  Notation Iter x i := (fun n=> FRun (i_subst x (NNum n) i)).  
  Notation BranchMap x i l m := (Map (Iter x i) l m).
  Definition DeclMap x i n1 n2 m := BranchMap x i (range_list n1 n2) m.
  (*Hint Unfold DeclMap core.*)

  Transparent DeclMap.
(*
  Lemma branch_map_to_map:
    forall x i l m,
    BranchMap x i l m ->
    NoDup l ->
    Map (Iter x i) l m.
  Proof.
    intros x i l m Hb.
    induction Hb; intros. {
      apply map_nil.
    }
    inversion H0; subst; clear H0.
    apply map_cons; auto.
  Qed.

  Lemma map_to_branch_map:
    forall x i l m,
    Map (Iter x i) l m ->
    BranchMap x i l m.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      apply branch_map_nil.
    }
    inversion H; subst; clear H.
    eauto using branch_map_cons.
  Qed.

  Lemma branch_map_in:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n,
    List.In n l ->
    exists h, List.In (n, h) (List.combine l hss).
  Proof.
    induction l; intros. {
      contradiction.
    }
    destruct H0 as [Ha|Hi]; inversion H; subst; clear H. {
      simpl.
      eauto.
    }
    eapply IHl in H4; eauto.
    destruct H4 as (h, Hj).
    eauto using in_cons.
  Qed.

  Lemma branch_map_pair_in_to_run:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n h,
    List.In (n, h) (List.combine l hss) ->
    Run (i_subst x (NNum n) i) h.
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H; subst; clear H.
    destruct H0 as [Hx|Hx]. {
      inversion Hx; subst; clear Hx.
      assumption.
    }
    eauto.
  Qed.

  Lemma branch_map_to_run:
    forall x i l hss,
    BranchMap x i l hss ->
    forall n,
    List.In n l ->
    exists hs, Run (i_subst x (NNum n) i) hs.
  Proof.
    intros.
    eapply branch_map_in in H0; eauto.
    destruct H0 as (h, Hi).
    eauto using branch_map_pair_in_to_run.
  Qed.
*)
(*
  Lemma branch_map_def:
    forall x i l f,
    (forall n, List.In n l -> ERun (i_subst x (NNum n) i) (f n)) ->
    BranchMap x i l (map f l).
  Proof.
    induction l; intros.
    - apply map_nil.
    - simpl.
      apply map_cons.
      + auto using in_eq.
      + intros.
      + apply IHl; auto using in_cons.
  Qed.
*)
  Definition ProgImpl i j : Prop :=
    forall m,
    FRun i m ->
    FRun j m.

  Lemma prog_impl_def:
    forall i j,
    (forall m, FRun i m -> FRun j m) ->
    ProgImpl i j.
  Proof.
    intros.
    unfold ProgImpl.
    apply H.
  Qed.

  Lemma prog_impl_refl:
    forall i,
    ProgImpl i i.
  Proof.
    unfold ProgImpl.
    auto.
  Qed.

  Lemma prog_impl_trans:
    forall i j k,
    ProgImpl i j ->
    ProgImpl j k ->
    ProgImpl i k.
  Proof.
    unfold ProgImpl.
    intros.
    eauto.
  Qed.

  (** Register [ProgImpl] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgImpl
    reflexivity proved by prog_impl_refl
    transitivity proved by prog_impl_trans
    as prog_impl_setoid.

  Definition ProgEquiv i j : Prop :=
    forall m, FRun i m <-> FRun j m.

  Infix "~>" := ProgImpl (at level 40).
  Infix "~~" := ProgEquiv (at level 40).

  Lemma prog_equiv_def:
    forall i j,
    ProgImpl i j ->
    ProgImpl j i ->
    ProgEquiv i j.
  Proof.
    split; auto.
  Qed.

  Lemma prog_equiv_inv_l:
    forall i m j,
    FRun i m ->
    ProgEquiv i j ->
    FRun j m.
  Proof.
    intros.
    apply H0 in H.
    assumption.
  Qed.

  Lemma prog_equiv_inv_r:
    forall i m j,
    FRun j m ->
    ProgEquiv i j ->
    FRun i m.
  Proof.
    intros.
    apply H0 in H.
    auto.
  Qed.

  Lemma prog_equiv_refl:
    forall i,
    ProgEquiv i i.
  Proof.
    intros.
    unfold ProgEquiv.
    intuition.
  Qed.

  Lemma prog_equiv_sym:
    forall i j,
    ProgEquiv i j ->
    ProgEquiv j i.
  Proof.
    unfold ProgEquiv.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma prog_equiv_trans:
    forall i j k,
    ProgEquiv i j ->
    ProgEquiv j k ->
    ProgEquiv i k.
  Proof.
    unfold ProgEquiv.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  (** Register [Equiv] in Coq's tactics. *)
  Global Add Parametric Relation : _ ProgEquiv
    reflexivity proved by prog_equiv_refl
    symmetry proved by prog_equiv_sym
    transitivity proved by prog_equiv_trans
    as prog_equiv_setoid.

  Global Instance f_run_proper_2: Proper (ProgEquiv ==> EEq ==> iff) FRun.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros; subst.
    - rewrite H0 in H1.
      apply H in H1.
      assumption.
    - rewrite <- H0 in H1.
      apply H in H1.
      assumption.
  Qed.


  Lemma branch_map_rw:
    forall l i j x hss,
    (forall n, List.In n l ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    BranchMap x i l hss ->
    BranchMap x j l hss.
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0.
      auto using map_nil.
    }
    inversion H0; subst; clear H0.
    assert (hi: List.In a (a :: l)) by eauto using in_eq.
    assert (Hx := H _ hi); clear hi.
    assert (Hy: forall n : nat,
       List.In n l -> ProgEquiv (i_subst x (NNum n) i) (i_subst x (NNum n) j)) by auto using in_cons.
    assert (IHl := IHl i j x vs Hy H6).
    apply map_cons; auto.
    eapply prog_equiv_inv_l in H3; eauto.
  Qed.

(*
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
    intros B n f.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    assert (n <> a). {
      intros N.
      subst.
      contradict H.
      auto using in_eq.
    }
    rewrite add_neq_rw; auto.
    assert (Hi : ~ List.In n l). {
      intros N.
      contradict H.
      auto using in_cons.
    }
    assert (IHl := IHl x Hi).
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma branch_map_inv:
    forall x i l hss,
    BranchMap x i l hss ->
    NoDup l ->
    exists f, hss = map f l /\
    (forall n, List.In n l -> Run (i_subst x (NNum n) i) (f n)).
  Proof.
    intros.
    induction H.
    + exists (fun n => []).
      split; auto.
      intros.
      contradiction.
    + inversion H0; subst; clear H0.
      destruct IHBranchMap as (f, (?, Hf)); auto.
      exists (add f n hs).
      subst.
      simpl.
      split. {
        subst.
        rewrite add_eq_rw.
        rewrite map_add_rw_not_in; auto.
      }
      intros.
      destruct H0. {
        subst.
        rewrite add_eq_rw.
        assumption.
      }
      assert (Hf := Hf _ H0).
      rewrite add_neq_rw; auto.
      intros N.
      subst.
      contradiction.
  Qed.
*)
  Lemma f_run_branch_map:
    forall l i1 i2 x m ml,
    BranchMap x i1 l ml ->
    FRun i2 m ->
    FRun (Branch x l i1 i2) (Prod (summation ml) m).
  Proof.
    induction l; intros; subst; inversion H; subst; clear H.
    - simpl.
      rewrite e_prod_nil_l.
      auto using f_run_branch_nil.
    - apply IHl with (i2:=i2) (m:=m) in H6; auto; clear IHl.
      apply f_run_seq_eq with (i1:=(i_subst x (NNum a) i1)) (m1:=v) in H0; auto.
      simpl.
      rewrite <- e_prod_plus_l.
      apply f_run_branch_cons_eq; auto.
  Qed.
(*
  Lemma run_branch_map_def:
    forall f l i1 i2 x hs hs',
    hs' = prod (List.concat (List.map f l)) hs ++ hs  ->
    (forall n, List.In n l -> Run (i_subst x (NNum n) i1) (f n)) ->
    Run i2 hs ->
    Run (Branch x l i1 i2) hs'.
  Proof.
    intros.
    eapply run_branch_map; eauto using branch_map_def.
  Qed.
*)
(*
  Definition DeclMap x i n1 n2 hss := BranchMap x i (range_list n1 n2) hss.
*)
(*
  Lemma decl_map_to_map:
    forall x i n1 n2 hss,
    DeclMap x i n1 n2 hss ->
    Map (Iter x i) (range_list n1 n2) hss.
  Proof.
    unfold DeclMap.
    intros.
    apply branch_map_to_map in H; auto using range_list_no_dup.
  Qed.

  Lemma decl_map_from_map:
    forall x i n1 n2 hss, 
    Map (Iter x i) (range_list n1 n2) hss ->
    DeclMap x i n1 n2 hss.
  Proof.
    intros.
    unfold DeclMap.
    auto using map_to_branch_map.
  Qed.

  Lemma decl_map_iff_map:
    forall x i n1 n2 hss,
    DeclMap x i n1 n2 hss <-> Map (Iter x i) (range_list n1 n2) hss.
  Proof.
    split; auto using decl_map_from_map, decl_map_to_map.
  Qed.
*)
(*
  Lemma decl_map_iter_def:
    forall x i n1 n2,
    (forall n, n1 <= n < n2 -> exists hs, Run (i_subst x (NNum n) i) hs) ->
    exists hss, DeclMap x i n1 n2 hss.
  Proof.
    intros.
    assert (Hm: exists hss, Map (Iter x i) (range_list n1 n2) hss). {
      apply map_def; auto using range_list_no_dup.
      intros.
      unfold Iter.
      auto using range_list_inv_in_2.
    }
    destruct Hm as (m, Hm).
    eauto using decl_map_from_map.
  Qed.
*)
  Lemma f_run_decl_map:
     forall n1 n2 i1 i2 x lm m,
     DeclMap x i1 n1 n2 lm ->
     FRun i2 m ->
     FRun (Decl x (NNum n1, NNum n2) i1 i2) (Prod (summation lm) m).
  Proof.
    eauto using f_run_branch_map, f_run_decl, r_step_range_list.
  Qed.
(*
  Lemma decl_map_def:
    forall x i n1 n2 f,
    (forall n, n1 <= n < n2 -> Run (i_subst x (NNum n) i) (f n)) ->
    DeclMap x i n1 n2 (map f (range_list n1 n2)).
  Proof.
    intros.
    unfold DeclMap.
    auto using branch_map_def, range_list_inv_in_2.
  Qed.
*)
  Lemma decl_map_rw:
    forall n1 n2 i j x l,
    (forall n, n1 <= n < n2 ->
      ProgEquiv (i_subst x (NNum n) i)
                (i_subst x (NNum n) j)) ->
    DeclMap x i n1 n2 l ->
    DeclMap x j n1 n2 l.
  Proof.
    intros.
    apply branch_map_rw with (j:=j) in H0; auto.
    intros.
    apply range_list_inv_in_2 in H1.
    auto.
  Qed.
(*
  Lemma e_run_decl_map_def:
     forall f n1 n2 i1 i2 x hs hs',
     (forall n,
       n1 <= n < n2 ->
       ERun (i_subst x (NNum n) i1) (f n)) ->
     ERun i2 hs ->
     exists m,
     EEq m (Plus (Prod (List.concat (map f (range_list n1 n2))) hs) hs)
     ERun (Decl x (NNum n1, NNum n2) i1 i2) hs'.
  Proof.
    intros.
    eapply run_decl_map; eauto using decl_map_def.
  Qed.
*)
  Lemma f_run_inv_branch_nil:
    forall x i1 i2 m,
    FRun (Branch x [] i1 i2) m ->
    FRun i2 m.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    rewrite R.
    eauto using f_run_eq.
  Qed.

  Lemma f_run_inv_branch_cons:
    forall x n l i1 i2 m,
    FRun (Branch x (n :: l) i1 i2) m ->
    exists m1 m2,
    m == (m1 + m2) /\
    FRun (seq (i_subst x (NNum n) i1) i2) m1 /\
    FRun (Branch x l i1 i2) m2.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists hs1.
    exists hs2.
    split; auto.
    split; auto using f_run_eq.
  Qed.

  Lemma f_run_branch_inv_map:
    forall l i1 i2 x m,
    FRun (Branch x l i1 i2) m ->
    NoDup l ->
    exists lm m',
    EEq m (Prod (summation lm) m')  /\
    FRun i2 m' /\ BranchMap x i1 l lm.
  Proof.
    induction l; intros. {
      apply f_run_inv_branch_nil in H.
      exists [].
      exists m.
      simpl.
      rewrite e_prod_nil_l.
      split. { reflexivity. }
      split; auto using map_nil.
    }
    apply f_run_inv_branch_cons in H.
    destruct H as (m1, (m2, (R1, (Hr1, Hr2)))).
    inversion H0; subst; clear H0.
    apply IHl in Hr2; auto; clear IHl.
    destruct Hr2 as (hss, (hs3, (R2,(Hr,Hf)))).
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m3, (m4, (R3, (Hr1, Hr2)))).
    eapply map_cons in Hf; eauto.
    exists (m3::hss).
    exists m4.
    split; auto.
    rewrite R3 in *; clear R3.
    rewrite R1 in *; clear R1.
    assert (R4: hs3 == m4) by eauto using f_run_fun.
    simpl.
    rewrite R2; clear R2.
    rewrite R4; clear R4.
    rewrite e_prod_plus_l.
    reflexivity.
  Qed.

  Lemma f_run_inv_decl:
    forall x r i1 i2 m,
    FRun (Decl x r i1 i2) m ->
    exists l,
    RStep r l /\ FRun (Branch x l i1 i2) m.
  Proof.
    intros.
    destruct H as (m', (R, Hr)).
    inversion Hr; subst; clear Hr.
    exists l.
    rewrite R.
    eauto using f_run_eq.
  Qed.

  Lemma f_run_decl_inv_map:
    forall n1 n2 i1 i2 x m',
    FRun (Decl x (NNum n1, NNum n2) i1 i2) m' ->
    exists lm m,
    EEq m' (Prod (summation lm) m) /\
    FRun i2 m /\
    DeclMap x i1 n1 n2 lm.
  Proof.
    intros.
    apply f_run_inv_decl in H.
    destruct H as (l, (Hr, Hb)).
    apply r_step_to_range_list in Hr.
    subst.
    eauto using f_run_branch_inv_map, range_list_no_dup.
  Qed.
(*
  Definition branch_iter n1 n2 f :=
    @List.map nat (list history) f (range_list n1 n2).

  Lemma decl_map_inv:
    forall n1 n2 i x hs',
    DeclMap x i n1 n2 hs' ->
    exists f,
    hs' = branch_iter n1 n2 f /\
    (forall n, n1 <= n < n2 -> Run (i_subst x (NNum n) i) (f n)).
  Proof.
    intros.
    unfold DeclMap in H.
    apply branch_map_inv in H; auto using range_list_no_dup.
    destruct H as (f, (?, Hf)).
    subst.
    exists f.
    auto using range_list_in.
  Qed.*)

  Lemma impl_branch_seq_1:
    forall x l i j k,
    ~ In x i ->
    l <> [] ->
    ProgImpl
      (Branch x l (seq i j) k)
      (seq i (Branch x l j k)).
  Proof.
    unfold ProgImpl.
    induction l. {
      intros.
      contradiction.
    }
    intros i j k Hnin _ m1 Hr1.
    destruct l. {
      clear IHl.
      apply f_run_inv_branch_cons in Hr1.
      destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
      rewrite R1; clear R1.
      apply f_run_inv_branch_nil in Hr2.
      repeat rewrite i_subst_seq in Hr1.
      rewrite i_subst_not_in in Hr1; eauto.
      apply f_run_inv_seq in Hr1.
      destruct Hr1 as (m4, (m5, (R1, (Hr1, Hr3)))).
      rewrite R1; clear R1.
      assert (R1: m5 == m3) by eauto using f_run_fun.
      rewrite R1 in *; clear R1 Hr3.
      clear m1 m2 m5.
      apply f_run_inv_seq in Hr1.
      destruct Hr1 as (m1, (m2, (R, (Hr3, Hr4)))).
      rewrite R; clear R.
      assert (Hb: Branch x [a] j k // (m2 * m3)). {
        assert (i_subst x (NNum a) j ;; k // (m2 * m3)) by eauto using f_run_seq_eq.
        eapply f_run_branch_cons; eauto using f_run_branch_nil.
        rewrite e_prod_plus_absorb_rw.
        reflexivity.
      }
      rewrite e_prod_plus_absorb_rw.
      rewrite e_prod_assoc.
      auto using f_run_seq_eq.
    }
    apply f_run_inv_branch_cons in Hr1.
    destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
    rewrite R1; clear R1 m1.
    assert (Hne2: n :: l <> []). {
      intros N.
      inversion N.
    }
    apply IHl in Hr2; eauto; clear IHl Hne2.
    repeat rewrite i_subst_seq in Hr1.
    rewrite i_subst_not_in in Hr1; eauto.
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m1, (m4, (R, (Hr1, Hr3)))).
    rewrite R; clear R m2.
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m2, (m5, (R, (Hr1, Hr4)))).
    rewrite R; clear R m1.
    apply f_run_inv_seq in Hr2.
    destruct Hr2 as (m1, (m6, (R, (Hr2, Hr5)))).
    rewrite R; clear R m3.
    assert (R: m2 == m1) by eauto using f_run_fun.
    rewrite R in *; clear R m2 Hr2.
    rewrite e_prod_assoc.
    rewrite e_prod_plus_r.
    apply f_run_seq_eq; auto.
    apply f_run_branch_cons_eq; auto.
    apply f_run_seq_eq; auto.
  Qed.

  Lemma impl_branch_seq_2:
    forall x l i j k,
    ~ In x i ->
    l <> [] ->
    ProgImpl
      (seq i (Branch x l j k))
      (Branch x l (seq i j) k).
  Proof.
    unfold ProgImpl.
    induction l. {
      intros.
      contradiction.
    }
    intros i j k Hnin _ m1 Hr1.
    apply f_run_inv_seq in Hr1.
    destruct Hr1 as (m2, (m3, (R1, (Hr1, Hr2)))).
    rewrite R1; clear R1 m1.
    apply f_run_inv_branch_cons in Hr2.
    destruct Hr2 as (m1, (m4, (R, (Hr2, Hr3)))).
    rewrite R; clear R m3.
    apply f_run_inv_seq in Hr2.
    destruct Hr2 as (m3, (m5, (R, (Hr2, Hr4)))).
    rewrite R; clear R m1.
    destruct l. {
      clear IHl.
      apply f_run_inv_branch_nil in Hr3.
      assert (R: m4 == m5) by eauto using f_run_fun.
      rewrite R in *; clear R m4 Hr4.
      rewrite e_prod_plus_absorb_rw.
      apply f_run_branch_cons with (m1:=m2 * m3 * m5) (m2:=m5).
      + rewrite i_subst_seq.
        rewrite i_subst_not_in; auto.
        auto using f_run_seq_eq.
      + auto using f_run_branch_nil.
      + rewrite e_prod_plus_absorb_rw.
        rewrite e_prod_assoc.
        reflexivity.
    }
    assert (Hr: i ;; Branch x (n :: l) j k // m2 * m4)
      by auto using f_run_seq_eq.
    clear Hr3.
    assert (Hne: n :: l <> []) by (intros N; inversion N).
    apply IHl in Hr; auto; clear Hne IHl.
    apply f_run_branch_cons with (m1:=m2*m3*m5) (m2 := m2 * m4); auto.
    + rewrite i_subst_seq.
      rewrite i_subst_not_in; auto using f_run_seq_eq.
    + rewrite e_prod_assoc.
      rewrite e_prod_plus_r.
      reflexivity.
  Qed.

  Lemma equiv_i_subst_branch_seq:
    forall i j k l x,
    ~ In x i ->
    l <> [] ->
    ProgEquiv
      (Branch x l (seq i j) k)
      (seq i (Branch x l j k)).
  Proof.
    auto using prog_equiv_def, impl_branch_seq_1, impl_branch_seq_2.
  Qed.

  Lemma equiv_i_subst_decl_seq:
    forall i j k n1 n2 x,
    ~ In x i ->
    n1 < n2 ->
    ProgEquiv
      (Decl x (NNum n1, NNum n2) (seq i j) k)
      (seq i (Decl x (NNum n1, NNum n2) j k)).
  Proof.
    intros.
    apply prog_equiv_def; apply prog_impl_def; intros. {
      apply f_run_inv_decl in H1.
      destruct H1 as (l, (Hr, Hb)).
      assert (Hrs := Hr).
      apply r_step_to_range_list in Hr; subst.
      apply equiv_i_subst_branch_seq in Hb; auto using range_list_not_nil.
      apply f_run_inv_seq in Hb.
      destruct Hb as (m1, (m2, (R, (Hr1, Hr2)))).
      rewrite R; clear R m.
      eapply f_run_decl in Hr2; eauto.
      apply f_run_seq_eq; eauto using f_run_decl.
    }
    apply f_run_inv_seq in H1.
    destruct H1 as (m1, (m2, (R, (Hr1, Hr2)))).
    rewrite R; clear R m.
    apply f_run_inv_decl in Hr2.
    destruct Hr2 as (l, (Hrs, Hb)).
    assert (Hr := Hrs).
    apply r_step_to_range_list in Hr; subst.
    apply f_run_seq_eq with (i1:=i) (m1:=m1) in Hb; auto.
    apply equiv_i_subst_branch_seq in Hb; auto using range_list_not_nil.
    eapply f_run_decl in Hb; eauto.
  Qed.

  Lemma branch_map_inv_seq:
    forall l x i j ms1, 
    BranchMap x (seq i j) l ms1 ->
    exists ms2 ms3,
    BranchMap x i l ms2 /\ BranchMap x j l ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      eauto using map_nil, e_eq_list_nil.
    }
    inversion H; subst; clear H.
    rewrite i_subst_seq in H2.
    apply f_run_inv_seq in H2.
    destruct H2 as (hs1, (hs2, (R, (Hra, Hrb)))).
    apply IHl in H5.
    destruct H5 as (ms2, (ms3, (Hb1, (Hb2, R2)))).
    eexists.
    eexists.
    repeat split.
    - eauto using map_cons.
    - eauto using map_cons.
    - rewrite map2_cons_rw.
      auto using e_eq_list_cons.
  Qed.

  Lemma branch_map_seq:
    forall l x i j ms1 ms2, 
    BranchMap x i l ms1 ->
    BranchMap x j l ms2 ->
    BranchMap x (seq i j) l (map2 Prod ms1 ms2).
  Proof.
    induction l; intros; inversion H; inversion H0; subst; clear H H0. {
      apply map_nil.
    }
    rewrite map2_cons_rw.
    apply map_cons; auto.
    rewrite i_subst_seq.
    auto using f_run_seq_eq.
  Qed.

  Lemma decl_map_inv_seq:
    forall n1 n2 x i j ms1, 
    DeclMap x (seq i j) n1 n2 ms1 ->
    exists ms2 ms3,
    DeclMap x i n1 n2 ms2 /\ DeclMap x j n1 n2 ms3 /\ EEqList ms1 (map2 Prod ms2 ms3).
  Proof.
    eauto using branch_map_inv_seq.
  Qed.

  Lemma decl_map_seq:
    forall n1 n2 x i j ms1 ms2, 
    DeclMap x i n1 n2 ms1 ->
    DeclMap x j n1 n2 ms2 ->
    DeclMap x (seq i j) n1 n2 (map2 Prod ms1 ms2).
  Proof.
    unfold DeclMap.
    eauto using branch_map_seq.
  Qed.

  Lemma decl_map_inv_i_subst_eq:
    forall x y i n1 n2 m1,
    ~ In x i ->
    DeclMap x (i_subst y (NVar x) i) n1 n2 m1 ->
    DeclMap y i n1 n2 m1.
  Proof.
    unfold DeclMap.
    intros x y i n1 n2 m1 Hn1 Hd.
    apply map_impl with (P:=Iter x (i_subst y (NVar x) i)); auto.
    intros.
    rewrite i_subst_subst_trans in H; auto.
  Qed.

  Lemma run_decl_seq:
    forall x n1 n2 i j k m1 m2 m3,
    FRun k m1 ->
    DeclMap x i n1 n2 m2 ->
    DeclMap x j n1 n2 m3 ->
    FRun (Decl x (NNum n1, NNum n2) (seq i j) k) (Prod (summation (map2 Prod m2 m3)) m1).
  Proof.
    intros.
    eapply f_run_decl_map; eauto.
    apply decl_map_seq; auto.
  Qed.

  Let i_subst_not_in_decl_rw:
    forall x n1 y n2 i j hs,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    FRun (i_subst x (NNum n2) (Decl y (NNum n1, NVar x) i j)) hs ->
    FRun (Decl y (NNum n1, NNum n2) i j) hs.
  Proof.
    intros.
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
    end.
    simpl in Hr.
    destruct (Set_VAR.MF.eq_dec x x) as [_|?].
    2: { contradiction. }
    destruct (Set_VAR.MF.eq_dec x y) as [?|_]. { contradiction. }
    rewrite i_subst_not_in in Hr; auto.
    rewrite i_subst_not_in in Hr; auto.
  Qed.

  Lemma branch_map_inv_decl_not_in:
    forall l n1 i j ms x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    l <> [] ->
    BranchMap x (Decl y (NNum n1, NVar x) i j) l ms ->
    NoDup l ->
    exists m hs,
    EEqList ms (map (fun x => (Prod (summation x) m)) hs) /\
    FRun j m /\
    Map (DeclMap y i n1) l hs.
  Proof.
    induction l; intros n i j ms x y Hn1 Hn2 Hneq Hnil Hb Hd. {
      contradiction.
    }
    clear Hnil.
    destruct l; inversion Hb; subst; clear Hb. {
      match goal with
      | [ H: FRun _ _ |- _ ] => rename H into Hr
      end.
      apply i_subst_not_in_decl_rw in Hr; auto.
      apply f_run_decl_inv_map in Hr.
      destruct Hr as (ms1, (m2, (R, (Hr, Hm)))).
      inversion H4; clear H4.
      subst.
      exists m2.
      simpl.
      exists [ms1].
      simpl.
      rewrite R.
      repeat split; auto using map_cons, map_nil.
      reflexivity.
    }
    match goal with
    | [ H: FRun _ _ |- _ ] => rename H into Hr
    end.
    apply i_subst_not_in_decl_rw in Hr; auto.
    apply f_run_decl_inv_map in Hr.
    destruct Hr as (ms1, (m2, (R, (Hr, Hm)))).
    subst.
    inversion Hd; subst; clear Hd.
    apply IHl in H4; auto; clear IHl.
    2: { intros N; inversion N. }
    destruct H4 as (m, (hs, (R1, (Hr2, Hmap)))).
    assert (m2 == m) by eauto using f_run_fun; subst. 
    exists m.
    exists (ms1::hs).
    repeat split; auto using map_cons.
    simpl.
    rewrite <- R1.
    rewrite R.
    rewrite H.
    reflexivity.
  Qed.

  Lemma decl_map_inv_decl_not_in:
    forall n1 n2 n3 i j ms x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 ms ->

    exists (m:list history) (hs:list (list (list history))),
    ms = (map (fun x => (prod (@List.concat history x) m) ++ m) hs) /\
    FRun j m /\
    Map (DeclMap y i n1) (range_list n2 n3) hs.
  Proof.
    intros.
    apply branch_map_inv_decl_not_in in H3; auto using range_list_no_dup, range_list_not_nil.
  Qed.

  Lemma branch_map_decl:
    forall l n1 i j m hs x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    l <> [] ->
    NoDup l ->
    Run j m ->
    Map (DeclMap y i n1) l hs ->
    BranchMap x (Decl y (NNum n1, NVar x) i j) l (map (fun x => (prod (@List.concat history x) m) ++ m) hs).
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H3; subst; clear H3.
    inversion H5; subst; clear H5.
    destruct l. {
      inversion H12; subst; clear H12.
      apply branch_map_cons; auto using branch_map_nil.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    }
    apply branch_map_cons.
    - simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      eapply run_decl_map; eauto.
      + rewrite i_subst_not_in; auto.
      + rewrite i_subst_not_in; auto.
    - apply IHl; auto.
      intros N; inversion N.
  Qed.

  Lemma decl_map_decl:
    forall n1 n2 n3 i j hs m x y,
    ~ In x i ->
    ~ In x j ->
    x <> y ->
    n2 < n3 ->
    Run j m ->
    Map (DeclMap y i n1) (range_list n2 n3) hs ->
    DeclMap x (Decl y (NNum n1, NVar x) i j) n2 n3 (map (fun x => (prod (@List.concat history x) m) ++ m) hs) .
  Proof.
    intros.
    apply branch_map_decl; auto using range_list_no_dup, range_list_not_nil.
  Qed.


  Lemma branch_map_inv_acc:
    forall l x e i ms,
    BranchMap x (Acc e i) l ms ->
    exists ms1 ms2,
    ms = map2 prod ms1 ms2 /\
    BranchMap x (Acc e Skip) l ms1 /\
    BranchMap x i l ms2.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      exists [].
      exists [].
      repeat split; auto using branch_map_nil.
    }
    inversion H; subst; clear H.
    apply IHl in H4; clear IHl.
    destruct H4 as (ms1, (ms2, (?, (Hb1, Hb2)))).
    subst.
    simpl in H2.
    destruct e as (ac, e).
    inversion H2; subst; clear H2.
    assert (Hra: Run (Acc (access_subst x (NNum a) ac, n_subst x (NNum a) e) Skip) (prepend v [[]])). {
      auto using run_access, run_skip.
    }
    eapply branch_map_cons in Hb1; eauto; clear Hra.
    exists (prepend v [[]] :: ms1).
    eapply branch_map_cons in Hb2; eauto.
    exists (hs0 :: ms2).
    simpl in *.
    rewrite app_nil_r in *.
    rewrite map2_cons_rw.
    rewrite prepend_rw.
    auto.
  Qed.

  Lemma decl_map_inv_acc:
    forall x e i n1 n2 ms,
    DeclMap x (Acc e i) n1 n2 ms ->
    exists ms1 ms2,
    ms = map2 prod ms1 ms2 /\
    DeclMap x (Acc e Skip) n1 n2 ms1 /\
    DeclMap x i n1 n2 ms2.
  Proof.
    intros.
    unfold DeclMap in *.
    apply branch_map_inv_acc in H.
    destruct H as (ms1, (ms2, (?, (Hb1, Hb2)))).
    eauto.
  Qed.

  Lemma impl_branch_nil_1:
    forall x i j,
    ProgImpl
      (Branch x [] i j)
      j.
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    inversion H; subst; clear H.
    exists m1.
    split; auto; reflexivity.
  Qed.

  Lemma impl_branch_nil_2:
    forall x i j,
    ProgImpl
      j
      (Branch x [] i j).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    exists m1.
    split; auto using run_branch_nil; reflexivity.
  Qed.

  Lemma p_eq_branch_nil:
    forall x i j,
    ProgEquiv (Branch x [] i j) j.
  Proof.
    intros.
    auto using prog_equiv_def, impl_branch_nil_1, impl_branch_nil_2.
  Qed.

  Import Morphisms.

  Lemma p_eq_seq_impl:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgImpl (seq i1 j1) (seq i2 j2).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    apply run_inv_seq in H1.
    destruct H1 as (hs1, (hs2, (?, (Hr1, Hr2)))).
    subst.
    assert (hs1 <> []) by eauto using run_not_nil.
    assert (hs2 <> []) by eauto using run_not_nil.
    eapply run_prog_equiv_inv_l in Hr1; eauto.
    destruct Hr1 as (m2, (Hr_i2, ?)).
    eapply run_prog_equiv_inv_l in Hr2; eauto.
    destruct Hr2 as (m3, (Hr_j2, ?)).
    exists (prod m2 m3).
    split; auto using run_seq.
    rewrite mem_equiv_prod_l with (m4:=m2); eauto using run_not_nil.
    rewrite mem_equiv_prod_r with (m4:=m3); eauto using run_not_nil.
    reflexivity.
  Qed.

  Lemma p_eq_seq:
    forall i1 i2 j1 j2,
    ProgEquiv i1 i2 ->
    ProgEquiv j1 j2 ->
    ProgEquiv (seq i1 j1) (seq i2 j2).
  Proof.
    intros.
    apply prog_equiv_def.
    - auto using p_eq_seq_impl.
    - symmetry in H.
      symmetry in H0.
      auto using p_eq_seq_impl.
  Qed.

  Global Instance seq_p_equiv_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgEquiv) seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq.
  Qed.

  Global Instance seq_p_impl_proper: Proper (ProgEquiv ==> ProgEquiv ==> ProgImpl) seq.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using p_eq_seq_impl.
  Qed.

  Global Instance proper_prog_impl_2: Proper (ProgEquiv ==> ProgEquiv ==> Basics.flip Basics.impl) ProgImpl.
  Proof.
    unfold Proper, respectful.
    intros.
    unfold Basics.flip.
    unfold Basics.impl.
    intros.
    rename x into i1.
    rename y into i2.
    rename x0 into j1.
    rename y0 into j2.
    destruct H.
    destruct H0.
    transitivity i2; auto.
    transitivity j2; auto.
  Qed.
(*
  Lemma prog_impl_branch_cons:
    forall x a l i,
    ProgImpl (Branch x (a :: l) i Skip)
        (seq (i_subst x (NNum a) i) (Branch x l i Skip)).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    inversion H; subst; clear H.
    subst.
    eexists.
    split. {
      rewrite seq_nil_rw in *.
      apply run_seq; eauto.
    }
  Qed.
  *)
(*
  Lemma prog_impl_branch_cons:
    forall x a l i k,
    ProgImpl (Branch x (a :: l) i k)
        (Or (seq (i_subst x (NNum a) i) k) (Branch x l i k)).
  Proof.
    intros.
    apply prog_impl_def.
    intros.
    inversion H; subst; clear H.
    subst.
    eexists.
    split. {
      apply run_seq; eauto.
    }
  Qed.
*)


  Import PairInUtil.
  Lemma impl_branch_branch_seq_1:
    forall x l i1 i2 j1 j2,
    ProgImpl
      (Branch x l (seq i1 i2) (seq j1 j2))
      (seq (Branch x l i1 j1) (Branch x l i2 j2)).
  Proof.
    induction l; intros. {
      rewrite p_eq_branch_nil.
      rewrite p_eq_branch_nil.
      rewrite p_eq_branch_nil.
      reflexivity.
    }
    apply prog_impl_def.
    intros.
    inversion H; subst; clear H.
    apply IHl in H7; clear IHl.
    destruct H7 as (m2, (Hr, R1)).
    apply run_inv_seq in H6.
    destruct H6 as (m1, (m3, (?, (Hr2, Hr3)))).
    apply run_inv_seq in Hr.
    destruct Hr as (m4, (m5, (?, (Hr4, Hr5)))).
    apply run_inv_seq in Hr3.
    destruct Hr3 as (m6, (m7, (?, (Hr6, Hr7)))).
    rewrite i_subst_seq in Hr2.
    apply run_inv_seq in Hr2.
    destruct Hr2 as (m8, (m9, (?, (Hr8, Hr9)))).
    subst.
    eexists.
    split. {
      apply run_seq.
      - apply run_branch_cons.
        + apply run_seq; eauto.
        + eauto.
      - apply run_branch_cons.
        + apply run_seq; eauto.
        + eauto.
    }
    rewrite R1; clear R1.
    rename m8 into m_i1.
    rename m9 into m_i2.
    rename m6 into m_j1.
    rename m7 into m_j2.
    rename m4 into m_b_i1.
    rename m5 into m_b_i2.
    repeat rewrite prod_assoc.
    split; intros.
    - apply m_pair_in_app_or in H.
      destruct H. {
        apply m_pair_in_inv_prod in H.
        destruct H as [H|[H|[H|H]]].
        - (* MPairIn p m_i1 *)
          apply m_pair_in_prod_l. {
            apply m_pair_in_app_l.
            apply m_pair_in_prod_l; eauto using run_not_nil.
          }
          admit.
        - apply m_pair_in_inv_prod in H.
          destruct H as [H|[H|[(Hl,Hr)|(Hl,Hr)]]].
          + (* MPairIn p m_i2 *) admit.
          + apply m_pair_in_inv_prod in H.
            destruct H as [H|[H|[(Hl,Hr)|(Hl,Hr)]]].
            * (* MPairIn p m_j1 *) admit.
            * (* MPairIn p m_j2 *) admit.
            * destruct p as (v1, v2).
              (* MIn v1 m_j1 /\ MIn v2 m_j2 *)
              simpl in *.
              admit.
            * destruct p as (v1, v2).
              simpl in *.
              (* MIn v1 m_j2 /\ MIn v2 m_j1 *)
              admit.
          + destruct p as (v1, v2).
            simpl in *.
            apply m_in_prod_inv in Hr.
            destruct Hr as [Hr|Hr]. {
              (*  MIn v1 m_i2 /\ MIn v2 m_j1 *)
            }
            Search (MIn _ (prod _ _)).
            apply m_in_inv_prod in Hr.
      }
      Search (MPairIn _ (app _ _)).
    rewrite <- prod_app.
    rewrite prod_assoc.
    Search (MemEquiv (prod _ _)). 
    rewrite prod_assoc.
    rewrite <- prod_assoc.
    rewrite prod_app.
    repeat (rewrite prod_assoc | rewrite prod_app).
    rewrite prod_app.
  Qed.

  Lemma impl_branch_seq_2:
    forall x l i j k,
    ProgImpl
      (seq (Branch x l i k) (Branch x l j k))
      (Branch x l (seq i j) k).
  Proof.
  Qed.