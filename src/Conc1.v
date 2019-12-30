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
  | gen_access_nil:
    GenAccess a 0 []
  | gen_access_cons:
    forall n v l,
    GenAccess a n l ->
    access_step (access_subst TID n a, NNum  n) v ->
    GenAccess a (S n) (v::l).

  Inductive Step: state -> state -> Prop :=
  | step_access:
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

  Lemma gen_access_lt:
    forall e n v,
    GenAccess e n v ->
    forall m,
    m < n ->
    exists l, access_step (access_subst TID m e, NNum m) l /\ List.In l v.
  Proof.
    intros e n v Hg.
    induction Hg; intros. {
      inversion H.
    }
    inversion H0; subst; clear H0. {
      exists v.
      auto using in_eq.
    }
    assert (Hx: m < n) by auto with *.
    apply IHHg in Hx.
    destruct Hx as (l', (Hs, Hi)).
    eauto using in_cons.
  Qed.

  Lemma gen_access_in:
    forall e n v,
    GenAccess e n v ->
    forall l,
    List.In l v ->
    exists m, access_step (access_subst TID m e, NNum m) l /\ m < n.
  Proof.
    intros e n v Hg.
    induction Hg; intros. {
      contradiction.
    }
    destruct H0; subst. {
      eauto.
    }
    apply IHHg in H0.
    destruct H0 as (m, (Hs, Hlt)).
    eauto.
  Qed.


  Section Step2.
    Inductive Step2 (tid1 tid2:nat): state -> state -> Prop :=
    | step2_access_1:
      forall s e v1 v2,
      access_step (access_subst TID tid1 e, NNum tid1) v1 ->
      access_step (access_subst TID tid2 e, NNum tid2) v2 ->
      tid2 < tid1 ->
      Step2 tid1 tid2 (s, Acc e) (v1 ++ v2 ++ s, Skip)
    | step2_access_2:
      forall s e v1 v2,
      access_step (access_subst TID tid1 e, NNum tid1) v1 ->
      access_step (access_subst TID tid2 e, NNum tid2) v2 ->
      tid1 < tid2 ->
      Step2 tid1 tid2 (s, Acc e) (v2 ++ v1 ++ s, Skip)
    | step2_seq_step:
      forall s1 s2 p1 p2 p3,
      Step2 tid1 tid2 (s1, p1) (s2, p2) ->
      Step2 tid1 tid2 (s1, Seq p1 p3) (s2, Seq p2 p3)
    | step2_seq_skip:
      forall s p,
      Step2 tid1 tid2 (s, Seq Skip p) (s, p)
    | step2_for:
      forall x r p l s,
      RStep r l ->
      Step2 tid1 tid2 (s, For x r p) (s, Loop x l p)
    | step2_loop_step:
      forall s x n l p,
      Step2 tid1 tid2 (s, Loop x (n::l) p) (s, Seq (i_subst x n p) (Loop x l p))
    | step2_loop_skip:
      forall s x p,
      Step2 tid1 tid2 (s, Loop x [] p) (s, Skip).

  Definition proj2 t1 t2 (s:state) := let (h, p) := s in (Hist.proj2 t1 t2 h, p).
  End Step2.


  Fixpoint gen_access a n :=
    let a_step n := access_eval1 (access_subst TID n a, NNum n) in 
    match n with
    | 0 => Some []
    | S n =>
      match a_step n, gen_access a n with
      | Some v, Some l => Some (v :: l)
      | _, _ => None
      end
    end.

  Fixpoint step_iter h p : option state :=
    match p with
    | Acc e =>
      match gen_access e TID_COUNT with
      | Some l => Some (List.flat_map id l ++ h, Skip) 
      | None => None
      end
    | Seq Skip p => Some (h, p) 
    | Seq e1 e2 =>
      match step_iter h e1 with
      | Some (h, e3) => Some (h, Seq e3 e2)
      | None => None
      end 
    | For x r p =>
      match r_step r with
      | Some l => Some (h, Loop x l p)
      | None => None
      end 
    | Loop x [] p => Some (h, Skip)
    | Loop x (n::l) p => Some (h, Seq (i_subst x n p) (Loop x l p))
    | Skip => None
    end.

  Definition step (s:state) := let (h, p) := s in step_iter h p.

  Lemma gen_access_to_prop:
    forall a n l,
    gen_access a n = Some l ->
    GenAccess a n l.
  Proof.
    induction n; simpl; intros. {
      inversion H; subst; clear H.
      apply gen_access_nil.
    }
    destruct (access_eval1 _) eqn:He. {
      apply access_eval1_to_step in He.
      destruct (gen_access a n) eqn:Hg. {
        inversion H; subst; clear H.
        auto using gen_access_cons.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Lemma prop_to_gen_access:
    forall a n l,
    GenAccess a n l ->
    gen_access a n = Some l.
  Proof.
    induction n; intros; simpl; inversion H; subst; clear H. {
      reflexivity.
    }
    apply access_step_to_eval1 in H2.
    rewrite H2.
    apply IHn in H1.
    rewrite H1.
    reflexivity. 
  Qed.

  Fixpoint count n :=
  match n with
  | 0 => []
  | S n => n :: count n
  end.

  Definition gen_access_item a n :=
    match access_eval1 (access_subst TID n a, NNum n) with
    | Some v => v
    | None => []
    end.

  Definition gen_access_iter a n := List.flat_map (gen_access_item a) (count n).

  Lemma gen_access_iter_rw:
    forall a n l,
    GenAccess a n l ->
    gen_access_iter a n = flat_map id l.
  Proof.
    intros a n l Hg.
    unfold gen_access_iter, gen_access_item; induction Hg. {
      reflexivity.
    }
    simpl.
    rewrite IHHg.
    apply access_step_to_eval1 in H.
    rewrite H.
    reflexivity.
  Qed.
  Import Omega.

  Lemma gen_access_proj2_1:
    forall n a v n1 n2,
    GenAccess a n v ->
    n1 >= n ->
    n2 >= n ->
    Hist.proj2 n1 n2 (flat_map id v) = [].
  Proof.
    induction n; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite Hist.proj2_app.
    assert (R: Hist.proj2 n1 n2 (id v0) = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R; clear R.
    simpl.
    eapply IHn; eauto with *.
  Qed.

  Lemma gen_access_proj2_2:
    forall n a v,
    GenAccess a n v ->
    forall t1 t2,
    t1 < n ->
    t2 >= n ->
    Hist.proj2 t1 t2 (flat_map id v) = gen_access_item a t1.
  Proof.
    induction n; intros. {
      omega.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite Hist.proj2_app.
    assert (R: id v0 = v0) by auto; rewrite R; clear R.
    inversion H0; subst; clear H0. {
      (* t1 = 0 /\ n = 1 *)
      erewrite proj2_id_l; eauto.
      assert (R: Hist.proj2 n t2 (flat_map id l) = []). {
        erewrite gen_access_proj2_1; eauto.
        omega.
      }
      rewrite R.
      unfold gen_access_item.
      apply access_step_to_eval1 in H4.
      rewrite H4.
      rewrite app_nil_r.
      reflexivity.
    }
    apply IHn with (t1:=t1) (t2:= t2) in H3; auto with *.
    rewrite H3.
    assert (R: Hist.proj2 t1 t2 v0 = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R.
    auto.
  Qed.

  Lemma gen_access_proj_3:
    forall n a v,
    GenAccess a n v ->
    forall t1 t2,
    t1 < n ->
    t2 < n ->
    t1 < t2 ->
    Hist.proj2 t1 t2 (flat_map id v) = gen_access_item a t2 ++ gen_access_item a t1.
  Proof.
    induction n; intros; inversion H; subst; clear H. {
      inversion H0.
    }
    simpl.
    rewrite Hist.proj2_app.
    assert (R: id v0 = v0) by auto; rewrite R; clear R.
    inversion H0; subst; clear H0. {
      (* t1 = n *)
      inversion H1; subst; clear H1. {
        (* t2 = n *)
        omega.
      }
      (* t2 < n *)
      omega.
    }
    assert (t1 < n) by auto.
    inversion H1; subst; clear H1. {
      (* t2 = n *)
      assert (R: Hist.proj2 t1 n (flat_map id l) = gen_access_item a t1). {
        eapply gen_access_proj2_2; eauto.
      }
      rewrite R; clear R.
      erewrite proj2_id_r; eauto.
      assert (R: gen_access_item a n = v0). { 
        unfold gen_access_item.
        apply access_step_to_eval1 in H5.
        rewrite H5.
        reflexivity.
      }
      rewrite R.
      reflexivity.
    }
    assert (R: Hist.proj2 t1 t2 v0 = []). {
      eapply proj2_neq; eauto with *.
    }
    rewrite R.
    simpl.
    eauto.
  Qed.

  Lemma gen_access_proj2:
    forall n a v,
    GenAccess a n v ->
    forall t1 t2,
    t1 < n ->
    t2 < n ->
    t1 <> t2 ->
    (t1 < t2 /\ Hist.proj2 t1 t2 (flat_map id v) = gen_access_item a t2 ++ gen_access_item a t1)
    \/
    (t2 < t1 /\ Hist.proj2 t1 t2 (flat_map id v) = gen_access_item a t1 ++ gen_access_item a t2)
    .
  Proof.
    intros.
    apply nat_total_order in H2.
    destruct H2. {
      left; intuition.
      eauto using gen_access_proj_3.
    }
    right; intuition.
    rewrite Hist.proj2_symm.
    eapply gen_access_proj_3; eauto.
  Qed.

  Lemma step2_proj2:
    forall s1 s2,
    Step s1 s2 ->
    forall t1 t2,
    t1 < TID_COUNT ->
    t2 < TID_COUNT ->
    t1 <> t2 ->
    Step2 t1 t2 (proj2 t1 t2 s1) (proj2 t1 t2 s2).
  Proof.
    intros.
    induction H; simpl; try (constructor; auto; fail).
    assert (Hx := H0); assert (Hy := H1). 
    eapply gen_access_lt in H0; eauto.
    eapply gen_access_lt in H1; eauto.
    destruct H0 as (l1, (Hs1, Hi1)).
    destruct H1 as (l2, (Hs2, Hi2)).
    rewrite Hist.proj2_app.
    edestruct gen_access_proj2 with (t1:=t1) (t2:=t2) as [(Ha,Hb)|(Ha,Hb)]; eauto. {
      rewrite Hb.
      rewrite <- app_assoc.
      assert (R2: gen_access_item e t2 = l2). {
        unfold gen_access_item in *.
        apply access_step_to_eval1 in Hs2.
        rewrite Hs2 in *.
        reflexivity.
      }
      assert (R1: gen_access_item e t1 = l1). {
        unfold gen_access_item in *.
        apply access_step_to_eval1 in Hs1.
        rewrite Hs1 in *.
        reflexivity.
      }
      rewrite R1. rewrite R2.
      apply step2_access_2; auto.
    }
    rewrite Hb.
    rewrite <- app_assoc.
    assert (R2: gen_access_item e t2 = l2). {
      unfold gen_access_item in *.
      apply access_step_to_eval1 in Hs2.
      rewrite Hs2 in *.
      reflexivity.
    }
    assert (R1: gen_access_item e t1 = l1). {
      unfold gen_access_item in *.
      apply access_step_to_eval1 in Hs1.
      rewrite Hs1 in *.
      reflexivity.
    }
    rewrite R1. rewrite R2.
    apply step2_access_1; auto.
  Qed.


  Lemma step_iter_to_prop:
    forall p h s,
    step_iter h p = Some s ->
    Step (h, p) s.
  Proof.
    induction p; simpl; intros.
    - inversion H.
    - destruct (gen_access _ _) eqn:Hg; inversion H; subst; clear H.
      apply gen_access_to_prop in Hg.
      auto using step_access.
    - destruct p1.
      + inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
      + destruct (step_iter _ _) eqn:He2; try (inversion H; fail).
        destruct s0 as (h', s').
        inversion H; subst; clear H.
        constructor; auto.
    - destruct (r_step r) eqn:Hr; inversion H; subst; clear H.
      apply r_step_to_prop in Hr.
      constructor; auto.
    - destruct l;
      inversion H; subst; clear H;
      constructor.
  Qed.

  Lemma prop_to_step_iter:
    forall p h s,
    Step (h, p) s ->
    step_iter h p = Some s.
  Proof.
    induction p; intros; inversion H; subst; clear H; simpl; auto.
    - apply prop_to_gen_access in H3.
      rewrite H3.
      reflexivity.
    - apply IHp1 in H4.
      destruct p1; try (inversion H4; fail); rewrite H4; reflexivity.
    - apply prop_to_r_step in H5.
      rewrite H5.
      reflexivity.
  Qed.

  Lemma step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    intros.
    destruct s1 as (h, p).
    simpl in *.
    auto using step_iter_to_prop.
  Qed.

  Lemma prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    intros.
    destruct s1 as (h, p).
    apply prop_to_step_iter.
    auto.
  Qed.

End C1.
End C1.

Module Examples.
  Section Defs.
  Import C1.

  Definition TID := variable 0.

  Definition TID_NUM := 2.

  Notation b_step := (BStep TID_NUM TID).

  Infix "-->" := (Step TID_NUM TID) (at level 150).

  (* Helper function *)
  Fixpoint bstep fuel steps s :=
  match fuel with
  | 0 => (steps,s)
  | S n =>
    match step TID_NUM TID s with
    | Some s => bstep n (S steps) s
    | _ => (steps, s)
    end
  end.

  Definition run steps s := bstep steps 0 s.


  (* BAD: *)
  (* for x < n {
       [tid + x] 
     } *)

  Let x := variable 1.
  Let i1 := Acc (add (NVar TID) (NVar x), BBool true).
  Definition BAD :=
    For x (NNum 0, NNum 2) i1.

  Goal run 8 ([], BAD) =
    (8,
       ([{| OneDim.tid := 1; OneDim.index := 2 |}; {| OneDim.tid := 0; OneDim.index := 1 |};
         {| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip)
    ).
  auto. Qed.

  (* GOOD: *)
  (*
    for x < n {
      [x] if tid == x
    }
   *)

  Definition GOOD1 :=
    let x := variable 1 in
    For x (NNum 0, NNum 2) (
      Acc (NVar x, NRel NEq (NVar TID) (NVar x))
    ).

  Goal run 10 ([], GOOD1) =
    (8,
    ([{| OneDim.tid := 1; OneDim.index := 1 |}; {| OneDim.tid := 0; OneDim.index := 0 |}], Skip))
    .
    compute.
  auto. Qed.

  Definition GOOD2 :=
      Acc (NNum 9, BBool true).


  Goal run 10 ([], GOOD2) =
    (1,
    ([{| OneDim.tid := 1; OneDim.index := 9 |}; {| OneDim.tid := 0; OneDim.index := 9 |}], Skip))
    .
    compute.
  auto. Qed.

  End Defs.
End Examples.
