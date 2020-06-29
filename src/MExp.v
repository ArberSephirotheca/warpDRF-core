Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Access.
Require Import Util.
Require Import InUtil.
Require Import PairInUtil.
Require Import MultiHist.
Import ListNotations.

Section Defs.
  Context `{A:Access}.
  Notation history := (list access_val).

  (** Theory of memory expressions *)

  Inductive mexp :=
  | One: history -> mexp
  | Prod: mexp -> mexp -> mexp
  | Plus: mexp -> mexp -> mexp.

  (* We can flatten an expression down to a memory *)
  Fixpoint to_mem m :=
  match m with
  | One h => [h]
  | Prod m1 m2 => prod (to_mem m1) (to_mem m2)
  | Plus m1 m2 => app (to_mem m1) (to_mem m2)
  end.

  Fixpoint flatten_exp e :=
  match e with
  | One h => [[h]]
  | Prod e1 e2 => flatten_exp e1 ++ flatten_exp e2
  | Plus e1 e2 => flatten_exp e1 ++ flatten_exp e2
  end.

  Fixpoint m_in_list v (l:list (list history)) :=
  match l with
  | [] => False
  | m::l => MIn v m \/ m_in_list v l
  end.

  Lemma m_in_list_app_or:
    forall v l1 l2,
    m_in_list v (l1 ++ l2) ->
    m_in_list v l1 \/ m_in_list v l2.
  Proof.
    induction l1; intros; auto.
    simpl in *.
    destruct H; auto.
    apply IHl1 in H.
    destruct H; auto.
  Qed.

  Lemma m_in_list_app_l:
    forall v l1 l2,
    m_in_list v l1 ->
    m_in_list v (l1 ++ l2).
  Proof.
    induction l1; intros.
    - contradiction.
    - destruct H; simpl; auto.
  Qed.

  Lemma m_in_list_app_r:
    forall v l1 l2,
    m_in_list v l2 ->
    m_in_list v (l1 ++ l2).
  Proof.
    induction l1; intros.
    - assumption.
    - simpl.
      auto.
  Qed.

  Lemma m_in_list_to_Exists v l:
    m_in_list v l -> Exists (MIn v) l.
  Proof.
    intros.
    induction l; simpl in *. {
      contradiction.
    }
    destruct H. {
      auto using Exists_cons.
    }
    auto using Exists_cons.
  Qed.

  Lemma Exists_to_m_in_list v l:
    Exists (MIn v) l -> m_in_list v l.
  Proof.
    induction l; simpl in *; intros.
    - inversion H.
    - inversion H; subst; clear H; auto.
  Qed.

  Lemma m_in_list_Exists v l:
    m_in_list v l <-> Exists (MIn v) l.
  Proof.
    split; auto using m_in_list_to_Exists, Exists_to_m_in_list.
  Qed.

  Fixpoint one_of (p:access_val*access_val) l1 l2 :=
    let (v1, v2) := p in
    (m_in_list v1 l1 /\ m_in_list v2 l2)
    \/
    (m_in_list v2 l1 /\ m_in_list v1 l2).

  Fixpoint e_pair_in p pe :=
  match pe with
  | One h => PairIn p h
  | Plus e1 e2 =>
    (* MPairIn p (ls1 ++ ls2) ->
       MPairIn p ls1 \/ MPairIn p ls2 *)
    e_pair_in p e1 \/ e_pair_in p e2
  | Prod e1 e2 =>
    (*
       MPairIn p (prod m1 m2) ->
       MPairIn p m1 \/
       MPairIn p m2 \/
       (MIn (fst p) m1 /\ MIn (snd p) m2) \/
       (MIn (fst p) m2 /\ MIn (snd p) m1)
     *)
    e_pair_in p e1 \/ e_pair_in p e2 \/
    one_of p (flatten_exp e1) (flatten_exp e2)
  end.

  Lemma to_mem_not_nil:
    forall e,
    to_mem e <> nil.
  Proof.
    induction e; simpl.
    - intros N.
      inversion N.
    - auto using prod_neq_nil.
    - auto using app_neq_nil.
  Qed.

  Lemma m_in_list_1:
    forall e x,
    m_in_list x (flatten_exp e) ->
    MIn x (to_mem e).
  Proof.
    induction e; simpl; intros x Hi.
    - destruct Hi; try contradiction; auto.
    - apply m_in_list_app_or in Hi.
      destruct Hi. {
        apply IHe1 in H; auto.
        apply m_in_prod_l; eauto using to_mem_not_nil.
      }
      apply IHe2 in H; auto.
      apply m_in_prod_r; eauto using to_mem_not_nil.
    - apply m_in_list_app_or in Hi.
      destruct Hi. {
        apply IHe1 in H; auto.
        apply m_in_app_l; eauto using to_mem_not_nil.
      }
      apply IHe2 in H; auto.
      apply m_in_app_r; eauto using to_mem_not_nil.
  Qed.

  Lemma m_in_list_2:
    forall v e,
    MIn v (to_mem e) ->
    m_in_list v (flatten_exp e).
  Proof.
    induction e; simpl; intros.
    - auto.
    - apply m_in_prod_inv in H.
      destruct H as [Hx|Hx].
      + auto using m_in_list_app_l.
      + auto using m_in_list_app_r.
    - apply m_in_inv_app in H.
      destruct H; auto using m_in_list_app_l, m_in_list_app_r.
  Qed.

  Lemma on_of_1:
    forall e1 e2 x y,
    one_of (x,y) (flatten_exp e1) (flatten_exp e2) ->
    (MIn x (to_mem e1) /\ MIn y (to_mem e2))
    \/
    (MIn x (to_mem e2) /\ MIn y (to_mem e1)).
  Proof.
    intros.
    simpl in H.
    destruct H as [(Ha,Hb)|(Ha,Hb)].
    - apply m_in_list_1 in Ha; auto.
      apply m_in_list_1 in Hb; auto.
    - apply m_in_list_1 in Ha; auto.
      apply m_in_list_1 in Hb; auto.
  Qed.

  Lemma e_pair_in_1:
    forall p e,
    e_pair_in p e ->
    MPairIn p (to_mem e).
  Proof.
    induction e; intros Hp; intros; simpl in *.
    - auto using m_pair_in_eq.
    - destruct Hp as [Hp|[Hp|Hp]].
      + eauto using to_mem_not_nil, m_pair_in_prod_l.
      + eauto using to_mem_not_nil, m_pair_in_prod_r.
      + destruct p as (v1, v2).
        apply on_of_1 in Hp; auto.
        destruct Hp as [(Ha,Hb)|(Ha,Hb)].
        * auto using m_pair_in_prod_1.
        * auto using m_pair_in_prod_2.
    - destruct Hp as [Hp|Hp].
      + auto using m_pair_in_app_l.
      + auto using m_pair_in_app_r.
  Qed.

  Lemma e_pair_in_2:
    forall p e,
    MPairIn p (to_mem e) ->
    e_pair_in p e.
  Proof.
    induction e; simpl; intros Hi.
    - inversion Hi; subst; clear Hi; auto.
      inversion H0.
    - destruct p as (v1, v2).
      apply m_pair_in_inv_prod in Hi.
      destruct Hi as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]]; eauto; simpl in *.
      + apply m_in_list_2 in Ha; auto.
        apply m_in_list_2 in Hb; auto.
      + apply m_in_list_2 in Ha; auto.
        apply m_in_list_2 in Hb; auto.
    - apply m_pair_in_app_or in Hi.
      destruct Hi; auto.
  Qed.

  Definition EIncl e1 e2 :=
    forall p,
    e_pair_in p e1 ->
    e_pair_in p e2.

  Lemma e_incl_to_m_incl:
    forall x y,
    EIncl x y ->
    MIncl (to_mem x) (to_mem y).
  Proof.
    unfold EIncl.
    intros.
    unfold MIncl.
    intros.
    apply e_pair_in_2 in H0; auto using e_pair_in_1.
  Qed.

  Lemma m_incl_to_e_incl:
    forall x y,
    MIncl (to_mem x) (to_mem y) ->
    EIncl x y.
  Proof.
    unfold EIncl, MIncl.
    intros.
    eauto using e_pair_in_2, e_pair_in_1.
  Qed.

  Lemma e_incl_iff_m_incl:
    forall x y,
    MIncl (to_mem x) (to_mem y) <->
    EIncl x y.
  Proof.
    split; intros; auto using m_incl_to_e_incl, e_incl_to_m_incl.
  Qed.

  Lemma e_incl_refl:
    forall e,
    EIncl e e.
  Proof.
    intros.
    unfold EIncl.
    intros.
    assumption.
  Qed.

  Lemma e_inc_trans:
    forall x y z,
    EIncl x y ->
    EIncl y z ->
    EIncl x z.
  Proof.
    intros.
    rewrite <- e_incl_iff_m_incl in *.
    transitivity (to_mem y); auto.
  Qed.

  Definition EEq e1 e2 :=
    forall p,
    e_pair_in p e1 <->
    e_pair_in p e2.

  Lemma m_equiv_to_e_eq:
    forall e1 e2,
    EEq e1 e2 ->
    MemEquiv (to_mem e1) (to_mem e2).
  Proof.
    unfold EEq, MemEquiv.
    split; intros;
      apply e_pair_in_2 in H0;
      apply H in H0;
      eauto using e_pair_in_1.
  Qed.

  Lemma e_eq_to_m_equiv:
    forall e1 e2,
    MemEquiv (to_mem e1) (to_mem e2) ->
    EEq e1 e2.
  Proof.
    unfold EEq, MemEquiv.
    split; intros;
      apply e_pair_in_1 in H0;
      apply H in H0;
      eauto using e_pair_in_2.
  Qed.

  Lemma e_eq_iff_m_equiv:
    forall e1 e2,
    MemEquiv (to_mem e1) (to_mem e2) <->
    EEq e1 e2.
  Proof.
    split; intros; auto using e_eq_to_m_equiv, m_equiv_to_e_eq.
  Qed.

  Lemma e_eq_refl:
    forall e,
    EEq e e.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    reflexivity.
  Qed.

  Lemma e_eq_sym:
    forall x y,
    EEq x y ->
    EEq y x.
  Proof.
    intros.
    apply e_eq_iff_m_equiv in H.
    apply e_eq_iff_m_equiv.
    symmetry; assumption. 
  Qed.

  Lemma e_eq_trans:
    forall x y z,
    EEq x y ->
    EEq y z ->
    EEq x z.
  Proof.
    intros.
    apply e_eq_iff_m_equiv in H.
    apply e_eq_iff_m_equiv in H0.
    apply e_eq_iff_m_equiv.
    etransitivity; eauto.
  Qed.

  (** Register [EEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ EEq
    reflexivity proved by e_eq_refl
    symmetry proved by e_eq_sym
    transitivity proved by e_eq_trans
    as e_eq_setoid.


  Import Morphisms.

  Global Instance e_eq_proper_1: Proper (EEq ==> EEq ==> EEq) Plus.
  Proof.
    unfold Proper, respectful.
    intros.
    apply e_eq_iff_m_equiv in H.
    apply e_eq_iff_m_equiv in H0.
    apply e_eq_iff_m_equiv.
    simpl.
    auto using mem_equiv_app.
  Qed.


  Global Instance e_eq_proper_2: Proper (EEq ==> EEq ==> EEq) Prod.
  Proof.
    unfold Proper, respectful.
    intros.
    apply e_eq_iff_m_equiv in H.
    apply e_eq_iff_m_equiv in H0.
    apply e_eq_iff_m_equiv.
    simpl.
    apply mem_equiv_prod; auto using to_mem_not_nil.
  Qed.

  Lemma e_prod_plus_l:
    forall e1 e2 e3,
    EEq (Plus (Prod e1 e3) (Prod e2 e3)) (Prod (Plus e1 e2) e3).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite prod_app.
    reflexivity.
  Qed.

  Lemma e_prod_one_plus_l:
    forall l e1 e2,
    EEq (Prod (One l) (Plus e1 e2)) (Plus (Prod (One l) e1) (Prod (One l) e2)).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    repeat rewrite app_nil_r.
    rewrite prepend_app.
    reflexivity.
  Qed.

  Lemma one_of_app_l_l:
    forall p l1 l2 l3,
    one_of p l1 l3 ->
    one_of p (l1 ++ l2) l3.
  Proof.
    destruct p as (v1, v2).
    induction l1; simpl; intros.
    - destruct H as [([],_)|([],_)].
    - destruct H as [([Ha|Ha],Hb)|(Ha,H)];
      auto using m_in_list_app_l.
      destruct Ha; auto using m_in_list_app_l.
  Qed.

  Lemma one_of_app_l_r:
    forall p l1 l2 l3,
    one_of p l2 l3 ->
    one_of p (l1 ++ l2) l3.
  Proof.
    destruct p as (v1, v2).
    induction l1; simpl; intros.
    - destruct H; auto.
    - destruct H as [(Ha,Hb)|(Ha,Hb)]; auto using m_in_list_app_r.
  Qed.

  Lemma one_of_app_r_l:
    forall p l1 l2 l3,
    one_of p l1 l2 ->
    one_of p l1 (l2 ++ l3).
  Proof.
    destruct p as (v1, v2).
    induction l1; simpl; intros.
    - destruct H as [([],_)|([],_)].
    - destruct H as [([Ha|Ha],Hb)|(Ha,H)];
      auto using m_in_list_app_l.
  Qed.

  Lemma one_of_app_r_r:
    forall p l1 l2 l3,
    one_of p l1 l3 ->
    one_of p l1 (l2 ++ l3).
  Proof.
    destruct p as (v1, v2).
    induction l1; simpl; intros.
    - destruct H as [([],_)|([],_)].
    - destruct H as [([Ha|Ha],Hb)|(Ha,H)];
      auto using m_in_list_app_r.
  Qed.

  Lemma one_of_inv_app_r:
    forall p l1 l2 l3,
    one_of p l1 (l2 ++ l3) ->
    one_of p l1 l2 \/ one_of p l1 l3.
  Proof.
    intros (v1, v2).
    induction l1; simpl; intros. {
      destruct H as [([],_)|([],_)].
    }
    destruct H as [([Ha|Ha],Hb)|([Hb|Hb],Hc)].
    + apply m_in_list_app_or in Hb.
      destruct Hb; auto.
    + apply m_in_list_app_or in Hb.
      destruct Hb; auto.
    + apply m_in_list_app_or in Hc.
      destruct Hc; auto.
    + apply m_in_list_app_or in Hc.
      destruct Hc; auto.
  Qed.

  Lemma one_of_inv_app_l:
    forall p l1 l2 l3,
    one_of p (l1 ++ l2) l3 ->
    one_of p l1 l3 \/ one_of p l2 l3.
  Proof.
    intros (v1, v2).
    induction l1; simpl; intros. {
      destruct H as [(Ha,Hb)|(Ha,Hb)]; auto.
    }
    destruct H as [([Ha|Ha],Hb)|([Hb|Hb],Hc)]; auto.
    + apply m_in_list_app_or in Ha.
      destruct Ha; auto.
    + apply m_in_list_app_or in Hb.
      destruct Hb; auto.
  Qed.

  Lemma e_prod_plus_r:
    forall e1 e2 e3,
    EEq (Plus (Prod e1 e2) (Prod e1 e3)) (Prod e1 (Plus e2 e3)).
  Proof.
    split; intros.
    - simpl in *.
      destruct H as [[H|[H|H]]|[H|[H|H]]]; auto using one_of_app_r_l, one_of_app_r_r.
    - simpl in *.
      destruct H as [H|[[H|H]|H]]; auto.
      apply one_of_inv_app_r in H.
      destruct H; auto.
  Qed.

  Lemma e_prod_nil_l:
    forall m,
    EEq (Prod (One []) m) m.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite app_nil_r.
    rewrite prepend_nil_l.
    reflexivity.
  Qed.

  Lemma e_prod_nil_r:
    forall m,
    EEq (Prod m (One [])) m.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite prod_nil_nil_r.
    reflexivity.
  Qed.

  Lemma e_prod_assoc:
    forall m1 m2 m3,
    EEq (Prod (Prod m1 m2) m3) (Prod m1 (Prod m2 m3)).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite prod_assoc.
    reflexivity.
  Qed.

  Lemma e_plus_assoc:
    forall m1 m2 m3,
    EEq (Plus m1 (Plus m2 m3))
        (Plus (Plus m1 m2) m3).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma e_plus_nil_l:
    forall m,
    EEq (Plus (One []) m) m.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    rewrite mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Lemma e_plus_nil_r:
    forall m,
    EEq (Plus m (One [])) m.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    apply mequiv_app_nil_r.
  Qed.

  Lemma e_plus_sym:
    forall m1 m2,
    EEq (Plus m1 m2) (Plus m2 m1).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    apply mem_equiv_app_sym.
  Qed.

  Lemma one_of_sym_nil_l:
    forall p l,
    ~ one_of p [] l.
  Proof.
    intros.
    destruct p as (v1, v2).
    simpl.
    intros N.
    destruct N as [([],_)|([],_)].
  Qed.

  Lemma one_of_sym_nil_r:
    forall p l,
    ~ one_of p l [].
  Proof.
    intros.
    destruct p as (v1, v2).
    simpl.
    intros N.
    destruct N as [(_,[])|(_,[])].
  Qed.

  Lemma one_of_sym:
    forall p l1 l2,
    one_of p l1 l2 ->
    one_of p l2 l1.
  Proof.
    induction l1; intros. {
      apply one_of_sym_nil_l in H.
      contradiction.
    }
    destruct p as (v1, v2).
    destruct l2. {
      apply one_of_sym_nil_r in H.
      contradiction.
    }
    simpl in *.
    intuition.
  Qed.

  Lemma e_prod_sym:
    forall m1 m2,
    EEq (Prod m1 m2) (Prod m2 m1).
  Proof.
    split; simpl; intros; destruct H as [H|H]; auto;
    destruct H as [H|H]; auto.
    - apply one_of_sym in H.
      auto.
    - apply one_of_sym in H.
      auto.
  Qed.
(*
  Lemma e_plus_prod_prod_rw:
    forall m1 m2 m3 m4,
    EEq (Plus (Prod m1 m2) (Prod m3 m4))
        (Prod (Plus m1 m3) (Plus m2 m4)).
  Proof.
    intros.
    split; simpl; intros; destruct H as [[H1|H2]|[H3|H4]]; auto.
    - destruct H2; auto.
      auto using one_of_app_r_l, one_of_app_l_l.
    - destruct H4; auto.
      auto using one_of_app_r_r, one_of_app_l_r.
    - destruct H3; auto.
    - apply one_of_inv_app_l in H4.
      destruct H4 as [H|H].
      + apply one_of_inv_app_r in H.
        destruct H; auto.
        (* 
          one_of p (flatten_exp m1) (flatten_exp m4) ->
          one_of p (flatten_exp m1) (flatten_exp m2) \/
          one_of p (flatten_exp m3) (flatten_exp m4)
        *)
        (*
        right; right; right.
        left; right; right.
        *)
        admit.
      + apply one_of_inv_app_r in H.
        destruct H; auto.
        (*
          one_of p (flatten_exp m3) (flatten_exp m2) ->
          one_of p (flatten_exp m1) (flatten_exp m2) \/
          one_of p (flatten_exp m3) (flatten_exp m4)
        *)
        (*
        right; right; right.
        left; right; right.
        *)
        admit.
  Qed.
*)
  Lemma e_plus_absorb_rw:
    forall m,
    EEq (Plus m m) m.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    apply mem_equiv_app_refl_rw.
  Qed.

  Lemma to_mem_eq_rw:
    forall m1 m2,
    to_mem m1 = to_mem m2 ->
    EEq m1 m2.
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    rewrite H.
    reflexivity.
  Qed.

  Lemma e_prod_plus_absorb_rw:
    forall m1 m2,
    EEq (Plus (Prod m1 m2) m2) (Prod m1 m2).
  Proof.
    intros.
    apply e_eq_iff_m_equiv.
    simpl.
    apply app_prod_absorb_1.
    auto using to_mem_not_nil.
  Qed.

  Inductive EEqList : list mexp -> list mexp -> Prop :=
  | e_eq_list_nil:
    EEqList [] []
  | e_eq_list_cons:
    forall m1 m2 mm1 mm2,
    EEq m1 m2 ->
    EEqList mm1 mm2 ->
    EEqList (m1::mm1) (m2::mm2).

  Lemma e_eq_list_refl:
    forall m,
    EEqList m m.
  Proof.
    induction m; auto using e_eq_list_nil.
    apply e_eq_list_cons; auto.
    reflexivity.
  Qed.

  Lemma e_eq_list_trans:
    forall x y z,
    EEqList x y ->
    EEqList y z ->
    EEqList x z.
  Proof.
    intros x y.
    generalize dependent x.
    induction y; intros; inversion H; inversion H0; subst; clear H H0.
    - apply e_eq_list_nil.
    - apply e_eq_list_cons; eauto.
      etransitivity; eauto.
  Qed.

  Lemma e_eq_list_sym:
    forall x y,
    EEqList x y ->
    EEqList y x.
  Proof.
    induction x; intros; inversion H; subst; clear H. {
      apply e_eq_list_nil.
    }
    apply IHx in H4.
    symmetry in H2.
    auto using e_eq_list_cons.
  Qed.

  Global Add Parametric Relation : _ EEqList
    reflexivity proved by e_eq_list_refl
    symmetry proved by e_eq_list_sym
    transitivity proved by e_eq_list_trans
    as e_eq_list_setoid.

  Fixpoint summation (l:list mexp) :=
    match l with
    | [] => One []
    | x :: l => Plus x (summation l)
    end.

  Global Instance e_eq_list_proper_1: Proper (EEq ==> EEqList ==> EEqList) cons.
  Proof.
    unfold Proper, respectful.
    intros.
    apply e_eq_list_cons; auto.
  Qed.

  Lemma eq_list_summation_rw:
    forall x y,
    EEqList x y ->
    EEq (summation x) (summation y).
  Proof.
    induction x; intros. {
      inversion H; subst; clear H.
      reflexivity.
    }
    inversion H; subst; clear H.
    simpl.
    rewrite H2.
    rewrite IHx; eauto.
    reflexivity.
  Qed.


  Global Instance e_eq_list_proper_2: Proper (EEqList ==> EEq) summation.
  Proof.
    unfold Proper, respectful.
    intros.
    apply eq_list_summation_rw.
    assumption.
  Qed.

  Global Instance e_eq_list_proper_3: Proper (EEqList ==> EEqList ==> EEqList) (map2 Prod).
  Proof.
    unfold Proper, respectful.
    induction x; intros. {
      inversion H; subst.
      reflexivity.
    }
    inversion H; subst; clear H.
    destruct x0. {
      inversion H0; subst; clear H0.
      repeat rewrite map2_nil_r.
      apply e_eq_list_nil.
    }
    inversion H0; subst; clear H0.
    repeat rewrite map2_cons_rw.
    apply e_eq_list_cons.
    - rewrite H3; rewrite H2; reflexivity.
    - auto.
  Qed.

  Global Instance e_eq_list_proper_4: Proper (EEqList ==> EEqList ==> EEqList) (map2 Plus).
  Proof.
    unfold Proper, respectful.
    induction x; intros. {
      inversion H; subst.
      reflexivity.
    }
    inversion H; subst; clear H.
    destruct x0. {
      inversion H0; subst; clear H0.
      repeat rewrite map2_nil_r.
      apply e_eq_list_nil.
    }
    inversion H0; subst; clear H0.
    repeat rewrite map2_cons_rw.
    apply e_eq_list_cons.
    - rewrite H3; rewrite H2; reflexivity.
    - auto.
  Qed.

  Lemma e_eq_list_map_rw:
    forall (A:Type) (f g:A -> mexp),
    (forall n, EEq (f n) (g n)) ->
    forall l,
    EEqList (map f l) (map g l).
  Proof.
    induction l; intros. {
      apply e_eq_list_nil.
    }
    simpl.
    apply e_eq_list_cons; auto.
  Qed.

  Lemma e_pair_in_summation_l:
    forall p l1 l2,
    length l1 = length l2 ->
    e_pair_in p (summation l1) ->
    e_pair_in p (summation (map2 Prod l1 l2)).
  Proof.
    induction l1; intros. {
      simpl in *.
      assumption.
    }
    destruct l2. {
      inversion H.
    }
    rewrite map2_cons_rw.
    simpl.
    simpl in H0.
    destruct H0; auto.
  Qed.

  Lemma e_pair_in_summation_r:
    forall p l1 l2,
    length l1 = length l2 ->
    e_pair_in p (summation l2) ->
    e_pair_in p (summation (map2 Prod l1 l2)).
  Proof.
    induction l1; intros. {
      simpl in *.
      destruct l2; auto.
      inversion H.
    }
    destruct l2. {
      inversion H.
    }
    rewrite map2_cons_rw.
    simpl.
    simpl in H0.
    destruct H0; auto.
  Qed.

  Lemma e_summation_app:
    forall l1 l2,
    EEq (summation (l1 ++ l2)) (Plus (summation l1) (summation l2)).
  Proof.
    induction l1; intros. {
      simpl.
      rewrite e_plus_nil_l.
      reflexivity.
    }
    simpl.
    rewrite IHl1.
    rewrite e_plus_assoc.
    reflexivity.
  Qed.

(*
  Lemma prod_summation_cons_rw:
    forall la a b lb,
    EEq (Plus (Prod a b) (Prod (summation la) (summation lb)))
        (Prod (summation (a :: la)) (summation (b :: lb))).
  Proof.
    induction la; simpl; intros. {
      rewrite e_prod_nil_l.
      rewrite e_plus_nil_r.
      split; intros; simpl in *.
      - destruct H; auto.
        destruct H; auto.
        destruct H; auto.
        auto using one_of_app_r_l.
      - destruct H; auto.
        destruct H; auto. {
          destruct H; auto.
        }
        apply one_of_inv_app_r in H.
        destruct H; auto.
        
        Search (one_of _ _ (_ ++ _)).
    } 
  Qed.
*)
(*
  Lemma prod_summation_rw:
    forall l1 l2,
    length l1 = length l2 ->
    EEq (Prod (summation l1) (summation l2))
        (summation (map2 Prod l1 l2)).
  Proof.
    induction l1; intros. {
      destruct l2. {
        simpl.
        rewrite e_prod_nil_l.
        reflexivity.
      }
      inversion H.
    }
    destruct l2. { inversion H. }
    inversion H; subst; clear H.
    assert (Hl := H1).
    apply IHl1 in H1.
    rewrite map2_cons_rw.
    simpl.
    rewrite <- IHl1.
    - rewrite H1.
      split; intros.
      + simpl in *.
        destruct H; auto. {
          destruct H; auto.
          auto using e_pair_in_summation_l.
        }
        destruct H as [[]|?]; auto using e_pair_in_summation_r.
        apply one_of_inv_app_l in H.
        destruct H as [H|H]; apply one_of_inv_app_r in H; destruct H as [H|H]; auto.
        Search (one_of _ (_ ++ _)).
  Qed.*)
End Defs.

Module MHistNotations.
  Infix "==" :=  EEq (at level 60, right associativity).
  Infix "+" := Plus (at level 50, left associativity).
  Infix "*" := Prod (at level 40, left associativity).
  Notation "'Σ'" := summation.
End MHistNotations.
