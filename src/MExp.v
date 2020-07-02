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

  Fixpoint EIn x (e:mexp) :=
    match e with
    | One h => List.In x h
    | Prod e1 e2
    | Plus e1 e2 => EIn x e1 \/ EIn x e2
    end.

  Fixpoint one_of (p:access_val*access_val) e1 e2 :=
    let (v1, v2) := p in
    (EIn v1 e1 /\ EIn v2 e2)
    \/
    (EIn v2 e1 /\ EIn v1 e2).

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
    one_of p e1 e2
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

  Lemma e_in_1:
    forall e x,
    EIn x e ->
    MIn x (to_mem e).
  Proof.
    induction e; simpl; intros x Hi.
    - auto using m_in_eq.
    - destruct Hi. {
        apply IHe1 in H; auto.
        apply m_in_prod_l; eauto using to_mem_not_nil.
      }
      apply IHe2 in H; auto.
      apply m_in_prod_r; eauto using to_mem_not_nil.
    - destruct Hi. {
        apply IHe1 in H; auto.
        apply m_in_app_l; eauto using to_mem_not_nil.
      }
      apply IHe2 in H; auto.
      apply m_in_app_r; eauto using to_mem_not_nil.
  Qed.

  Lemma e_in_2:
    forall v e,
    MIn v (to_mem e) ->
    EIn v e.
  Proof.
    induction e; simpl; intros.
    - inversion H; subst; clear H.
      inversion H0; subst; clear H0; try contradiction.
      assumption.
    - apply m_in_prod_inv in H.
      destruct H as [Hx|Hx]; auto.
    - apply m_in_inv_app in H.
      destruct H; auto.
  Qed.

  Lemma e_in_iff:
    forall x e,
    MIn x (to_mem e) <-> EIn x e.
  Proof.
    split; auto using e_in_1, e_in_2.
  Qed.

  Lemma on_of_1:
    forall e1 e2 x y,
    one_of (x,y) e1 e2 ->
    (MIn x (to_mem e1) /\ MIn y (to_mem e2))
    \/
    (MIn x (to_mem e2) /\ MIn y (to_mem e1)).
  Proof.
    intros.
    simpl in H.
    destruct H as [(Ha,Hb)|(Ha,Hb)]; auto using e_in_1.
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
      + apply e_in_2 in Ha; auto.
        apply e_in_2 in Hb; auto.
      + apply e_in_2 in Ha; auto.
        apply e_in_2 in Hb; auto.
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

  Lemma e_in_to_e_pair_in:
    forall x m,
    EIn x m ->
    e_pair_in (x, x) m.
  Proof.
    induction m; simpl; intros.
    - auto using pair_in_refl.
    - destruct H; auto.
    - destruct H; auto.
  Qed.

  Lemma e_pair_in_to_e_in_l:
    forall x y m,
    e_pair_in (x, y) m ->
    EIn x m.
  Proof.
    induction m; simpl; intros.
    - apply pair_in_to_in_l in H.
      auto using m_in_eq.
    - destruct H; auto.
      destruct H; auto.
      destruct H as [(?,?)|(?,?)]; auto.
    - destruct H; auto.
  Qed.

  Lemma e_pair_in_to_e_in_r:
    forall x y m,
    e_pair_in (x, y) m ->
    EIn y m.
  Proof.
    induction m; simpl; intros.
    - eauto using pair_in_to_in_r.
    - destruct H; auto.
      destruct H; auto.
      destruct H as [(?,?)|(?,?)]; auto.
    - destruct H; auto.
  Qed.

  Lemma e_pair_in_to_m_in_list:
    forall x y m,
    e_pair_in (x, y) m ->
    EIn x m /\
    EIn y m.
  Proof.
    intros.
    assert (Hx := H).
    apply e_pair_in_to_e_in_r in H.
    apply e_pair_in_to_e_in_l in Hx.
    auto.
  Qed.

  Lemma e_in_rw_eq:
    forall m1 m2,
    EEq m1 m2 ->
    forall x,
    EIn x m1 ->
    EIn x m2.
  Proof.
    intros.
    apply e_in_to_e_pair_in in H0.
    apply H in H0.
    eauto using e_pair_in_to_e_in_l.
  Qed.

  Global Instance m_in_proper_1: Proper (eq ==> EEq ==> iff) EIn.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros.
    - eauto using e_in_rw_eq.
    - symmetry in H0.
      eauto using e_in_rw_eq.
  Qed.

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

  Lemma e_prod_plus_r:
    forall e1 e2 e3,
    EEq (Plus (Prod e1 e2) (Prod e1 e3)) (Prod e1 (Plus e2 e3)).
  Proof.
    split; intros.
    - (* Because this is computational, p is the only thing that
         is making evaluation stuck. Destruct it and evaluate it. *)
      destruct p as (x, y); simpl in *.
      (* If this is provable, then intuition can handle it. *)
      intuition.
    - destruct p as (x, y); simpl in *.
      intuition.
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

  Lemma one_of_sym:
    forall p m1 m2,
    one_of p m1 m2 ->
    one_of p m2 m1.
  Proof.
    destruct p as (x, y).
    induction m1; intros; simpl in *; intuition.
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

  Fixpoint summation (l:list mexp) :=
    match l with
    | [] => One []
    | x :: l => Plus x (summation l)
    end.

  Lemma e_in_nil:
    forall x,
    ~ EIn x (One []).
  Proof.
    unfold EIn.
    intros.
    simpl.
    intros N.
    assumption.
  Qed.

  Lemma e_in_summation_map2_prod_or:
    forall x l1 l2,
    EIn x (summation (map2 Prod l1 l2)) ->
    EIn x (summation l1) \/ EIn x (summation l2).
  Proof.
    induction l1; intros. {
      rewrite map2_nil_l in *.
      auto.
    }
    destruct l2. {
      rewrite map2_nil_r in *.
      simpl in *.
      auto.
    }
    rewrite map2_cons_rw in *.
    simpl in *.
    (* Let intuition clear out the easy bits. *)
    intuition.
    apply IHl1 in H0.
    intuition.
  Qed.

  Lemma e_in_summation_map2_prod_or_rev:
    forall x l1 l2,
    length l1 = length l2 ->
    EIn x (summation l1) \/ EIn x (summation l2) ->
    EIn x (summation (map2 Prod l1 l2)).
  Proof.
    induction l1; intros. {
      destruct l2. {
        intuition.
      }
      inversion H.
    }
    destruct l2. { inversion H. }
    inversion H; subst; clear H.
    simpl in *.
    assert (Hx: (EIn x (summation l1) \/ EIn x (summation l2)) \/ (EIn x a \/ EIn x m)). {
      intuition.
    }
    clear H0.
    destruct Hx as [Hx|Hx]. { eauto. }
    auto.
  Qed.

  Lemma e_in_rw_summation_map2_prod:
    forall x l1 l2,
    length l1 = length l2 ->
    EIn x (summation l1) \/ EIn x (summation l2) <->
    EIn x (summation (map2 Prod l1 l2)).
  Proof.
    intros.
    split; auto using e_in_summation_map2_prod_or, e_in_summation_map2_prod_or_rev.
  Qed.

  Lemma e_in_summation_map2_plus_or:
    forall x l1 l2,
    EIn x (summation (map2 Plus l1 l2)) ->
    EIn x (summation l1) \/ EIn x (summation l2).
  Proof.
    induction l1; intros. {
      rewrite map2_nil_l in *.
      auto.
    }
    destruct l2. {
      rewrite map2_nil_r in *.
      simpl in *.
      auto.
    }
    rewrite map2_cons_rw in *.
    simpl in *.
    (* Let intuition clear out the easy bits. *)
    intuition.
    apply IHl1 in H0.
    intuition.
  Qed.

  Lemma e_in_summation_map2_plus_or_rev:
    forall x l1 l2,
    length l1 = length l2 ->
    EIn x (summation l1) \/ EIn x (summation l2) ->
    EIn x (summation (map2 Plus l1 l2)).
  Proof.
    induction l1; intros. {
      destruct l2. {
        intuition.
      }
      inversion H.
    }
    destruct l2. { inversion H. }
    inversion H; subst; clear H.
    simpl in *.
    assert (Hx: (EIn x (summation l1) \/ EIn x (summation l2)) \/ (EIn x a \/ EIn x m)). {
      intuition.
    }
    clear H0.
    destruct Hx as [Hx|Hx]. { eauto. }
    auto.
  Qed.

  Lemma e_in_rw_summation_map2_plus:
    forall x l1 l2,
    length l1 = length l2 ->
    EIn x (summation l1) \/ EIn x (summation l2) <->
    EIn x (summation (map2 Plus l1 l2)).
  Proof.
    intros.
    split; auto using e_in_summation_map2_plus_or, e_in_summation_map2_plus_or_rev.
  Qed.

  (* ------------------- EEqList ----------------------------- *)

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

  Lemma e_eq_list_map2_prod_sym:
    forall l1 l2,
    EEqList (map2 Prod l1 l2) (map2 Prod l2 l1).
  Proof.
    induction l1; intros. {
      rewrite map2_nil_l.
      rewrite map2_nil_r.
      apply e_eq_list_nil.
    }
    destruct l2. {
      rewrite map2_nil_l.
      rewrite map2_nil_r.
      apply e_eq_list_nil.
    }
    rewrite map2_cons_rw.
    rewrite map2_cons_rw.
    rewrite IHl1.
    rewrite e_prod_sym.
    reflexivity.
  Qed.

  Lemma e_eq_list_inv_length_l:
    forall A B f l1 l2 l, 
    length l1 = length l2 ->
    EEqList l (@map2 A B _ f l1 l2) ->
    length l = length l1.
  Proof.
    induction l1; intros. {
      destruct l2. {
        rewrite map2_nil_l in *.
        inversion H0; subst; reflexivity.
      }
      inversion H.
    }
    destruct l2. { inversion H. }
    rewrite map2_cons_rw in *.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    apply IHl1 in H5; auto.
    simpl.
    rewrite H5.
    reflexivity.
  Qed.

  Lemma e_eq_list_inv_length_r:
    forall A B f l1 l2 l, 
    length l1 = length l2 ->
    EEqList l (@map2 A B _ f l1 l2) ->
    length l = length l2.
  Proof.
    induction l1; intros. {
      destruct l2. {
        rewrite map2_nil_l in *.
        inversion H0; subst; reflexivity.
      }
      inversion H.
    }
    destruct l2. { inversion H. }
    rewrite map2_cons_rw in *.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    apply IHl1 in H5; auto.
    simpl.
    rewrite H5.
    reflexivity.
  Qed.

  Lemma e_in_inv_summation:
    forall x l,
    EIn x (summation l) ->
    exists m, List.In m l /\ EIn x m.
  Proof.
    induction l; intros. { simpl in *. contradiction. }
    destruct H. { eauto using in_eq. }
    apply IHl in H.
    destruct H as (m, (Hi, He)).
    eauto using in_cons.
  Qed.
End Defs.

Module MHistNotations.
  Infix "==" :=  EEq (at level 70, right associativity).
  Infix "+" := Plus (at level 50, left associativity).
  Infix "*" := Prod (at level 40, left associativity).
  Notation "'Σ'" := summation.
End MHistNotations.
