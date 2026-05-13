
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Sets.Constructive_sets.
Require Import Aniceto.Graphs.Graph.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lists.List.
From Faial.Approx Require Import Util.
From Stdlib Require Sorting.SetoidList.
Import ListNotations.

Module SetEq.
  Definition t {A:Type} (l1 l2:list A) : Prop :=
    forall a, List.In a l1 <-> List.In a l2.
  Lemma cons:
    forall {A:Type} (x:A) l1 l2,
    t l1 l2 ->
    t (x :: l1) (x :: l2).
  Proof.
    unfold t.
    intros.
    simpl.
    rewrite H.
    reflexivity.
  Qed.
End SetEq.

Module SetEqA.
  Definition t {A:Type} (eqA: A -> A -> Prop) (l1 l2:list A) : Prop :=
    forall a, SetoidList.InA eqA a l1 <-> SetoidList.InA eqA a l2.
End SetEqA.

Section Defs.
  
  Definition AllIncl {A:Type} (ls:list (list A)) (l:list A) :=
    List.Forall (fun (l':list A) => incl l' l) ls.

  Inductive MIn {A:Type} (a:A) ls : Prop :=
  | m_in_def:
    forall l,
    List.In l ls ->
    List.In a l ->
    MIn a ls.

  Definition AllInclAll {A:Type} (ls1 ls2:list (list A)) :=
    forall x,
      MIn x ls1 -> MIn x ls2.

  Lemma all_incl_all_def:
    forall A ls1 ls2,
    (forall (x:A), MIn x ls1 -> MIn x ls2) ->
    AllInclAll ls1 ls2.
  Proof.
    auto.
  Qed.

  (** Every element of l is in some list of ls *)
  Definition InclAll {A:Type} (l:list A) (ls:list (list A)) :=
    Included A (fun (a:A) => List.In a l) (fun a => MIn a ls).

  (** XXX: MOVE TO ANICETO *)
  Lemma incl_app_r:
    forall A (l1:list A) l2 l3,
    incl (l1 ++ l2) l3 ->
    incl l2 l3.
  Proof.
    unfold incl; intros.
    apply H.
    apply in_app_iff.
    auto.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma incl_app_l:
    forall A (l1:list A) l2 l3,
    incl (l1 ++ l2) l3 ->
    incl l1 l3.
  Proof.
    unfold incl; intros.
    apply H.
    apply in_app_iff.
    auto.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma incl_app_ll:
    forall A l3 l1 l2,
    @incl A l1 l2 ->
    incl (l3 ++ l1) (l3 ++ l2).
  Proof.
    unfold incl; intros.
    apply in_app_iff.
    apply in_app_iff in H0.
    intuition.
  Qed.

  Lemma all_incl_inv_prepend_1:
    forall A (l1 l2:list A) ls,
    AllIncl (prepend l1 ls) l2 ->
    AllIncl ls l2.
  Proof.
    unfold AllIncl; intros.
    rewrite List.Forall_forall in *.
    intros.
    eauto using in_prepend, incl_app_r.
  Qed.

  Lemma incl_all_nil:
    forall A ls,
    @InclAll A [] ls.
  Proof.
    unfold InclAll; intros.
    unfold Included.
    intros.
    contradiction.
  Qed.

  Lemma incl_all_app:
    forall A l1 l2 ls,
    InclAll l1 ls ->
    InclAll l2 ls ->
    @InclAll A (l1 ++ l2) ls.
  Proof.
    unfold InclAll, Included, Ensembles.In; intros.
    apply in_app_iff in H1.
    destruct H1; auto.
  Qed.

  Lemma m_in_eq:
    forall A (x:A) l ls, 
    List.In x l ->
    MIn x (l::ls).
  Proof.
    eauto using m_in_def, in_eq.
  Qed.

  Lemma incl_all_prepend_l:
    forall A l ls,
    ls <> [] ->
    @InclAll A l (prepend l ls).
  Proof.
    unfold InclAll, Included, Ensembles.In. intros.
    destruct ls. {
      contradiction.
    }
    simpl.
    apply m_in_eq.
    apply in_app_iff.
    auto.
  Qed.

  Lemma m_in_prepend:
    forall A (x:A) l ls,
    MIn x ls ->
    MIn x (prepend l ls).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply m_in_def; eauto using in_prepend.
    apply in_app_iff.
    auto.
  Qed.

  Lemma m_in_prepend_inv:
    forall A (x:A) l ls,
    MIn x (prepend l ls) ->
    List.In x l \/ MIn x ls.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply in_prepend_inv in H0.
    destruct H0 as (l3, (?, Hi)).
    subst.
    apply in_app_iff in H1.
    destruct H1; eauto using m_in_def.
  Qed.

  Lemma m_in_cons:
    forall A (x:A) l ll,
    MIn x ll ->
    MIn x (l::ll).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using m_in_def, in_cons.
  Qed.

  Lemma in_concat_to_m_in:
    forall A (x:A) ll,
    List.In x (List.concat ll) ->
    MIn x ll.
  Proof.
    induction ll; intros. {
      inversion H.
    }
    simpl in *.
    apply in_app_iff in H.
    destruct H.
    - auto using m_in_eq.
    - auto using m_in_cons.
  Qed.

  Lemma incl_all_prepend_r:
    forall A l1 l2 ls,
    @InclAll A l1 ls ->
    InclAll l1 (prepend l2 ls).
  Proof.
    unfold InclAll, Included, Ensembles.In. intros.
    auto using m_in_prepend.
  Qed.

  Lemma all_incl_nil:
    forall A h,
    @AllIncl A [] h.
  Proof.
    unfold AllIncl; intros.
    apply List.Forall_nil.
  Qed.

  Lemma all_incl_inv_cons:
    forall A (l1:list A) ls1 l2,
    AllIncl (l1 :: ls1) l2 ->
    incl l1 l2 /\ AllIncl ls1 l2.
  Proof.
    unfold AllIncl; intros.
    inversion H; subst; clear H.
    intuition.
  Qed.

  Lemma all_incl_cons:
    forall A l1 ls1 l2,
    incl l1 l2 ->
    @AllIncl A ls1 l2 ->
    AllIncl (l1 :: ls1) l2.
  Proof.
    unfold AllIncl; intros.
    apply List.Forall_cons; auto.
  Qed.

  Lemma all_incl_nil_nil:
    forall A,
    @AllIncl A [[]] [].
  Proof.
    intros.
    apply all_incl_cons; auto using all_incl_nil, List.incl_nil_nil.
  Qed.

  Lemma all_incl_appr:
    forall A l ll1 ll2,
    @AllIncl A l ll2 -> AllIncl l (ll1 ++ ll2).
  Proof.
    unfold AllIncl.
    intros.
    rewrite Forall_forall in *.
    intros.
    apply incl_appr.
    auto.
  Qed.

  Lemma m_in_incl:
    forall A l1 l2 (x:A),
    incl l1 l2 ->
    MIn x l1 ->
    MIn x l2.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply m_in_def with (l:=l); auto.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma incl_app_refl_r:
    forall A l1 l2,
    @incl A l2 (l1 ++ l2).
  Proof.
    unfold incl; intros.
    apply in_app_iff.
    auto.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma incl_app_refl_l:
    forall A l1 l2,
    @incl A l1 (l1 ++ l2).
  Proof.
    unfold incl; intros.
    apply in_app_iff.
    auto.
  Qed.

  Lemma all_incl_all_refl_app_r:
    forall A ls1 ls2,
    @AllInclAll A ls2 (ls1 ++ ls2).
  Proof.
    unfold AllInclAll.
    intros.
    unfold Included in *.
    unfold Ensembles.In; intros.
    apply m_in_incl with (l1:=ls2); auto.
    auto using incl_app_refl_r.
  Qed.

  Lemma all_incl_all_refl_app_l:
    forall A ls1 ls2,
    @AllInclAll A ls1 (ls1 ++ ls2).
  Proof.
    unfold AllInclAll.
    intros.
    unfold Included in *.
    unfold Ensembles.In; intros.
    apply m_in_incl with (l1:=ls1); auto.
    auto using incl_app_refl_l.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma included_trans:
    forall A P Q R,
    Included A P Q ->
    Included A Q R ->
    Included A P R.
  Proof.
    unfold Included; intros.
    apply H in H1.
    apply H0 in H1.
    assumption.
  Qed.

  Lemma all_incl_all_trans:
    forall A ls1 ls2 ls3,
    @AllInclAll A ls1 ls2 ->
    AllInclAll ls2 ls3 ->
    AllInclAll ls1 ls3.
  Proof.
    unfold AllInclAll.
    eauto using included_trans.
  Qed.

  (** XXX: MOVE TO ANICETO *)
  Lemma included_refl:
    forall A P,
    Included A P P.
  Proof.
    intros.
    unfold Included.
    intros.
    assumption.
  Qed.

  Lemma all_incl_all_refl:
    forall A ls,
    @AllInclAll A ls ls.
  Proof.
    intros.
    unfold AllInclAll.
    apply included_refl.
  Qed.

  Lemma all_incl_all_app_r:
    forall A ls1 ls2 ls3,
    @AllInclAll A ls1 ls3 ->
    AllInclAll ls1 (ls2 ++ ls3).
  Proof.
    intros.
    apply all_incl_all_trans with (ls2:=ls3); auto.
    auto using all_incl_all_refl_app_r.
  Qed.

  Lemma all_incl_all_app_l:
    forall A ls1 ls2 ls3,
    @AllInclAll A ls1 ls2 ->
    AllInclAll ls1 (ls2 ++ ls3).
  Proof.
    intros.
    apply all_incl_all_trans with (ls2:=ls2); auto.
    auto using all_incl_all_refl_app_l.
  Qed.

  Lemma all_incl_app:
    forall A l1 l2 ls,
    AllIncl l1 ls ->
    AllIncl l2 ls ->
    @AllIncl A (l1 ++ l2) ls.
  Proof.
    unfold AllIncl. intros.
    rewrite Forall_forall in *.
    intros.
    apply in_app_iff in H1.
    destruct H1; auto.
  Qed.

  Lemma all_incl_appl:
    forall A l ls1 ls2,
    @AllIncl A l ls1 -> AllIncl l (ls1 ++ ls2).
  Proof.
    unfold AllIncl.
    intros.
    rewrite Forall_forall in *.
    intros.
    apply incl_appl.
    auto.
  Qed.

  Lemma m_in_app_l:
    forall A (x:A) ls1 ls2,
    MIn x ls1 ->
    MIn x (ls1 ++ ls2).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply m_in_def; eauto.
    apply in_app_iff.
    auto.
  Qed.

  Lemma m_in_app_r:
    forall A (x:A) ls1 ls2,
    MIn x ls2 ->
    MIn x (ls1 ++ ls2).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply m_in_def; eauto.
    apply in_app_iff.
    auto.
  Qed.

  Lemma m_in_inv_app:
    forall A (x:A) ls1 ls2,
    MIn x (ls1 ++ ls2) ->
    MIn x ls1 \/ MIn x ls2.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply in_app_iff in H0.
    destruct H0; eauto using m_in_def.
  Qed.

  Lemma incl_all_app_l:
    forall A l ls1 ls2,
    @InclAll A l ls1 ->
    InclAll l (ls1 ++ ls2).
  Proof.
    unfold InclAll, Included, Ensembles.In.
    intros.
    apply H in H0.
    auto using m_in_app_l.
  Qed.

  Lemma incl_all_app_r:
    forall A l ls1 ls2,
    @InclAll A l ls2 ->
    InclAll l (ls1 ++ ls2).
  Proof.
    unfold InclAll, Included, Ensembles.In.
    intros.
    apply H in H0.
    auto using m_in_app_r.
  Qed.

  Lemma all_incl_prepend:
    forall A ls1 (l1:list A) l2,
    AllIncl ls1 l2 ->
    AllIncl (prepend l1 ls1) (l1 ++ l2).
  Proof.
    induction ls1; intros. {
      simpl.
      auto using all_incl_nil.
    }
    simpl.
    apply all_incl_inv_cons in H.
    destruct H as (Hi, Hp).
    apply all_incl_cons; auto using incl_app_ll.
  Qed.

  Lemma all_incl_to_incl:
    forall A ls (l1 l2: list A),
    @AllIncl A ls l2 ->
    List.In l1 ls ->
    incl l1 l2.
  Proof.
    unfold AllIncl.
    intros.
    rewrite List.Forall_forall in H.
    apply H in H0.
    assumption.
  Qed.

  Lemma all_incl_prod:
    forall A l1 l2 ls,
    AllIncl l1 ls ->
    AllIncl l2 ls ->
    @AllIncl A (prod l1 l2) ls.
  Proof.
    unfold AllIncl. intros.
    rewrite Forall_forall in *.
    intros.
    apply in_prod_inv in H1.
    destruct H1 as (a, (Hi, Hj)).
    apply in_prepend_inv in Hj.
    destruct Hj as (y, (?, Hj)).
    subst.
    apply incl_app; auto.
  Qed.

  Lemma all_incl_all_m_in:
    forall A ls1 ls2,
    @AllInclAll A ls1 ls2 ->
    forall a,
    MIn a ls1 ->
    MIn a ls2.
  Proof.
    unfold AllInclAll; intros.
    apply H in H0.
    assumption.
  Qed.

  Lemma all_incl_all_incl_all:
    forall A ls1 ls2,
    @AllInclAll A ls1 ls2 ->
    forall l,
    AllIncl ls2 l ->
    AllIncl ls1 l.
  Proof.
    unfold AllIncl; intros.
    rewrite Forall_forall in *.
    intros.
    unfold incl; intros.
    assert (MIn a ls1) by eauto using m_in_def.
    assert (Hi: MIn a ls2) by eauto using all_incl_all_m_in.
    inversion Hi; subst; clear Hi.
    assert (incl l0 l) by eauto.
    auto.
  Qed.

  Lemma m_in_prod_r:
    forall A (x:A) ls1 ls2,
    ls1 <> [] ->
    MIn x ls2 ->
    MIn x (prod ls1 ls2).
  Proof.
    induction ls1; intros. {
      contradiction.
    }
    clear H.
    destruct ls1. {
      simpl.
      rewrite app_nil_r.
      auto using m_in_prepend.
    }
    apply IHls1 in H0.
    + simpl in *.
      auto using m_in_app_r.
    + intros N.
      inversion N.
  Qed.

  Lemma m_in_inv:
    forall A (x:A) l ls,
    MIn x (l :: ls) ->
    List.In x l \/ MIn x ls.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      auto.
    }
    eauto using m_in_def.
  Qed.

  Lemma m_in_inv_cons_nil:
    forall A (x:A) (l:list A),
    MIn x [l] ->
    List.In x l.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      assumption.
    }
    inversion H.
  Qed.

  Lemma m_in_nil:
    forall A (x:A), 
    ~ MIn x [].
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    contradiction.
  Qed.

  Lemma m_in_nil_nil:
    forall A (x:A), 
    ~ MIn x [[]].
  Proof.
    intros.
    intros N.
    apply m_in_inv_cons_nil in N.
    inversion N.
  Qed.

  Lemma m_in_to_in_concat:
    forall A (x:A) ll,
    MIn x ll ->
    List.In x (List.concat ll).
  Proof.
    induction ll; intros. {
      apply m_in_nil in H.
      contradiction.
    }
    apply m_in_inv in H.
    simpl.
    apply in_app_iff.
    destruct H; auto.
  Qed.

  Lemma m_in_concat_rw:
    forall A (x:A) ll,
    MIn x ll <-> List.In x (List.concat ll).
  Proof.
    split; intros; auto using m_in_to_in_concat, in_concat_to_m_in.
  Qed.


  Lemma m_in_concat:
    forall A x ls l,
    MIn x l ->
    List.In l ls ->
    @MIn A x (List.concat ls).
  Proof.
    induction ls; intros. {
      contradiction.
    }
    destruct H0. {
      subst.
      simpl.
      auto using m_in_app_l.
    }
    simpl.
    apply m_in_app_r.
    eauto.
  Qed.

  Lemma m_in_prepend_l:
    forall A (x:A) l ls,
    ls <> [] ->
    List.In x l ->
    MIn x (prepend l ls).
  Proof.
    intros.
    destruct ls. {
      contradiction.
    }
    simpl.
    apply m_in_eq.
    apply in_app_iff.
    auto.
  Qed.

  Lemma m_in_prepend_r:
    forall A (x:A) ls l,
    MIn x ls ->
    MIn x (prepend l ls).
  Proof.
    induction ls; unfold prepend; intros; simpl. {
      assumption.
    }
    simpl.
    apply m_in_inv in H.
    destruct H. {
      apply m_in_eq.
      rewrite in_app_iff.
      auto.
    }
    eauto using m_in_cons.
  Qed.

  Lemma m_in_prod_l:
    forall A (x:A) ls1 ls2,
    ls2 <> [] ->
    MIn x ls1 ->
    MIn x (prod ls1 ls2).
  Proof.
    induction ls1; intros. {
      apply m_in_nil in H0.
      contradiction.
    }
    apply m_in_inv in H0.
    simpl.
    destruct H0. {
      auto using m_in_app_l, m_in_prepend_l.
    }
    apply m_in_app_r.
    auto.
  Qed.

  Lemma incl_all_prod_l:
    forall A l ls1 ls2,
    ls2 <> [] ->
    @InclAll A l ls1 ->
    InclAll l (prod ls1 ls2).
  Proof.
    unfold InclAll, Included, Ensembles.In.
    auto using m_in_prod_l.
  Qed.

  Lemma incl_all_prod_r:
    forall A l ls1 ls2,
    ls1 <> [] ->
    @InclAll A l ls2 ->
    InclAll l (prod ls1 ls2).
  Proof.
    unfold InclAll, Included, Ensembles.In.
    auto using m_in_prod_r.
  Qed.

  Lemma m_in_prod_inv:
    forall {A} (x:A) ls1 ls2,
    MIn x (prod ls1 ls2) ->
    MIn x ls1 \/ MIn x ls2.
  Proof.
    intros.
    inversion H in H; subst; clear H.
    apply in_prod_inv in H0.
    destruct H0 as (a, (Hi, Hj)).
    apply in_prepend_inv in Hj.
    destruct Hj as (b, (?, Hj)).
    subst.
    apply in_app_iff in H1.
    destruct H1; eauto using m_in_def.
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


End Defs.

