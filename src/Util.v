Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Sets.Ensembles.
Require Coq.Sets.Constructive_sets.

Require Import Aniceto.Graphs.Graph.

Import ListNotations.
Section Ops.
  Fixpoint count n :=
  match n with
  | 0 => []
  | S n => n :: count n
  end.

  (** Prepends every element of a list with a prefix *)

  Definition prepend {A:Type} (l1:list A) (l2: list (list A)) : list (list A) :=
    List.fold_right (fun x accum => (l1 ++ x) :: accum) [] l2.  

  (** Product of two lists. That is for each two elements x,y of lists l1 l2, yields
      x ++ y *)

  Definition prod {A:Type} (l1: list (list A)) (l2: list (list A)) : list (list A) :=
    List.fold_right (fun x accum => prepend x l2 ++ accum) [] l1. 

  Definition AllIncl {A:Type} (ls:list (list A)) (l:list A) :=
    List.Forall (fun (l':list A) => incl l' l) ls.

  (* A pair of elements is in the list. *) 
  Inductive PairIn {A:Type}: (A * A) -> list A -> Prop :=
  | pair_in_def:
    forall x y l,
    List.In x l ->
    List.In y l ->
    PairIn (x, y) l.

  (* A pair of elements is in a sub-list *)
  Definition MPairIn {A:Type} (p:A*A) := Exists (fun l => PairIn p l).

  (* Every pair in l must also be in a list of ls *)
  Definition PairIncl {A:Type} l ls :=
    Included (A*A) (fun p => PairIn p l) (fun p => MPairIn p ls).

  Inductive MIn {A:Type} (a:A) ls : Prop :=
  | m_in_def:
    forall l,
    List.In l ls ->
    List.In a l ->
    MIn a ls.

  (* Every pair in l must also be in a list of ls *)
  Definition MPairIncl {A:Type} ls1 ls2 :=
    forall x y,
      MIn x ls1 ->
      MIn y ls1 ->
      @MPairIn A (x, y) ls2.

  Definition AllInclAll {A:Type} (ls1 ls2:list (list A)) :=
    Included A (fun a => MIn a ls1) (fun a => MIn a ls2).

  (** Every element of l is in some list of ls *)
  Definition InclAll {A:Type} (l:list A) (ls:list (list A)) :=
    Included A (fun (a:A) => List.In a l) (fun a => MIn a ls).

  Lemma in_prepend:
    forall A ls (l1 l2:list A),
    List.In l2 ls ->
    List.In (l1 ++ l2) (prepend l1 ls).
  Proof.
    induction ls; intros. {
      contradiction.
    }
    inversion H; subst; clear H. {
      simpl.
      auto.
    }
    apply IHls with (l1:=l1) in H0; eauto.
    simpl.
    auto.
  Qed.

  Lemma in_prepend_inv:
    forall A ls l1 l2,
    List.In l1 (@prepend A l2 ls) ->
    exists l3, l1 = l2 ++ l3 /\ List.In l3 ls.
  Proof.
    induction ls; intros. {
      simpl in *.
      contradiction.
    }
    inversion H; subst; clear H. {
      eauto using in_eq.
    }
    apply IHls in H0.
    destruct H0 as (?, (?, Hi)).
    eauto using in_cons.
  Qed.

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
    apply m_in_def with (l0:=l); auto.
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

  Lemma pair_incl_in:
    forall A l ll p,
    @PairIncl A l ll ->
    PairIn p l ->
    MPairIn p ll.
  Proof.
    unfold PairIncl; intros.
    apply H in H0.
    assumption.
  Qed.

  Lemma prepend_app:
    forall {A} (l:list A) ll1 ll2,
    prepend l (ll1 ++ ll2) = prepend l ll1 ++ prepend l ll2.
  Proof.
    induction ll1; intros; simpl. {
      reflexivity.
    }
    rewrite IHll1.
    reflexivity.
  Qed.

  Lemma prod_nil_nil_r:
    forall A ll, 
    @prod A ll [[]] = ll.
  Proof.
    induction ll. {
      reflexivity.
    }
    simpl.
    rewrite IHll.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma prod_app:
    forall A ll1 ll2 ll3, 
    @prod A ll1 ll3 ++ prod ll2 ll3 = prod (ll1 ++ ll2) ll3.
  Proof.
    induction ll1; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    rewrite <- IHll1.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma prepend_assoc:
    forall A ll l1 l2,
    @prepend A l1 (prepend l2 ll) = prepend (l1 ++ l2) ll.
  Proof.
    induction ll; intros; simpl. {
      reflexivity.
    }
    rewrite IHll.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma prepend_prod:
    forall {A:Type} (l:list A) ll1 ll2,
    prepend l (prod ll1 ll2) = prod (prepend l ll1) ll2.
  Proof.
    induction ll1; intros; simpl. {
      reflexivity.
    }
    rewrite prepend_app.
    rewrite IHll1.
    rewrite prepend_assoc.
    reflexivity.
  Qed.

  Lemma prepend_nil:
    forall A l,
    @prepend A [] l = l.
  Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite IHl.
      reflexivity.
  Qed.
(*
  Lemma in_prepend_inv:
    forall A x l ls,
    List.In x (@prepend A l ls) ->
    exists y, l ++ y = x /\ List.In y ls.
  Proof.
    induction ls; unfold prepend; simpl; intros. {
      contradiction.
    }
    destruct H. {
      eauto.
    }
    apply IHls in H.
    destruct H as (?, (?, ?)).
    subst.
    eauto.
  Qed.
*)
  Lemma in_prod_inv:
    forall A x ls1 ls2,
    List.In x (@prod A ls1 ls2) ->
    exists a, List.In a ls1 /\ List.In x (prepend a ls2).
  Proof.
    unfold prod; induction ls1; simpl; intros. {
      contradiction.
    }
    apply in_app_iff in H.
    destruct H. {
      exists a.
      intuition.
    }
    apply IHls1 in H.
    destruct H as (b, (Hi, Hj)).
    exists b.
    intuition.
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

  Lemma par_not_in_nil:
    forall A p,
    ~ @PairIn A p [].
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    contradiction.
  Qed.

  Lemma pair_incl_nil_l:
    forall A ls,
    @PairIncl A [] ls.
  Proof.
    unfold PairIncl.
    intros.
    unfold Included.
    intros.
    unfold Ensembles.In in *.
    apply par_not_in_nil in H.
    contradiction.
  Qed.

  Lemma pair_in_app_l:
    forall A p l1 l2,
    @PairIn A p l1 ->
    PairIn p (l1 ++ l2).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply pair_in_def; apply in_app_iff; intuition.
  Qed.

  Lemma pair_in_app_r:
    forall A p l1 l2,
    @PairIn A p l2 ->
    PairIn p (l1 ++ l2).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply pair_in_def; apply in_app_iff; intuition.
  Qed.

  Lemma pair_in_prepend_1:
    forall A p l ls,
    ls <> [] ->
    @PairIn A p l ->
    MPairIn p (prepend l ls).
  Proof.
    intros.
    apply Exists_exists.
    destruct ls as [|l1]. {
      contradiction.
    }
    simpl.
    exists (l++l1).
    intuition.
    auto using pair_in_app_l.
  Qed.

  Lemma pair_in_prepend_2:
    forall A (x:A) y l ls,
    MIn x ls ->
    List.In y l ->
    MPairIn (x, y) (prepend l ls).
  Proof.
    intros.
    apply Exists_exists.
    inversion H; subst; clear H.
    exists (l ++ l0).
    split.
    - auto using in_prepend.
    - apply pair_in_def; apply in_app_iff; intuition.
  Qed.

  Lemma pair_in_prepend_3:
    forall A (x:A) y l ls,
    List.In x l ->
    MIn y ls ->
    MPairIn (x, y) (prepend l ls).
  Proof.
    intros.
    apply Exists_exists.
    inversion H0; subst; clear H0.
    exists (l ++ l0).
    split.
    - auto using in_prepend.
    - apply pair_in_def; apply in_app_iff; intuition.
  Qed.

  Lemma pair_in_prepend_4:
    forall A p ls l,
    @MPairIn A p ls ->
    MPairIn p (prepend l ls).
  Proof.
    intros.
    apply Exists_exists in H.
    destruct H as (l1, (Hi, Hj)).
    apply Exists_exists.
    exists (l++l1).
    split; auto using in_prepend, pair_in_app_r.
  Qed.

  Lemma pair_in_to_in_l:
    forall A (x:A) y l,
    PairIn (x, y) l ->
    List.In x l.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Lemma pair_in_to_in_r:
    forall A (x:A) y l,
    PairIn (x, y) l ->
    List.In y l.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Lemma m_pair_in_to_in_l:
    forall A (x:A) y ls,
    MPairIn (x, y) ls ->
    MIn x ls.
  Proof.
    intros.
    apply Exists_exists in H.
    destruct H as (l, (Hi, Hp)).
    assert (List.In x l) by eauto using pair_in_to_in_l.
    eauto using m_in_def.
  Qed.

  Lemma m_pair_in_to_in_r:
    forall A (x:A) y ls,
    MPairIn (x, y) ls ->
    MIn y ls.
  Proof.
    intros.
    apply Exists_exists in H.
    destruct H as (l, (Hi, Hp)).
    assert (List.In y l) by eauto using pair_in_to_in_r.
    eauto using m_in_def.
  Qed.

  Lemma m_pair_in_to_in:
    forall A (x:A) y ls,
    MPairIn (x, y) ls ->
    MIn x ls /\ MIn y ls.
  Proof.
    intros.
    split; eauto using m_pair_in_to_in_l, m_pair_in_to_in_r.
  Qed.

  Lemma pair_incl_prepend:
    forall A l2 ls,
    ls <> [] ->
    @PairIncl A l2 ls ->
    forall l1,
    PairIncl (l1 ++ l2) (prepend l1 ls).
  Proof.
    unfold PairIncl, Included, Ensembles.In; intros.
    inversion H1; subst; clear H1.
    apply in_app_iff in H3.
    apply in_app_iff in H2.
    assert (Hin: forall a, List.In a l2 -> MIn a ls). {
      intros.
      destruct l2. {
        contradiction.
      }
      assert (Hi: MPairIn (a, a0) ls). {
        assert (PairIn (a, a0) (a0::l2)). {
          apply pair_in_def; auto using in_eq.
        }
        auto.
      }
      eauto using m_pair_in_to_in_l.
    }
    destruct H3, H2.
    - eauto using pair_in_prepend_1, pair_in_def.
    - auto using pair_in_prepend_2.
    - auto using pair_in_prepend_3.
    - auto using pair_in_prepend_4, pair_in_def.
  Qed.

  Lemma in_prod:
    forall (A : Type) (x : list A) a ls1 ls2,
    List.In a ls1 ->
    List.In x (prepend a ls2) ->
    List.In x (prod ls1 ls2).
  Proof.
    induction ls1; intros. {
      contradiction.
    }
    inversion H; subst; clear H; simpl; apply in_app_iff; auto.
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

  Lemma m_in_concat:
    forall A (x:A) ll,
    MIn x ll <-> List.In x (List.concat ll).
  Proof.
    split; intros; auto using m_in_to_in_concat, in_concat_to_m_in.
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

  Lemma m_pair_in_prod:
    forall {A} (x:A) y ls1 ls2,
    MIn x ls1 ->
    MIn y ls2 ->
    MPairIn (x,y) (prod ls1 ls2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply Exists_exists.
    exists (l ++ l0).
    split.
    - eapply in_prod; eauto.
      eapply in_prepend; eauto.
    - eapply pair_in_def; apply in_app_iff; auto.
  Qed.

  Lemma m_pair_in_prod_l:
    forall {A} p ls1 ls2,
    @MPairIn A p ls1 ->
    ls2 <> [] ->
    MPairIn p (prod ls1 ls2).
  Proof.
    intros.
    apply Exists_exists in H.
    destruct H as (l, (Hi, Hp)).
    destruct ls2. {
      contradiction.
    }
    apply Exists_exists.
    exists (l ++ l0).
    split.
    - eapply in_prod; eauto.
      eapply in_prepend; eauto using in_eq.
    - auto using pair_in_app_l.
  Qed.

  Lemma m_pair_in_prod_r:
    forall {A} p ls1 ls2,
    @MPairIn A p ls2 ->
    ls1 <> [] ->
    MPairIn p (prod ls1 ls2).
  Proof.
    intros.
    apply Exists_exists in H.
    destruct H as (l, (Hi, Hp)).
    destruct ls1. {
      contradiction.
    }
    apply Exists_exists.
    exists (l0 ++ l).
    split.
    - simpl.
      apply in_app_iff.
      left.
      eapply in_prepend; eauto using in_eq.
    - auto using pair_in_app_r.
  Qed.

  Lemma m_pair_in_app_l:
    forall A p (ls1 ls2: list (list A)),
    MPairIn p ls1 ->
    MPairIn p (ls1 ++ ls2).
  Proof.
    induction ls1; intros. {
      inversion H.
    }
    inversion H; subst; clear H. {
      apply Exists_exists.
      exists a.
      simpl.
      intuition.
    }
    apply IHls1 with (ls2:=ls2) in H1; eauto.
    unfold MPairIn.
    simpl.
    apply Exists_cons.
    right.
    auto.
  Qed.

  Lemma m_pair_in_app_r:
    forall A p (ls1 ls2: list (list A)),
    MPairIn p ls2 ->
    MPairIn p (ls1 ++ ls2).
  Proof.
    induction ls1; intros. {
      simpl.
      assumption.
    }
    simpl.
    apply IHls1 in H.
    apply Exists_cons.
    auto.
  Qed.

  Lemma m_pair_in_concat:
    forall {A} p (ls:list (list A)) lls,
    List.In ls lls ->
    MPairIn p ls ->
    MPairIn p (List.concat lls).
  Proof.
    induction lls; intros. {
      contradiction.
    }
    simpl.
    inversion H; subst; clear H. {
      apply m_pair_in_app_l; auto.
    }
    apply m_pair_in_app_r.
    auto.
  Qed.
End Ops.

Section filter.
  Lemma filter_app:
    forall {A:Type} f (l1:list A) l2,
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; simpl; intros. {
      reflexivity.
    }
    destruct (f a); simpl; rewrite IHl1; reflexivity.
  Qed.
End filter.

Section clos_trans_refl.
  Lemma clos_refl_trans_to_clos_trans:
    forall (A:Type) (R:relation A) x y,
    clos_refl_trans A R x y ->
    clos_trans A R x y \/ x = y.
  Proof.
    intros.
    induction H.
    - left.
      auto using t_step.
    - intuition.
    - destruct IHclos_refl_trans1 as [Hx|Hx]. {
        destruct IHclos_refl_trans2 as [Hy|Hy]. {
          left.
          apply t_trans with (y:=y); auto.
        }
        subst.
        intuition.
      }
      destruct IHclos_refl_trans2 as [Hy|Hy]; subst; intuition.
  Qed.
End clos_trans_refl.

Section LinWalk2.
  Variable A:Type.
  Variable Edge: A * A -> Prop.

  Lemma walk2_inv_3:
    forall v1 vn w,
    Walk2 Edge v1 vn w ->
    (w = (v1,vn)::nil /\ Edge (v1, vn)) \/
    (exists v2, Edge (v1, v2) /\ exists w' e', w = (v1, v2) :: e' :: w' /\ Walk2 Edge v2 vn (e' :: w')).
  Proof.
    intros.
    destruct w. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    destruct w. {
      apply walk2_inv_pair in H.
      destruct H.
      subst.
      intuition.
    }
    right.
    apply walk2_inv in H.
    destruct H as (v2, (?, (?, ?))).
    exists v2.
    intuition.
    exists w.
    subst.
    exists p0.
    intuition.
  Qed.

  Lemma walk2_inv_fst_edge:
    forall x y w,
    Walk2 Edge x y w ->
    exists v, Edge (x, v).
  Proof.
    intros.
    apply walk2_inv_3 in H.
    destruct H as [(?,Hx)|(v2, (Hx,_))]. {
      subst.
      eauto.
    }
    eauto.
  Qed.

  Lemma reaches_inv_fst_edge:
    forall x y,
    Reaches Edge x y ->
    exists v, Edge (x, v).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using walk2_inv_fst_edge.
  Qed.

  Lemma ends_with_to_in:
    forall w (x:A),
    EndsWith w x ->
    exists v, List.In (v, x) w.
  Proof.
    induction w; intros. {
      apply ends_with_nil_inv in H.
      contradiction.
    }
    destruct w. {
      destruct a as (a1, a2).
      apply ends_with_inv_cons_nil in H.
      subst.
      eauto using in_eq.
    }
    apply ends_with_inv in H.
    apply IHw in H.
    destruct H as (v, Hi).
    eauto using in_cons.
  Qed.

  Lemma walk2_inv_snd_edge:
    forall x y w,
    Walk2 Edge x y w ->
    exists v, Edge (v, y).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply ends_with_to_in in H1.
    destruct H1 as (v, Hi).
    exists v.
    apply in_edge with (w:=w); auto.
  Qed.

  Lemma reaches_inv_snd_edge:
    forall x y,
    Reaches Edge x y ->
    exists v, Edge (v, y).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using walk2_inv_snd_edge.
  Qed.

  Variable edge_fun: forall a b c,
    Edge (a, b) ->
    Edge (a, c) ->
    b = c.

  Variable irreflexive:
    forall x,
    ~ clos_trans A (fun a b => Edge (a, b)) x x.

  Let walk2_irreflexive:
    forall x w, ~ Walk2 Edge x x w.
  Proof.
    intros.
    intros N.
    apply walk2_to_clos_trans with (R:=fun a b=>Edge (a,b)) in N. {
      apply irreflexive in N.
      contradiction.
    }
    tauto.
  Qed.

  (** If the edge behaves like a function, then there is only one path to
      arrive at each node. *)
  Lemma walk2_linear_fun:
    forall w1 a b w2,
    Walk2 Edge a b w1 ->
    Walk2 Edge a b w2 ->
    w1 = w2.
  Proof.
    induction w1; intros. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    apply walk2_inv_3 in H.
    destruct H as [(Hr,?)|(v2,(He, (w, (e,(Hx, Hy)))))]. {
      inversion Hr; subst; clear Hr.
      apply walk2_inv_3 in H0.
      destruct H0 as [(Hr, ?)|(v2,(?,(w,(e,(Hx,Hy)))))]. {
        subst.
        reflexivity.
      }
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    inversion Hx; subst; clear Hx.
    apply walk2_inv_3 in H0.
    destruct H0 as [(?,?)|(v3,(Hf,(w',(e',(Hx,Hz)))))]. {
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    subst.
    assert (v3 = v2) by eauto.
    subst.
    apply IHw1 in Hz; auto.
    inversion Hz; subst; clear Hz.
    reflexivity.
  Qed.
End LinWalk2.

Section BigStep.
  Variable A:Type.
  Variable R: relation A.
  Variable Value: A -> Prop.
  Definition Edge (p:A*A) := let (x,y) := p in R x y. 
  Inductive BigStep : A -> A -> Prop :=
  | big_step_reaches:
    forall x y,
    Reaches Edge x y ->
    Value y ->
    BigStep x y
  | safe_path_skip:
    forall x,
    Value x ->
    BigStep x x.

End BigStep.
