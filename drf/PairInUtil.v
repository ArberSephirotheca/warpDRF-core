From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Sets.Constructive_sets.
Require Import Aniceto.Graphs.Graph.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.

From Stdlib Require Import Lists.List.
Require Import Util.
Require Import InUtil.
Require Import Tictac.
Import ListNotations.

Section Defs.

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

  (* Every pair in l must also be in a list of ls *)
  Definition MPairIncl {A:Type} ls1 ls2 :=
    forall x y,
      MIn x ls1 ->
      MIn y ls1 ->
      @MPairIn A (x, y) ls2.

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

  Lemma pair_not_in_nil:
    forall A p,
    ~ @PairIn A p [].
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    contradiction.
  Qed.

  Lemma pair_in_sym:
    forall A x y l,
    @PairIn A (x, y) l ->
    PairIn (y, x) l.
  Proof.
    intros.
    invc H.
    eauto using pair_in_def.
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
    apply pair_not_in_nil in H.
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

  Lemma m_pair_in_prod_1:
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

  Lemma m_pair_in_prod_2:
    forall {A} (x:A) y ls1 ls2,
    MIn x ls2 ->
    MIn y ls1 ->
    MPairIn (x,y) (prod ls1 ls2).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply Exists_exists.
    exists (l0 ++ l).
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

  Lemma m_pair_in_def:
    forall A ll p (l:list A),
    PairIn p l ->
    List.In l ll ->
    MPairIn p ll.
  Proof.
    intros.
    apply Exists_exists.
    eauto.
  Qed.


  Lemma pair_in_refl:
    forall A x l,
    @List.In A x l ->
    PairIn (x, x) l.
  Proof.
    intros.
    auto using pair_in_def.
  Qed.

  Lemma m_pair_in_refl:
    forall A x m,
    @MIn A x m ->
    MPairIn (x, x) m.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using m_pair_in_def, pair_in_refl.
  Qed.


  Lemma m_pair_in_inv_cons_nil:
    forall A p l,
    @MPairIn A p ([] :: l) ->
    MPairIn p l.
  Proof.
    intros.
    inversion H; subst; clear H.
    - apply pair_not_in_nil in H1.
      contradiction.
    - assumption.
  Qed.

  Lemma m_pair_in_nil:
    forall A p,
    ~ @MPairIn A p [].
  Proof.
    intros.
    intros N.
    inversion N.
  Qed.


  Lemma m_pair_in_eq:
    forall A p l ls,
    @PairIn A p l ->
    MPairIn p (l :: ls).
  Proof.
    intros.
    apply m_pair_in_def with (l:=l); auto using in_eq.
  Qed.

  Lemma m_pair_in_cons:
    forall A p l ls,
    @MPairIn A p ls ->
    MPairIn p (l :: ls).
  Proof.
    intros.
    unfold MPairIn in H.
    rewrite Exists_exists in H.
    destruct H as (l1, (Hi, Hp)).
    eauto using m_pair_in_def, in_cons, in_eq.
  Qed.

  Lemma m_pair_in_app_or:
    forall A p ls1 ls2,
    @MPairIn A p (ls1 ++ ls2) ->
    MPairIn p ls1 \/ MPairIn p ls2.
  Proof.
    intros.
    unfold MPairIn in H.
    apply Exists_exists in H.
    destruct H as (l, (Hi, Hp)).
    apply in_app_or in Hi.
    destruct Hi as [Hi|Hi];
      eauto using m_pair_in_def.
  Qed.

  Lemma m_pair_in_app_sym:
    forall A p m1 m2,
    @MPairIn A p (m1 ++ m2) ->
    MPairIn p (m2 ++ m1).
  Proof.
    intros.
    apply m_pair_in_app_or in H.
      destruct H;
        eauto using m_pair_in_app_r, m_pair_in_app_l.
  Qed.

  Lemma m_pair_in_inv:
    forall A p a h,
    MPairIn p (a :: h) ->
    PairIn p a \/ @MPairIn A p h.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
  Qed.

  Lemma pair_in_inv_app:
    forall A p l1 l2, 
    @PairIn A p (l1 ++ l2) ->
    PairIn p l1 \/
    PairIn p l2 \/
    (List.In (fst p) l1 /\  List.In (snd p) l2) \/
    (List.In (snd p) l1 /\  List.In (fst p) l2).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply in_app_or in H0.
    apply in_app_or in H1.
    destruct H0, H1; auto using pair_in_def.
  Qed.

  Lemma m_pair_in_inv_prepend:
    forall A p ll l,
    @MPairIn A p (prepend l ll) ->
    MPairIn p ll \/
    PairIn p l \/
    (List.In (fst p) l /\ MIn (snd p) ll) \/
    (List.In (snd p) l /\ MIn (fst p) ll).
  Proof.
    induction ll; intros. {
      simpl in *.
      apply m_pair_in_nil in H.
      contradiction.
    }
    simpl in *.
    apply m_pair_in_inv in H.
    destruct H as [H|H]. {
      apply pair_in_inv_app in H.
      destruct H as [H|[H|[(Ha,Hb)|(Ha,Hb)]]].
      - auto.
      - eauto using m_pair_in_eq.
      - right.
        right.
        left.
        split; eauto using m_in_def, in_eq.
      - right.
        right.
        right.
        split; eauto using m_in_def, in_eq.
    }
    apply IHll in H; clear IHll.
    destruct H as [H|[H|[(Ha,Hb)|(Ha,Hb)]]].
    - eauto using m_pair_in_cons.
    - auto.
    - right. right.
      left.
      eauto using m_in_def, m_in_cons.
    - right; right; right.
      eauto using m_in_def, m_in_cons.
  Qed.

  Lemma m_pair_in_inv_prod:
    forall A m1 m2 p,
    @MPairIn A p (prod m1 m2) ->
    MPairIn p m1 \/
    MPairIn p m2 \/
    (MIn (fst p) m1 /\ MIn (snd p) m2) \/
    (MIn (fst p) m2 /\ MIn (snd p) m1).
  Proof.
    induction m1; intros. {
      simpl in *.
      auto.
    }
    simpl in *.
    apply m_pair_in_app_or in H.
    destruct H as [Hx|Hx]. {
      apply m_pair_in_inv_prepend in Hx.
      destruct Hx as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
      - auto.
      - auto using m_pair_in_eq.
      - right.
        right.
        left.
        eauto using m_in_eq.
      - right.
        right.
        right.
        eauto using m_in_eq.
    }
    apply IHm1 in Hx.
    destruct Hx as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
    - auto using m_pair_in_cons.
    - auto.
    - right.
      right.
      left.
      auto using m_in_cons.
    - right.
      right.
      right.
      auto using m_in_cons.
  Qed.

  Lemma m_pair_in_prod_cons_r:
    forall A p a m1 m2,
    @MPairIn A p (prod m1 m2) ->
    MPairIn p (prod m1 (a :: m2)).
  Proof.
    intros.
    assert (m1 <> []). {
      intros N; subst.
      apply m_pair_in_nil in H.
      assumption.
    }
    apply m_pair_in_inv_prod in H.
    destruct H as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
    - apply m_pair_in_prod_l; auto.
      intros N; inversion N.
    - apply m_pair_in_prod_r; auto.
      apply m_pair_in_cons.
      assumption.
    - destruct p as (v1,v2).
      simpl in *.
      apply m_pair_in_prod_1; auto using m_in_cons.
    - destruct p as (v1,v2).
      simpl in *.
      apply m_pair_in_prod_2; auto using m_in_cons.
  Qed.

  Lemma m_pair_in_prod_sym:
    forall A p m1 m2,
    m2 <> [] ->
    @MPairIn A p (prod m1 m2) ->
    MPairIn p (prod m2 m1).
  Proof.
    induction m1; intros. {
      simpl in *.
      apply m_pair_in_nil in H0.
      contradiction.
    }
    simpl in *.
    apply m_pair_in_app_or in H0.
    destruct H0 as [Hx|Hx]. {
      apply m_pair_in_inv_prepend in Hx.
      destruct Hx as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
      - apply m_pair_in_prod_l; auto.
        intros N; inversion N.
      - apply m_pair_in_prod_r; auto.
        auto using m_pair_in_eq.
      - assert (Hi: MIn (fst p) (a::m1)) by eauto using m_in_eq.
        destruct p as (v1, v2).
        auto using m_pair_in_prod_2.
      - assert (Hi: MIn (snd p) (a::m1)) by eauto using m_in_eq.
        destruct p as (v1, v2).
        auto using m_pair_in_prod_1.
    }
    apply IHm1 in Hx; auto using m_pair_in_prod_cons_r.
  Qed.

  Lemma m_pair_in_incl:
    forall A m1 m2,
    incl m1 m2 ->
    forall p,
    MPairIn (A:=A) p m1 ->
    MPairIn p m2.
  Proof.
    induction m1; intros. {
      apply m_pair_in_nil in H0.
      contradiction.
    }
    rename_hyp (MPairIn _ _) as Hm.
    apply m_pair_in_inv in Hm.
    destruct Hm as [Hm|Hm]. {
      assert (In a m2). {
        unfold incl in *.
        auto using in_eq.
      }
      eauto using m_pair_in_def.
    }
    eauto using List.incl_strengthten.
  Qed.


  Lemma m_pair_in_app_or_iff:
    forall (A : Type) (p : A * A) (ls1 ls2 : list (list A)),
    MPairIn p (ls1 ++ ls2) <-> MPairIn p ls1 \/ MPairIn p ls2.
  Proof.
    split; intros.
    - apply m_pair_in_app_or; auto.
    - destruct H; auto using m_pair_in_app_r, m_pair_in_app_l.
  Qed.

  Lemma m_pair_in_cons_or_iff:
    forall (A : Type) (p : A * A) h l,
    MPairIn p (h :: l) <-> PairIn p h \/ MPairIn p l.
  Proof.
    split; intros.
    - auto using m_pair_in_inv.
    - destruct H; auto using m_pair_in_eq, m_pair_in_cons.
  Qed.

End Defs.