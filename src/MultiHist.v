Require Import Coq.Lists.List.

Require Import Access.
Require Import Util.
Require Import SetTh.
Require Import Util.
Require Import InUtil.
Require Import PairInUtil.

Import ListNotations.

Section Defs.
  Context {A:Access}.
  Notation history := (list access_val).
  Definition MemEquiv (m1 m2:list history) :=
    forall p,
    MPairIn p m1 <-> MPairIn p m2.

  Lemma mem_equiv_iff_equiv:
    forall m1 m2,
    MemEquiv m1 m2 <-> Equiv (fun p => MPairIn p m1) (fun p => MPairIn p m2).
  Proof.
    intros.
    unfold Equiv, Member, MemEquiv.
    reflexivity.
  Qed.

  Lemma mem_equiv_refl:
    forall m,
    MemEquiv m m.
  Proof.
    intros.
    rewrite mem_equiv_iff_equiv.
    reflexivity.
  Qed.

  Lemma mem_equiv_sym:
    forall m1 m2,
    MemEquiv m1 m2 ->
    MemEquiv m2 m1.
  Proof.
    intros.
    rewrite mem_equiv_iff_equiv in *.
    symmetry.
    auto.
  Qed.

  Lemma mem_equiv_trans:
    forall m1 m2 m3,
    MemEquiv m1 m2 ->
    MemEquiv m2 m3 ->
    MemEquiv m1 m3.
  Proof.
    intros.
    rewrite mem_equiv_iff_equiv in *.
    eapply equiv_trans; eauto.
  Qed.

  (** Register [MemEquiv] in Coq's tactics. *)
  Global Add Parametric Relation : (list history) MemEquiv
    reflexivity proved by mem_equiv_refl
    symmetry proved by mem_equiv_sym
    transitivity proved by mem_equiv_trans
    as mem_equiv_setoid.

  Lemma mem_equiv_nil_rw:
    forall n,
    MemEquiv (repeat [] n) [].
  Proof.
    induction n; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    unfold MemEquiv.
    split; intros. {
      (*unfold Hist.history in *.*)
      apply m_pair_in_inv_cons_nil in H.
      apply IHn in H.
      assumption.
    }
    apply m_pair_in_nil in H.
    contradiction.
  Qed.

  Lemma mem_equiv_cons_nil_rw:
    MemEquiv [[]] [].
  Proof.
    apply (mem_equiv_nil_rw 1).
  Qed.

  Lemma mem_equiv_app_sym:
    forall m1 m2,
    MemEquiv (m1 ++ m2) (m2 ++ m1).
  Proof.
    split; intros; eauto using m_pair_in_app_sym.
  Qed.

  Lemma m_pair_in_app_equiv:
    forall p m1 m2 m3 m4,
    MemEquiv m1 m3 ->
    MemEquiv m2 m4 ->
    MPairIn p (m1 ++ m2) ->
    MPairIn p (m3 ++ m4).
  Proof.
    intros.
    apply m_pair_in_app_or in H1.
    destruct H1. {
      apply H in H1.
      eauto using m_pair_in_app_l.
    }
    apply H0 in H1.
    eauto using m_pair_in_app_r.
  Qed.

  Lemma mem_equiv_app:
    forall m1 m2 m3 m4,
    MemEquiv m1 m3 ->
    MemEquiv m2 m4 ->
    MemEquiv (m1 ++ m2) (m3 ++ m4).
  Proof.
    intros.
    unfold MemEquiv.
    split; intros.
    - eauto using m_pair_in_app_equiv.
    - symmetry in H.
      symmetry in H0.
      eauto using m_pair_in_app_equiv.
  Qed.

  Lemma mem_equiv_app_refl_rw:
    forall m,
    MemEquiv (m ++ m) m.
  Proof.
    split; intros.
    + apply m_pair_in_app_or in H.
      destruct H; auto.
    + apply m_pair_in_app_l.
      assumption.
  Qed.

  Import Morphisms.

  Global Instance app_mem_equiv_proper: Proper (MemEquiv ==> MemEquiv ==> MemEquiv) (@app history).
  Proof.
    unfold Proper, respectful.
    intros.
    auto using mem_equiv_app.
  Qed.

  Lemma mem_equiv_m_in:
    forall m1 m2 x,
    MemEquiv m1 m2 ->
    MIn x m1 ->
    MIn x m2.
  Proof.
    intros.
    assert (MPairIn (x,x) m1) by eauto using m_pair_in_refl.
    apply H in H1.
    eauto using m_pair_in_to_in_r.
  Qed.

  Global Instance in_mem_equiv_proper: Proper (eq ==> MemEquiv ==> iff) (@MIn access_val).
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros.
    - subst.
      eauto using mem_equiv_m_in.
    - symmetry in H0.
      subst.
      eauto using mem_equiv_m_in.
  Qed.

  Lemma mem_equiv_concat_repeat_rw:
    forall m n,
    n > 0 ->
    MemEquiv (List.concat (repeat m n)) m.
  Proof.
    induction n; intros.
    - simpl. inversion H.
    - inversion H; subst; clear H.
      + simpl.
        rewrite app_nil_r.
        reflexivity.
      + simpl.
        rewrite IHn; auto.
        rewrite mem_equiv_app_refl_rw.
        reflexivity.
  Qed.


  Lemma mem_equiv_concat_refl_rw:
    forall m l,
    l <> [] ->
    (forall m', List.In m' l -> MemEquiv m' m) ->
    MemEquiv (List.concat l) m.
  Proof.
    induction l; intros. {
      contradiction.
    }
    simpl.
    assert (MemEquiv a m) by eauto using in_eq.
    destruct l. {
      rewrite app_nil_r.
      assumption.
    }
    assert (Hne : l :: l0 <> []). {
      intros N.
      inversion N.
    }
    assert (Hfl: (forall m' : list history, List.In m' (l :: l0) -> MemEquiv m' m)). {
      eauto using in_cons.
    }
    assert (IHl := IHl Hne Hfl).
    rewrite IHl.
    rewrite H1.
    rewrite mem_equiv_app_refl_rw.
    reflexivity.
  Qed.

  Lemma mequiv_app_nil_r:
    forall m,
    MemEquiv (m ++ [[]]) m.
  Proof.
    intros.
    rewrite mem_equiv_cons_nil_rw.
    rewrite app_nil_r.
    reflexivity.
  Qed.


  Lemma mem_equiv_cons_eq_nil:
    forall h,
    MemEquiv [h] [] ->
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
    MemEquiv ([] :: h) [] ->
    MemEquiv h [].
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
    MemEquiv h [] ->
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
    MemEquiv m (prod (repeat [] (S n)) m).
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
    MemEquiv m1 [] ->
    forall m2,
    MemEquiv m2 (prod m1 m2).
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

  Lemma mem_equiv_app_r:
    forall m1 m2 m3,
    MemEquiv m1 m2 ->
    MemEquiv (m3 ++ m1) (m3 ++ m2).
  Proof.
    intros.
    split; intros; apply m_pair_in_app_or in H0; destruct H0 as [Hx|Hx].
    - auto using m_pair_in_app_l.
    - apply H in Hx.
      auto using m_pair_in_app_r.
    - auto using m_pair_in_app_l.
    - apply H in Hx.
      auto using m_pair_in_app_r.
  Qed.

  Lemma mem_equiv_app_l:
    forall m1 m2 m3,
    MemEquiv m1 m2 ->
    MemEquiv (m1 ++ m3) (m2 ++ m3).
  Proof.
    intros.
    rewrite (mem_equiv_app_sym m1 m3).
    rewrite (mem_equiv_app_sym m2 m3).
    auto using mem_equiv_app_r.
  Qed.


  Lemma prod_app_r:
    forall ll1 ll2 ll3, 
    MemEquiv (prod ll1 ll2 ++ prod ll1 ll3) (prod ll1 (ll2 ++ ll3)).
  Proof.
    induction ll1; intros. {
      reflexivity.
    }
    simpl.
    rewrite <- IHll1.
    rewrite prepend_app_r.
    repeat rewrite app_assoc_reverse.
    assert (R:
      MemEquiv
        (prod ll1 ll2 ++ prepend a ll3)
        (prepend a ll3 ++ prod ll1 ll2)
    ). {
      rewrite mem_equiv_app_sym.
      reflexivity.
    }
    repeat rewrite app_assoc.
    apply mem_equiv_app_l.
    repeat rewrite app_assoc_reverse.
    rewrite R.
    reflexivity.
  Qed.

  Lemma mem_equiv_prod_sym:
    forall m1 m2,
    m1 <> [] ->
    m2 <> [] ->
    MemEquiv (prod m1 m2) (prod m2 m1).
  Proof.
    intros.
    split; intros.
    - auto using m_pair_in_prod_sym.
    - auto using m_pair_in_prod_sym.
  Qed.

  Lemma mem_equiv_prod_r:
    forall m1 m2 m3,
    m1 <> [] ->
    m2 <> [] ->
    m3 <> [] ->
    MemEquiv m1 m2 ->
    MemEquiv (prod m3 m1) (prod m3 m2).
  Proof.
    intros m1 m2 m3 Hn1 Hn2 Hn3 R.
    split; intros Hi; apply m_pair_in_inv_prod in Hi; destruct Hi as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
    - apply m_pair_in_prod_l; auto.
    - apply R in Hx.
      apply m_pair_in_prod_r; auto.
    - destruct p as (v1,v2).
      simpl in *.
      rewrite R in Hb.
      auto using m_pair_in_prod_1.
    - destruct p as (v1,v2).
      simpl in *.
      rewrite R in Ha.
      auto using m_pair_in_prod_2.
    - auto using m_pair_in_prod_l.
    - apply R in Hx.
      auto using m_pair_in_prod_r.
    - destruct p as (v1, v2).
      simpl in *.
      rewrite <- R in Hb.
      auto using m_pair_in_prod_1.
    - destruct p as (v1, v2).
      simpl in *.
      rewrite <- R in Ha.
      auto using m_pair_in_prod_2.
  Qed.

  Lemma mem_equiv_prod_l:
    forall m1 m2 m3,
    m1 <> [] ->
    m2 <> [] ->
    m3 <> [] ->
    MemEquiv m1 m2 ->
    MemEquiv (prod m1 m3) (prod m2 m3).
  Proof.
    intros.
    rewrite (mem_equiv_prod_sym m1 m3); auto.
    rewrite (mem_equiv_prod_sym m2 m3); auto.
    auto using mem_equiv_prod_r.
  Qed.

  Lemma app_prod_absorb_1:
    forall m1 m2,
    m1 <> [] ->
    MemEquiv
      ((prod m1 m2) ++ m2)
      (prod m1 m2).
  Proof.
    split; intros.
    - apply m_pair_in_app_or in H0.
      destruct H0 as [?|Hx]; auto.
      auto using m_pair_in_prod_r.
    - apply m_pair_in_app_l.
      assumption.
  Qed.

  Definition MIncl (m1 m2:list history) : Prop :=
    forall p, MPairIn p m1 -> MPairIn p m2.

  Lemma m_incl_refl:
    forall m,
    MIncl m m.
  Proof.
    unfold MIncl; auto.
  Qed.

  Lemma m_incl_trans:
    forall m1 m2 m3,
    MIncl m1 m2 ->
    MIncl m2 m3 ->
    MIncl m1 m3.
  Proof.
    unfold MIncl; intros.
    auto.
  Qed.

  Lemma m_equiv_to_m_incl:
    forall m1 m2,
    MemEquiv m1 m2 ->
    MIncl m1 m2 /\ MIncl m2 m1.
  Proof.
    unfold MemEquiv, MIncl.
    intros.
    split; intros.
    - apply H.
      assumption.
    - apply H.
      assumption.
  Qed.

  (** Register [MIncl] in Coq's tactics. *)
  Global Add Parametric Relation : (list history) MIncl
    reflexivity proved by m_incl_refl
    transitivity proved by m_incl_trans
    as m_incl_setoid.

  Lemma m_incl_m_equiv:
    forall m1 m2 m3 m4,
    MemEquiv m1 m2 ->
    MemEquiv m3 m4 ->
    MIncl m1 m3 ->
    MIncl m2 m4.
  Proof.
    intros.
    apply m_equiv_to_m_incl in H.
    destruct H.
    apply m_equiv_to_m_incl in H0.
    destruct H0.
    transitivity m1; auto.
    transitivity m3; auto.
  Qed.

  Global Instance m_incl_equiv_proper: Proper (MemEquiv ==> MemEquiv ==> iff) MIncl.
  Proof.
    unfold Proper, respectful.
    split; intros.
    - eauto using m_incl_m_equiv.
    - symmetry in H.
      symmetry in H0.
      eauto using m_incl_m_equiv.
  Qed.

  Lemma m_incl_app_l:
    forall m1 m2,
    MIncl m1 m2 ->
    MemEquiv (m1 ++ m2) m2.
  Proof.
    intros.
    split; intros. {
      apply m_pair_in_app_or in H0.
      destruct H0 as [Ha|Ha]; auto.
    }
    auto using m_pair_in_app_r.
  Qed.

  Lemma m_incl_app_r:
    forall m1 m2,
    MIncl m1 m2 ->
    MemEquiv (m2 ++ m1) m2.
  Proof.
    intros.
    rewrite (mem_equiv_app_sym m2 m1).
    auto using m_incl_app_l.
  Qed.

  Lemma m_incl_prod_1:
    forall m1 m2,
    m1 <> [] ->
    MIncl m2 (prod m1 m2).
  Proof.
    unfold MIncl; intros.
    auto using m_pair_in_prod_r.
  Qed.

  Lemma m_incl_prod_2:
    forall m1 m2,
    m2 <> [] ->
    MIncl m1 (prod m1 m2).
  Proof.
    unfold MIncl; intros.
    auto using m_pair_in_prod_l.
  Qed.

  Lemma m_incl_prod_3:
    forall m1 m2 m3,
    m3 <> [] ->
    MIncl m2 m3 ->
    MIncl (prod m1 m2) (prod m1 m3).
  Proof.
    unfold MIncl.
    intros.
    destruct (list_eq_nil m1) as [?|Hne]. {
      subst.
      simpl in *.
      assumption.
    }
    apply m_pair_in_inv_prod in H1.
    destruct H1 as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
    - apply m_pair_in_prod_l; auto.
    - apply H0 in Hx.
      auto using m_pair_in_prod_r.
    - destruct p as (v1, v2); simpl in *.
      assert (MIn v2 m3). {
        eauto using m_pair_in_to_in_r, m_pair_in_refl.
      }
      eauto using m_pair_in_prod_1.
    - destruct p as (v1, v2); simpl in *.
      assert (MIn v1 m3). {
        eauto using m_pair_in_to_in_l, m_pair_in_refl.
      }
      eauto using m_pair_in_prod_2.
  Qed.

(*
  Lemma m_incl_prod_4:
    forall m1 m2 m3,
    m3 <> [] ->
    MIncl m2 m3 ->
    MIncl (prod m2 m1) (prod m3 m1).
  Proof.
    unfold MIncl.
    intros.
    destruct (list_eq_nil m1) as [?|Hne]. {
      subst.
      rewrite prod_nil_r in *.
      assumption.
    }
    apply m_pair_in_inv_prod in H1.
    destruct H1 as [Hx|[Hx|[(Ha,Hb)|(Ha,Hb)]]].
    - apply m_pair_in_prod_l; auto.
    - apply H0 in Hx.
      auto using m_pair_in_prod_r.
    - destruct p as (v1, v2); simpl in *.
      assert (MIn v2 m3). {
        eauto using m_pair_in_to_in_r, m_pair_in_refl.
      }
      eauto using m_pair_in_prod_1.
    - destruct p as (v1, v2); simpl in *.
      assert (MIn v1 m3). {
        eauto using m_pair_in_to_in_l, m_pair_in_refl.
      }
      eauto using m_pair_in_prod_2.
  Qed.
  *)
End Defs.


Section Member.
  Context `{A:Access}.
  Definition Member {A} l a := List.In (A:=A) a l.

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
    List.In x l ->
    List.In l ls ->
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

  Import Morphisms.

  Global Instance member_equiv_proper: Proper (MemEquiv ==> eq ==> iff) (@MMember access_val).
  Proof.
    unfold Proper, respectful.
    intros.
    repeat rewrite mmember_rw.
    subst.
    rewrite H.
    reflexivity.
  Qed.

  Global Instance member_in_equiv_proper: Proper (MemEquiv ==> @Equiv access_val) (@MMember access_val).
  Proof.
    unfold Proper, respectful.
    split; unfold SetTh.Member; intros.
    - rewrite <- H.
      assumption.
    - rewrite H.
      assumption.
  Qed.

  Goal
    forall (x:access_val),
    @MMember access_val [[]] x <-> MMember [] x.
  Proof.
    intros.
    rewrite mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Goal
    @Incl access_val (MMember [[]]) (MMember []).
  Proof.
    rewrite mem_equiv_cons_nil_rw.
    reflexivity.
  Qed.

  Goal
    forall m,
    @Incl access_val (MMember (m++ [[]])) (MMember m).
  Proof.
    intros.
    rewrite mequiv_app_nil_r.
    reflexivity.
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

  Definition MMImpl mm1 mm2 :=
    forall m1, List.In m1 mm1 -> exists m2, List.In m2 mm2 /\ MemEquiv m1 m2. 

  Definition MMEquiv mm1 mm2 := MMImpl mm1 mm2 /\ MMImpl mm2 mm1.
  Notation history := (list access_val).
  Inductive MMEquivStruct : list (list history) -> list (list history) -> Prop :=
  | mmequiv_struct_nil:
    MMEquivStruct [] []
  | mmequiv_struct_cons:
    forall m1 m2 mm1 mm2,
    MemEquiv m1 m2 ->
    MMEquivStruct mm1 mm2 ->
    MMEquivStruct (m1::mm1) (m2::mm2).

  Lemma mmequiv_struct_refl:
    forall m,
    MMEquivStruct m m.
  Proof.
    induction m; auto using mmequiv_struct_nil.
    apply mmequiv_struct_cons; auto.
    reflexivity.
  Qed.

  Lemma mmequiv_struct_trans:
    forall x y z,
    MMEquivStruct x y ->
    MMEquivStruct y z ->
    MMEquivStruct x z.
  Proof.
    intros x y.
    generalize dependent x.
    induction y; intros; inversion H; inversion H0; subst; clear H H0.
    - apply mmequiv_struct_nil.
    - apply mmequiv_struct_cons; eauto.
      etransitivity; eauto.
  Qed.

  Lemma mmequiv_struct_sym:
    forall x y,
    MMEquivStruct x y ->
    MMEquivStruct y x.
  Proof.
    induction x; intros; inversion H; subst; clear H. {
      apply mmequiv_struct_nil.
    }
    apply IHx in H4.
    symmetry in H2.
    auto using mmequiv_struct_cons.
  Qed.

  Global Add Parametric Relation : _ MMEquivStruct
    reflexivity proved by mmequiv_struct_refl
    symmetry proved by mmequiv_struct_sym
    transitivity proved by mmequiv_struct_trans
    as mmequiv_struct_setoid.

  Import Morphisms.

  Global Instance cons_mmequiv_struct_proper: Proper (MemEquiv ==> MMEquivStruct ==> MMEquivStruct) cons.
  Proof.
    unfold Proper, respectful.
    intros.
    auto using mmequiv_struct_cons.
  Qed.

  Lemma mmequiv_struct_to_mem_equiv:
    forall x y,
    MMEquivStruct x y ->
    MemEquiv (List.concat x) (List.concat y).
  Proof.
    induction x; intros; inversion H; subst; clear H. {
      reflexivity.
    }
    simpl.
    rewrite H2.
    apply mem_equiv_app_r.
    auto.
  Qed.

  (** Theory of memory expressions *)

  Inductive mexp :=
  | One: forall (m:list history), m <> [] -> mexp
  | Prod: mexp -> mexp -> mexp
  | Plus: mexp -> mexp -> mexp.

  (* We can flatten an expression down to a memory *)
  Fixpoint to_mem m :=
  match m with
  | One m _ => m
  | Prod m1 m2 => prod (to_mem m1) (to_mem m2)
  | Plus m1 m2 => app (to_mem m1) (to_mem m2)
  end.

  Fixpoint flatten_exp e :=
  match e with
  | One m _ => [m]
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
  | One m _ => MPairIn p m
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
    - assumption.
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
    - assumption.
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
    - assumption.
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

  (** Register [MemEquiv] in Coq's tactics. *)
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

  Lemma mem_equiv_prod:
    forall (m1 m2 m3 m4 : list history),
    m1 <> [] ->
    m2 <> [] ->
    m3 <> [] ->
    m4 <> [] ->
    MemEquiv m1 m2 ->
    MemEquiv m3 m4 ->
    MemEquiv (prod m1 m3) (prod m2 m4).
  Proof.
    split; intros.
    - apply m_pair_in_inv_prod in H5.
      destruct H5 as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]].
      + apply H3 in Hi.
        apply m_pair_in_prod_l; auto.
      + apply H4 in Hi. 
        apply m_pair_in_prod_r; auto.
      + destruct p.
        simpl in *.
        rewrite H3 in *.
        rewrite H4 in *.
        apply m_pair_in_prod_1; auto.
      + destruct p.
        simpl in *.
        rewrite H3 in *.
        rewrite H4 in *.
        apply m_pair_in_prod_2; auto.
    - apply m_pair_in_inv_prod in H5.
      destruct H5 as [Hi|[Hi|[(Ha,Hb)|(Ha,Hb)]]].
      + apply H3 in Hi.
        apply m_pair_in_prod_l; auto.
      + apply H4 in Hi. 
        apply m_pair_in_prod_r; auto.
      + destruct p.
        simpl in *.
        rewrite <- H3 in *.
        rewrite <- H4 in *.
        apply m_pair_in_prod_1; auto.
      + destruct p.
        simpl in *.
        rewrite <- H3 in *.
        rewrite <- H4 in *.
        apply m_pair_in_prod_2; auto.
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

  Lemma prod_inv_not_nil:
    forall A m1 m2,
    @prod A m1 m2 <> [] ->
    m1 <> [] /\ m2 <> [].
  Proof.
    intros.
    destruct m1. {
      contradiction.
    }
    destruct m2. {
      rewrite prod_nil_r in *.
      contradiction.
    }
    split; intros N; inversion N.
  Qed.

  Lemma one_prod_rw:
    forall m1 m2 n1,
    exists n2 n3,
    EEq (One (prod m1 m2) n1) (Prod (One m1 n2) (One m2 n3)).
  Proof.
    intros.
    assert (Hx := n1).
    apply prod_inv_not_nil in Hx.
    destruct Hx as (n2, n3).
    exists n2.
    exists n3.
    split; intros.
    - apply e_pair_in_1 in H.
      apply e_pair_in_2.
      simpl in *.
      assumption.
    - apply e_pair_in_1 in H.
      apply e_pair_in_2.
      simpl in *.
      assumption.
  Qed.

  Lemma one_app_rw m1 m2 n1 (n2:m1 <> []) (n3:m2 <> []):
    EEq (One (app m1 m2) n1) (Plus (One m1 n2) (One m2 n3)).
  Proof.
    split;
        intros;
        apply e_pair_in_1 in H;
        apply e_pair_in_2;
        simpl in *; auto.
  Qed.

End Member.