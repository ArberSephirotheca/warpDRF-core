Require Import Coq.Lists.List.

Import ListNotations.
Section Ops.

  Lemma app_neq_nil:
    forall A l1 l2,
    l1 <> [] ->
    l2 <> [] ->
    @app A l1 l2 <> [].
  Proof.
    intros.
    destruct l1. {
      contradiction.
    }
    destruct l2. {
      contradiction.
    }
    intros N.
    inversion N.
  Qed.

  Lemma list_eq_nil:
    forall {A:Type} (l:list A),
    l = [] \/ l <> [].
  Proof.
    intros.
    destruct l; auto.
    right.
    intros N.
    inversion N.
  Qed.

  (* ----------------------------- COUNT ------------------------- *)

  Fixpoint count n :=
  match n with
  | 0 => []
  | S n => n :: count n
  end.

  (** Prepends every element of a list with a prefix *)

  Definition prepend {A:Type} (l1:list A) (l2: list (list A)) : list (list A) :=
    List.fold_right (fun x accum => (l1 ++ x) :: accum) [] l2.  

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

  Lemma prepend_nil_l:
    forall A ll, 
    @prepend A [] ll = ll.
  Proof.
    induction ll; intros.
    - reflexivity.
    - simpl.
      rewrite IHll.
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

  Lemma prepend_app_r:
    forall A l ll1 ll2,
    @prepend A l (ll1 ++ ll2) = prepend l ll1 ++ prepend l ll2.
  Proof.
    induction ll1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHll1.
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

  Lemma prepend_inv_nil:
    forall A l x,
    @prepend A x l = [] ->
    l = [].
  Proof.
    induction l; intros. {
      reflexivity.
    }
    inversion H.
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

  (* -------------------------- PRODUCT --------------------------- *)

  (** Product of two lists. That is for each two elements x,y of lists l1 l2, yields
      x ++ y *)

  Definition prod {A:Type} (l1: list (list A)) (l2: list (list A)) : list (list A) :=
    List.fold_right (fun x accum => prepend x l2 ++ accum) [] l1. 

  Lemma prod_nil_nil_l:
    forall A ll, 
    @prod A [[]] ll = ll.
  Proof.
    intros.
    unfold prod.
    simpl.
    rewrite app_nil_r.
    rewrite prepend_nil_l.
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

  Lemma prod_nil_r:
    forall A ll,
    @prod A ll [] = [].
  Proof.
    induction ll; intros. { reflexivity. }
    simpl.
    rewrite IHll.
    reflexivity.
  Qed.

  Lemma prod_neq_nil:
    forall A ll1 ll2,
    ll1 <> [] ->
    ll2 <> [] ->
    @prod A ll1 ll2 <> [].
  Proof.
    intros.
    destruct ll1. {
      contradiction.
    }
    simpl.
    intros N.
    destruct l. {
      rewrite prepend_nil_l in *.
      destruct ll2. {
        contradiction.
      }
      inversion N.
    }
    destruct ll2. {
      contradiction.
    }
    simpl in *.
    inversion N.
  Qed.

  Lemma prod_inv_nil:
    forall A hs1 hs2,
    @prod A hs1 hs2 = [] ->
    hs1 = [] \/ hs2 = [].
  Proof.
    intros.
    destruct hs1. { auto. }
    destruct hs2. { auto. }
    inversion H.
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

  (* ---------------------- PREPEND + PROD -------------------------- *)

  Definition prepend1 {A:Type} (a:A) ls :=
     fold_right (fun x accum => (a::x) :: accum) [] ls.

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

  Lemma prod_assoc:
    forall (A:Type) l1 l2 l3,
    prod (@prod A l1 l2) l3 =
    prod l1 (prod l2 l3).
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    rewrite <- prod_app.
    rewrite <- prepend_prod.
    rewrite IHl1.
    reflexivity.
  Qed.

  Lemma prod_prepend_r:
    forall (A:Type) (l:list A) lls1 lls2,
    prod lls1 (prepend l lls2)
    =
    prod (prod (lls1) [l]) lls2.
  Proof.
    intros.
    destruct l; intros. {
      simpl.
      rewrite prod_assoc.
      simpl.
      rewrite app_nil_r.
      reflexivity.
    }
    rewrite prod_assoc.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma prepend_cons:
    forall A ls (a:A) l,
    prepend (a :: l) ls = prepend1 a (prepend l ls).
  Proof.
    induction ls; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHls.
    reflexivity.
  Qed.

  Lemma prepend_rw:
    forall (A:Type) lls l,
    @prepend A l lls = prod [l] lls.
  Proof.
    induction lls; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    rewrite IHlls.
    rewrite app_nil_r.
    reflexivity.
  Qed.
(*
  Definition interleave {A:Type} (p1 p2: list (list A) * list (list A)) :=
    let (ll1, ll3) := p1 in
    let (ll2, ll4) := p2 in
    @prod A (prod ll1 ll2) (prod ll3 ll4).
*)

  (* ------------------------------- MAP2 --------------------------- *)

  Definition map2 {A B C:Type} (f:A->B->C) l1 l2 :=
    List.map
      (fun (p:A * B) => let (v1,v2) := p in f v1 v2)
      (List.combine l1 l2).

  Lemma map2_nil_l:
    forall A B C f l,
    @map2 A B C f [] l = [].
  Proof.
    intros.
    destruct l; reflexivity.
  Qed.

  Lemma map2_nil_r:
    forall A B C f l,
    @map2 A B C f l [] = [].
  Proof.
    intros.
    destruct l; reflexivity.
  Qed.

  Lemma map2_cons_rw:
    forall A B C f l1 l2 x y,
    @map2 A B C f (x::l1) (y::l2) = (f x y):: map2 f l1 l2.
  Proof.
    unfold map2.
    simpl.
    reflexivity.
  Qed.

  Lemma map2_length_l:
    forall A B C f l1 l2,
    length l1 = length l2 ->
    length (@map2 A B C f l1 l2) = length l1.
  Proof.
    induction l1; intros;
      destruct l2; try (inversion H; fail). {
      reflexivity.
    }
    rewrite map2_cons_rw.
    inversion H; subst; clear H.
    simpl.
    rewrite IHl1; auto.
  Qed.

  (* ----------------------------- EXISTS ----------------------------- *)

  Lemma Exists_app_or:
    forall A P l1 l2,
    @Exists A P (l1 ++ l2) ->
    Exists P l1 \/ Exists P l2.
  Proof.
    intros.
    repeat rewrite Exists_exists in *.
    destruct H as (a, (Hi, H2)).
    apply in_app_or in Hi.
    destruct Hi; eauto.
  Qed.

  Lemma Exists_app_l:
    forall A P l1 l2, 
    @Exists A P l1 ->
    Exists P (l1 ++ l2).
  Proof.
    intros.
    repeat rewrite Exists_exists in *.
    destruct H as (x, (Hi, Hp)).
    exists x.
    split; auto.
    rewrite in_app_iff.
    auto.
  Qed.

  Lemma Exists_app_r:
    forall A P l1 l2, 
    @Exists A P l2 ->
    Exists P (l1 ++ l2).
  Proof.
    intros.
    repeat rewrite Exists_exists in *.
    destruct H as (x, (Hi, Hp)).
    exists x.
    split; auto.
    rewrite in_app_iff.
    auto.
  Qed.

  (* ------------------------------- NODUP ------------------------------ *)

  Lemma no_dup_inv_app_in:
    forall A l1 l2,
    @NoDup A (l1 ++ l2) ->
    forall a,
    List.In a (l1 ++ l2) ->
    (List.In a l1 /\ ~ List.In a l2) \/
    (~ List.In a l1 /\ List.In a l2).
  Proof.
    induction l1; intros. {
      simpl in *.
      right.
      auto.
    }
    simpl in *.
    inversion H; subst; clear H.
    destruct H0 as [?|Hi]. {
      subst.
      left.
      split; auto.
      intros N.
      contradict H3.
      apply in_app_iff.
      auto.
    }
    apply IHl1 with (a:=a0) in H4; auto.
    destruct H4 as [(Ha,Hb)|(Ha,Hb)]; auto.
    right.
    split. {
      intros N.
      destruct N as [N|N]. {
        subst.
        contradiction.
      }
      contradiction.
    }
    assumption.
  Qed.

  Lemma no_dup_app:
    forall A l1 l2,
    @NoDup A l1 ->
    NoDup l2 ->
    (forall x, List.In x l1 -> List.In x l2 -> False) ->
    NoDup (l1 ++ l2). 
  Proof.
    induction l1; intros. {
      simpl.
      assumption.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl1 in H0; auto. {
      apply NoDup_cons; auto.
      intros N.
      apply no_dup_inv_app_in in N; auto.
      destruct N as [(N1,N2)|(N1,N2)]; try contradiction.
      eapply H1; eauto using in_eq.
    }
    intros.
    eapply H1; eauto using in_cons.
  Qed.

  Lemma no_dup_map_pair:
    forall A B l n,
    @NoDup B l ->
    NoDup (map (@pair A B n) l).
  Proof.
    induction l; intros. {
      apply NoDup_nil.
    }
    simpl.
    inversion H; subst; clear H.
    apply IHl with (n:=n) in H3.
    apply NoDup_cons; auto.
    intros N.
    apply in_map_iff in N.
    destruct N as (x, (R, Hi)).
    inversion R; subst; clear R.
    contradiction.
  Qed.

End Ops.

Section filter.
  (* ------------------------------- FILTER ----------------------- *)
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

