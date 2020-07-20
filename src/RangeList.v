Set Implicit Arguments.

Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.omega.Omega.

Lemma map_rw_func:
  forall {A} {B} (f1:A -> B) f2 l,
  (forall x, List.In x l -> f1 x = f2 x) ->
  map f1 l = map f2 l.
Proof.
  induction l; intros; auto.
  simpl in *.
  rewrite IHl; auto.
  rewrite H; auto.
Qed.

Section Defs.
  Variable A:Type.
  (* XXX: use Coq.Lists.List.seq instead of range_list *)
  Inductive InvRangeList : nat -> nat -> list nat -> Prop :=
  | inv_range_list_nil:
    forall n m,
    n >= m ->
    InvRangeList n m []
  | inv_range_list_cons:
    forall n m l,
    n <= m ->
    InvRangeList n m l ->
    InvRangeList n (S m) (m :: l).

  Inductive RangeList : nat -> nat -> list nat -> Prop :=
  | range_list_nil:
    forall low high,
    low >= high ->
    RangeList low high []
  | range_list_cons:
    forall low high l,
    low < high ->
    RangeList (S low) high l ->
    RangeList low high (low::l). 

  Section range_list_fun.
    Import Omega.
    Lemma range_list_fun:
      forall l1 n1 n2 l2,
      RangeList n1 n2 l1 ->
      RangeList n1 n2 l2 ->
      l1 = l2.
    Proof.
      induction l1; intros; inversion H; subst; clear H. {
        inversion H0; subst; clear H0. {
          reflexivity.
        }
        omega.
      }
      inversion H0; subst; clear H0. {
        omega.
      }
      erewrite IHl1; eauto.
    Qed.

    Lemma range_list_inv_1:
      forall n,
      RangeList 0 n [] ->
      n = 0.
    Proof.
      intros.
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_2:
      forall l n,
      RangeList n 0 l ->
      l = [].
    Proof.
      destruct l; intros. {
        reflexivity.
      }
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_3:
      forall l n1 n2,
      RangeList n1 n2 l ->
      n1 >= n2 ->
      l = [].
    Proof.
      induction l; intros; auto.
      inversion H; subst; clear H.
      omega.
    Qed.

    Lemma range_list_inv_4:
      forall n1 n2,
      RangeList n1 n2 [] ->
      n1 >= n2.
    Proof.
      intros.
      inversion H; subst; clear H.
      assumption.
    Qed.

    Lemma range_list_inv_5:
      forall n1 n2 n3 l,
      RangeList n1 n2 (n3 :: l) ->
      n3 = n1.
    Proof.
      intros.
      inversion H; subst; clear H.
      reflexivity.
    Qed.

    Lemma range_list_inv_succ_nil:
      forall n1 n2,
      RangeList (S n1) (S n2) [] ->
      RangeList n1 n2 [].
    Proof.
      intros.
      inversion H; subst; clear H.
      assert (n1 >= n2) by auto with *.
      apply range_list_nil.
      assumption.
    Qed.

    Lemma range_list_inv_cons:
      forall l n1 n2 a,
      RangeList n1 (S n2) (l ++ [a]) ->
      a = n2.
    Proof.
      induction l; simpl; intros. {
        inversion H; subst; clear H.
        apply range_list_inv_succ_nil in H5.
        inversion H5; subst; clear H5.
        omega.
      }
      inversion H; subst; clear H.
      apply IHl in H5.
      subst.
      reflexivity.
    Qed.

    Lemma range_list_inv_cons_2:
      forall l n1 n2,
      RangeList n1 (S n2) (l ++ [n2]) ->
      RangeList n1 n2 l /\ n1 <= n2.
    Proof.
      induction l; simpl; intros;
      inversion H; subst; clear H.
      - split; auto using le_n.
        apply range_list_nil.
        apply le_n.
      - inversion H4; subst; clear H4. {
          apply range_list_inv_3 in H5; auto.
          destruct l; inversion H5.
        }
        apply IHl in H5.
        destruct H5.
        split. {
          apply range_list_cons; auto.
        }
        omega.
    Qed.

    Lemma range_list_succ:
      forall l n1 n2,
      n1 <= n2 ->
      RangeList n1 n2 l ->
      RangeList n1 (S n2) (l ++ [n2]).
    Proof.
      induction l; intros. {
        apply range_list_inv_4 in H0.
        assert (n1 = n2) by omega.
        subst.
        apply range_list_cons.
        + omega.
        + apply range_list_nil.
          omega.
      }
      simpl.
      assert (a = n1) by eauto using range_list_inv_5.
      subst.
      apply range_list_cons.
      + omega.
      + inversion H0; subst; clear H0.
        apply IHl in H5; auto.
    Qed.

    Lemma range_list_inv_spec:
      forall l n1 n2,
      RangeList n1 n2 (rev l) <-> InvRangeList n1 n2 l.
    Proof.
      induction l; intros. {
        simpl; split; intros.
        + inversion H; subst; clear H.
          apply inv_range_list_nil.
          assumption.
        + inversion H; subst; clear H.
          apply range_list_nil.
          assumption.
      }
      simpl.
      split.
      - intros.
        destruct n2. {
          apply range_list_inv_2 in H.
          destruct (rev l); inversion H.
        }
        assert (a = n2) by eauto using range_list_inv_cons. 
        subst.
        apply range_list_inv_cons_2 in H.
        destruct H as (Hr, Hle).
        apply inv_range_list_cons; auto.
        apply IHl.
        assumption.
      - intros.
        assert (S a = n2). {
          inversion H; subst; clear H.
          apply IHl in H5.
          reflexivity.
        }
        subst.
        inversion H; subst; clear H.
        apply IHl in H4.
        apply range_list_succ; auto.
    Qed.

    Fixpoint range_list_aux fuel n1 :=
      match fuel with
      | O => []
      | S n => n1 :: range_list_aux n (S n1)
      end.

    Definition range_list n1 n2 := range_list_aux (n2 - n1) n1.

    Goal range_list 0 2 = [0; 1]. auto. Qed.
    Goal RangeList 0 2 [0; 1].
    Proof.
      apply range_list_cons; auto.
      apply range_list_cons; auto.
      apply range_list_nil; auto.
    Qed.


    Goal range_list 0 10 = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]. auto. Qed.
    Goal range_list 1 0 = []. auto. Qed.
    Goal RangeList 1 0 [].
    Proof.
      apply range_list_nil; auto.
    Qed.

    Goal range_list 2 1 = []. auto. Qed.
    Goal range_list 10 10 = []. auto. Qed.


    Lemma range_list_r_0:
      forall n,
      RangeList n 0 [].
    Proof.
      intros.
      apply range_list_nil.
      auto with *.
    Qed.

    Lemma range_list_aux_inv_nil:
      forall n1 n2,
      range_list_aux n1 n2 = [] ->
      n1 = 0.
    Proof.
      intros; destruct n1. {
        reflexivity.
      }
      simpl in *.
      inversion H.
    Qed.

    Lemma range_list_aux_inv_cons:
      forall n1 n2 x l,
      range_list_aux n1 n2 = x :: l ->
      x = n2 /\ exists n, n1 = S n /\ range_list_aux n (S n2) = l.
    Proof.
      induction n1; intros. {
        simpl in *.
        inversion H.
      }
      inversion H.
      destruct l. {
        apply range_list_aux_inv_nil in H2.
        subst.
        eauto.
      }
      apply IHn1 in H2.
      subst.
      destruct H2 as (?, (?, (?, ?))).
      subst.
      eauto.
    Qed.

    Lemma range_list_to_prop:
      forall l n1 n2,
      range_list n1 n2 = l ->
      RangeList n1 n2 l.
    Proof.
      induction l; intros. {
        unfold range_list in *.
        apply range_list_aux_inv_nil in H.
        apply Nat.sub_0_le in H.
        apply range_list_nil.
        auto.
      }
      unfold range_list in H.
      apply range_list_aux_inv_cons in H.
      destruct H as (?, (?, (?, Hx))).
      subst.
      apply range_list_cons; auto with *.
      apply IHl.
      unfold range_list.
      assert (R: x = n2 - S n1) by omega.
      rewrite R.
      reflexivity.
    Qed.

    Lemma prop_to_range_list:
      forall l n1 n2,
      RangeList n1 n2 l ->
      range_list n1 n2 = l.
    Proof.
      induction l; intros;
        inversion H; subst; clear H. {
        apply Nat.sub_0_le in H0.
        unfold range_list.
        rewrite H0.
        reflexivity.
      }
      apply IHl in H5.
      unfold range_list in *.
      subst.
      destruct (n2 - a) eqn:R. {
        omega.
      }
      simpl.
      assert (R2: n2 - S a = n) by omega.
      rewrite R2.
      reflexivity.
    Qed.

  End range_list_fun.

  Lemma inv_range_list_progress:
    forall n1 n2, exists l, InvRangeList n1 n2 l.
  Proof.
    intros n1 n2; generalize dependent n1.
    induction n2; intros.
    - exists []. apply inv_range_list_nil.
      auto with *.
    - destruct (Compare_dec.le_ge_dec n1 (S n2)). {
        apply Lt.le_lt_or_eq in l.
        destruct l. {
          assert (n1 <= n2) by auto with *.
          destruct (IHn2 n1) as (l, IHl).
          exists (n2::l).
          auto using inv_range_list_cons.
        }
        subst.
        exists [].
        apply inv_range_list_nil.
        apply le_n.
      }
      exists [].
      apply inv_range_list_nil.
      assumption.
  Qed.

  Lemma range_list_progress:
    forall n1 n2, exists l, RangeList n1 n2 l.
  Proof.
    intros.
    destruct (inv_range_list_progress n1 n2) as (l, Hinv).
    exists (rev l).
    apply range_list_inv_spec.
    assumption.
  Qed.


  Lemma range_list_inv_in:
    forall l n1 n2 n,
    RangeList n1 n2 l ->
    List.In n l ->
    n1 <= n /\ n < n2. 
  Proof.
    induction l; intros. {
      contradiction.
    }
    inversion H0; subst; clear H0;
        inversion H; subst; clear H. {
      auto with *.
    }
    eapply IHl in H6; eauto.
    auto with *.
  Qed.

  Lemma range_list_inv_lt:
    forall l n1 n2 n,
    RangeList n1 n2 l ->
    n1 <= n ->
    n < n2 ->
    List.In n l.
  Proof.
    Import Omega.
    induction l; intros. {
      inversion H.
      subst.
      omega.
    }
    simpl.
    inversion H; subst; clear H.
    assert (Hx: a < n \/ a = n) by omega.
    destruct Hx. {
      eapply IHl in H7; eauto.
    }
    auto.
  Qed.

  Lemma range_list_inv_nil:
    forall n1 n2,
    RangeList n1 n2 [] ->
    n1 >= n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    auto.
  Qed.

  Lemma range_list_inv:
    forall l n1 n2,
    RangeList n1 n2 l ->
    (l = [] /\ n1 >= n2) \/
    (l <> [] /\ forall n, n1 <= n /\ n < n2 <-> List.In n l).
  Proof.
    intros.
    destruct l. {
      left.
      apply range_list_inv_nil in H.
      auto.
    }
    right.
    split. {
      intros N; inversion N.
    }
    intros n0.
    split; intros X. {
      destruct X; eauto using range_list_inv_lt.
    }
    eauto using range_list_inv_in.
  Qed.

  Lemma range_list_in:
    forall n1 n n2, 
    n1 <= n < n2 ->
    In n (range_list n1 n2).
  Proof.
    intros.
    remember (range_list _ _).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    apply range_list_inv_lt with (n1:=n1) (n2:=n2); auto with *.
  Qed.

  Lemma range_list_inv_in_2:
    forall n1 n n2, 
    In n (range_list n1 n2) ->
    n1 <= n < n2.
  Proof.
    intros.
    remember (range_list _ _).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    apply range_list_inv_in with (n:=n) in Heql; auto.
  Qed.

  Lemma range_list_in_iff:
    forall n1 n n2, 
    In n (range_list n1 n2) <-> n1 <= n < n2.
  Proof.
    split; intros; auto using range_list_in, range_list_inv_in_2.
  Qed.

  Lemma range_list_to_no_dup:
    forall l n1 n2,
    RangeList n1 n2 l ->
    NoDup l.
  Proof.
    induction l; intros. {
      apply NoDup_nil.
    }
    inversion H; subst; clear H.
    apply NoDup_cons; auto. {
      intros N.
      apply range_list_inv_in with (n:=a) in H5; auto.
      omega.
    }
    eauto.
  Qed.

  Lemma range_list_no_dup:
    forall n1 n2,
    NoDup (range_list n1 n2).
  Proof.
    intros.
    remember (range_list n1 n2).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    eauto using range_list_to_no_dup.
  Qed.

  Lemma range_list_length:
    forall l n1 n2,
    RangeList n1 n2 l ->
    Datatypes.length l = n2 - n1.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
      simpl.
      assert (Hle: n2 <= n1) by auto with *.
      apply Nat.sub_0_le in Hle.
      rewrite Hle.
      reflexivity.
    }
    inversion H; subst; clear H.
    apply IHl in H5.
    simpl.
    auto with *.
  Qed.

  Lemma range_list_fun_length:
    forall n1 n2,
    Datatypes.length (range_list n1 n2) = n2 - n1.
  Proof.
    intros.
    remember (range_list n1 n2).
    symmetry in Heql.
    apply range_list_to_prop in Heql.
    auto using range_list_length.
  Qed.

  Lemma range_list_not_nil:
    forall n1 n2,
    n1 < n2 ->
    range_list n1 n2 <> [].
  Proof.
    intros.
    intros N.
    apply range_list_to_prop in N.
    inversion N; subst.
    omega.
  Qed.

  Lemma range_list_inv_plus_l_1:
    forall l n1 n2 n3,
    n1 < n2 ->
    RangeList n1 (n2 + n3) l ->
    exists l1 l2,
    l = l1 ++ l2 /\ RangeList n1 n2 l1 /\ RangeList n2 (n2 + n3) l2.
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0.
      omega.
    }
    inversion H0; subst; clear H0.
    inversion H; subst; clear H. {
      simpl.
      exists [a].
      simpl.
      exists (l).
      simpl in *.
      split; auto.
      split; auto using range_list_nil, range_list_cons.
    }
    apply IHl in H6; auto with *; clear IHl.
    destruct H6 as (l1, (l2, (?, (Hr1, Hr2)))).
    subst.
    eexists.
    eexists.
    split.
    2: {
      split; eauto.
      apply range_list_cons; eauto.
    }
    reflexivity.
  Qed.

  Lemma range_list_plus_l_1:
    forall l1 l2 n1 n2 n3,
    n1 < n2 ->
    RangeList n1 n2 l1 ->
    RangeList n2 (n2 + n3) l2 ->
    RangeList n1 (n2 + n3) (l1 ++ l2).
  Proof.
    induction l1; intros; simpl; inversion H0; subst; clear H0. {
      omega.
    }
    inversion H; subst; clear H. {
      assert (l1 = []). {
        eauto using range_list_inv_3 with *.
      }
      subst.
      simpl.
      apply range_list_cons; auto with *.
    }
    apply range_list_cons; auto with *.
  Qed.

  Lemma range_list_spec:
    forall n1 n2,
    RangeList n1 n2 (range_list n1 n2).
  Proof.
    intros.
    apply range_list_to_prop.
    reflexivity.
  Qed.

End Defs.


Section Map.
  Variable A:Type.
  Variable B:Type.
  Inductive Map (P:A->B->Prop): list A -> list B -> Prop :=
  | map_nil:
    Map P [] []
  | map_cons:
    forall v vs k ks,
    P k v ->
    ~ List.In k ks ->
    Map P ks vs ->
    Map P (k::ks) (v::vs).

  Lemma in_map:
    forall P ks vs,
    Map P ks vs ->
    forall k,
    List.In k ks ->
    exists v, List.In (k, v) (combine ks vs).
  Proof.
    intros P ks vs Hm.
    induction Hm; intros. {
      contradiction.
    }
    destruct H1 as [?|Hi]. {
      subst.
      simpl.
      exists v.
      auto.
    }
    apply IHHm in Hi.
    destruct Hi as (v1, Hi).
    simpl.
    eauto.
  Qed.

  Lemma map_to_prop:
    forall P ks vs,
    Map P ks vs ->
    forall k v,
    List.In (k,v) (combine ks vs) ->
    P k v.
  Proof.
    intros P ks vs Hm.
    induction Hm; intros. {
      contradiction.
    }
    simpl in *.
    destruct H1 as [R|Hi]. {
      inversion R; subst; clear R.
      assumption.
    }
    auto.
  Qed.

  Lemma map_def:
    forall P ks,
    NoDup ks ->
    (forall k, List.In k ks -> exists v, P k v) ->
    exists vs, Map P ks vs.
  Proof.
    induction ks; intros. {
      exists [].
      apply map_nil.
    }
    inversion H; subst; clear H.
    assert (Hi := H0 a).
    destruct Hi as (v, Pk); auto using in_eq.
    destruct IHks as (vs, mp); auto using in_cons.
    exists (v::vs).
    eauto using map_cons.
  Qed.

  Lemma map_impl:
    forall (P Q: A -> B -> Prop),
    (forall k v, P k v -> Q k v) ->
    forall ks vs,
    Map P ks vs ->
    Map Q ks vs.
  Proof.
    intros P Q Hincl.
    induction ks; intros. {
      inversion H; subst.
      apply map_nil.
    }
    inversion H; subst; clear H.
    auto using map_cons.
  Qed.

  Lemma map_inv_app:
    forall P l1 l2 l,
    Map P (l1 ++ l2) l ->
    exists l1' l2',
    l = l1' ++ l2' /\
    Map P l1 l1' /\
    Map P l2 l2'.
  Proof.
    induction l1; intros. {
      simpl in *.
      exists [].
      exists l.
      split; auto using map_nil.
    }
    simpl in *.
    inversion H; subst; clear H.
    apply IHl1 in H5.
    destruct H5 as (l1', (l2', (R, (Hm1, Hm2)))).
    subst.
    exists (v :: l1').
    exists l2'.
    repeat split; auto.
    apply map_cons; auto.
    intros N.
    contradict H3.
    apply in_or_app.
    auto.
  Qed.

  Lemma map_app:
    forall P l1 l2 l1' l2',
    Map P l1 l1' ->
    Map P l2 l2' ->
    NoDup (l1 ++ l2) ->
    Map P (l1 ++ l2) (l1' ++ l2').
  Proof.
    induction l1; intros. {
      inversion H; subst; clear H.
      assumption.
    }
    inversion H; subst; clear H.
    simpl in *.
    inversion H1; subst; clear H1.
    eauto using map_cons.
  Qed.

  Lemma map_inv_value:
    forall P ks vs,
    Map P ks vs ->
    forall v,
    List.In v vs ->
    exists k, List.In k ks /\ P k v.
  Proof.
    induction ks; intros; inversion H; subst; clear H. {
      contradiction.
    }
    destruct H0 as [Hi|Hi]. {
      subst.
      eauto using in_eq.
    }
    eapply IHks in H6; eauto.
    destruct H6 as (k, (Hj, Hp)).
    eauto using in_cons.
  Qed.

End Map.

Section MapExtra.
  Lemma map_in_range_list:
    forall {A:Type} (P:nat -> A ->Prop) n1 n2 vs k,
    Map P (range_list n1 n2) vs ->
    n1 <= k < n2 ->
    exists v, P k v /\ List.In v vs.
  Proof.
    intros.
    apply range_list_in_iff in H0.
    eapply in_map in H0; eauto.
    destruct H0 as (v, Hi).
    assert (Hk := Hi).
    apply in_combine_r in Hk.
    eapply map_to_prop in Hi; eauto.
  Qed.

End MapExtra.