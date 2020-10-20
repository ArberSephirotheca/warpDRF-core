Require Import Coq.Classes.RelationPairs.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Require Import RangeList.
Require Import NExp.
Require Import Tictac.
Require Import Util.

Section Defs.
  Definition range := (nexp * nexp) % type.

  Inductive RList: range -> list nat -> Prop :=
  | r_list_def:
    forall e1 e2 n1 n2 l,
    NStep e1 n1 ->
    NStep e2 n2 ->
    RangeList n1 n2 l ->
    RList (e1, e2) l.

  Definition r_subst x v (r:range) :=
  let (n1, n2) := r in
  (n_subst x v n1, n_subst x v n2).

  Definition r_list (r:range) :=
    let (e1, e2) := r in
    match n_step e1, n_step e2 with
    | Some n1, Some n2 => Some (range_list n1 n2)
    | _, _ => None
    end.

  Lemma r_list_to_prop:
    forall r l,
    r_list r = Some l ->
    RList r l.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    destruct (n_step e1) eqn:He1. {
      destruct (n_step e2) eqn:He2. {
        apply n_step_to_prop in He1.
        apply n_step_to_prop in He2.
        inversion H; subst; clear H.
        remember (range_list _ _).
        symmetry in Heql.
        apply range_list_to_prop in Heql.
        eauto using r_list_def.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Lemma prop_to_r_list:
    forall r l,
    RList r l ->
    r_list r = Some l.
  Proof.
    intros.
    destruct r as (e1, e2).
    inversion H; subst; clear H.
    apply prop_to_n_step in H2.
    apply prop_to_n_step in H3.
    apply prop_to_range_list in H5.
    simpl.
    rewrite H2.
    rewrite H3.
    rewrite H5.
    reflexivity.
  Qed.

  Lemma r_list_fun:
    forall r n1 n2,
    RList r n1 ->
    RList r n2 ->
    n1 = n2.
  Proof.
    intros.
    apply prop_to_r_list in H.
    apply prop_to_r_list in H0.
    rewrite H in *.
    inversion H0.
    auto.
  Qed.

  Lemma r_list_to_range_list:
    forall n1 n2 l,
    RList (NNum n1, NNum n2) l ->
    l = range_list n1 n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H2; subst.
    inversion H3; subst; clear H2 H3.
    apply prop_to_range_list in H5.
    auto.
  Qed.


  Lemma r_list_range_list:
    forall n1 n2,
    RList (NNum n1, NNum n2) (range_list n1 n2).
  Proof.
    intros.
    remember (range_list _ _).
    apply r_list_def with (n1:=n1) (n2:=n2); auto using n_step_num.
    apply range_list_to_prop.
    auto.
  Qed.

  Lemma r_list_cons:
    forall e1 e2 n1 n2 l,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RList (NNum (S n1), NNum n2) l ->
    RList (e1, e2) (n1 :: l).
  Proof.
    intros.
    apply r_list_to_range_list in H2.
    symmetry in H2.
    assert (Hx := r_list_range_list n1 n2).
    eapply r_list_def; eauto.
    apply range_list_cons; auto.
    rewrite <- H2.
    apply range_list_to_prop.
    reflexivity.
  Qed.

  Inductive RTypes l : range -> Prop :=
  | r_types_def:
    forall n1 n2,
    NTypes l n1 ->
    NTypes l n2 ->
    RTypes l (n1, n2).

  Lemma r_progress:
    forall r,
    RTypes [] r ->
    exists l, RList r l.
  Proof.
    intros.
    destruct r as (e1, e2).
    inversion H; subst; clear H.
    destruct (n_progress e1) as (n1, Hn1); auto.
    destruct (n_progress e2) as (n2, Hn2); auto.
    destruct (range_list_progress n1 n2) as (l, Hr).
    exists l.
    eauto using r_list_def.
  Qed.

  Lemma r_subst_subst_neq_2:
    forall x y z n e,
    y <> z ->
    x <> z ->
    r_subst x (NVar y) (r_subst z (NNum n) e)
    =
    r_subst z (NNum n) (r_subst x (NVar y) e).
  Proof.
    intros.
    destruct e.
    simpl.
    repeat rewrite n_subst_subst_neq_2; auto.
  Qed.

  Lemma r_subst_subst_neq_3:
    forall e x y v1 v2,
    x <> y ->
    ~ NFree v1 y ->
    ~ NFree v2 x ->
    r_subst x v1 (r_subst y v2 e)
    =
    r_subst y v2 (r_subst x v1 e).
  Proof.
    intros (e1, e2); intros.
    simpl.
    rewrite n_subst_subst_neq_3; auto.
    rewrite n_subst_subst_neq_3 with (e:=e2); auto.
  Qed.

  Lemma r_subst_subst_eq:
    forall x n1 n2 r,
    r_subst x (NNum n1) (r_subst x (NNum n2) r) = r_subst x (NNum n2) r.
  Proof.
    intros.
    destruct r; simpl.
    repeat rewrite n_subst_subst_eq.
    reflexivity.
  Qed.

  Lemma r_subst_subst_neq:
    forall x y n1 n2 r,
    x <> y ->
    r_subst x (NNum n1) (r_subst y (NNum n2) r) =
    r_subst y (NNum n2) (r_subst x (NNum n1) r).
  Proof.
    destruct r; simpl; intros.
    rewrite n_subst_subst_neq; auto.
    remember (n_subst y _ (n_subst x _ n0)) as a.
    symmetry in Heqa.
    rewrite n_subst_subst_neq in Heqa; auto.
    subst.
    reflexivity.
  Qed.

  Lemma r_subst_subst_eq_2:
    forall x r v e,
    ~ NFree v x ->
    r_subst x e (r_subst x v r) = r_subst x v r.
  Proof.
    intros.
    destruct r.
    simpl in *.
    rewrite n_subst_subst_eq_2; auto.
    rewrite n_subst_subst_eq_2; auto.
  Qed.

  Definition RFree r x :=
    match r with
    | (e1, e2) => NFree e1 x \/ NFree e2 x
    end.

  Lemma r_list_to_not_free:
    forall r l,
    RList r l ->
    forall x,
    ~ RFree r x.
  Proof.
    intros.
    inversion H; subst; clear H.
    intros N.
    inversion N; subst; clear N.
    - apply n_step_to_not_free with (x:=x) in H0.
      contradiction.
    - apply n_step_to_not_free with (x:=x) in H1.
      contradiction.
  Qed.
(*
  Lemma r_not_free_to_n_free:
    forall x n1 n2,
    ~ RFree (n1, n2) x ->
    ~ NFree n1 x /\ ~ NFree n2 x.
  Proof.
    intros.
    split; intros N.
    - contradict H.
      auto using r_in_l.
    - contradict H.
      auto using r_in_r.
  Qed.
*)
  Lemma r_subst_not_free:
    forall x v r,
    ~ RFree r x ->
    r_subst x v r = r.
  Proof.
    intros.
    destruct r as (n1, n2).
    simpl in *.
    rewrite n_subst_not_free with (v:=v); auto.
    rewrite n_subst_not_free with (v:=v); auto.
  Qed.

  Lemma r_subst_subst_trans:
    forall e x v y,
    ~ RFree e x ->
    r_subst x v (r_subst y (NVar x) e) = r_subst y v e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    rewrite n_subst_subst_trans; auto.
    rewrite n_subst_subst_trans; auto.
  Qed.

  Lemma r_free_subst_neq:
    forall e x y v,
    RFree (r_subst y v e) x ->
    ~ NFree v x ->
    RFree e x.
  Proof.
    intros.
    destruct e.
    simpl in *.
    destruct H; eauto using n_free_subst_neq.
  Qed.

  Lemma r_list_no_dup:
    forall l r,
    RList r l ->
    NoDup l.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using range_list_to_no_dup.
  Qed.

  Lemma r_free_subst_eq:
    forall x y e,
    ~ RFree e x ->
    RFree (r_subst y (NVar x) e) x ->
    RFree e y.
  Proof.
    intros x y (nx, ny); simpl in *; intros.
    destruct H0.
    - left.
      eauto using n_free_subst_eq.
    - right.
      eauto using n_free_subst_eq.
  Qed.

  (* ------------------------ RSTEP --------------------------- *)

  Lemma eq_r_list_subst_proper:
    forall x v v' e n, 
    NEq v v' ->
    RList (r_subst x v e) n ->
    RList (r_subst x v' e) n.
  Proof.
    intros.
    destruct e as (e1, e2).
    simpl in *.
    inversion H0; subst; clear H0.
    eapply r_list_def; eauto.
    - rewrite <- H.
      assumption.
    - rewrite <- H.
      assumption.
  Qed.

  Import Morphisms.

  Global Instance n_eq_proper_4: Proper (eq ==> NEq ==> eq ==> NEq * NEq ) r_subst.
  Proof.
    unfold Proper, respectful, RelCompFun, RelProd.
    split; intros; subst; unfold RelCompFun.
    - destruct y1.
      simpl in *.
      rewrite H0.
      reflexivity.
    - destruct y1.
      simpl.
      rewrite H0.
      reflexivity.
  Qed.

  (* ------------------ ABSTRACTION OF RANGE ------------------------- *)


  Inductive RStep : range -> nat -> range -> Prop :=
  | r_step_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RStep (e1, e2) n1 (NNum (S n1), NNum n2).

  Inductive RFirst : range -> nat -> Prop :=
  | r_first_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    RFirst (e1, e2) n1.

  Lemma r_first_refl_l:
    forall e n,
    ~ RFirst (e, e) n.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N.
    assert (n2 = n) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_step_to_first:
    forall r n r',
    RStep r n r' ->
    RFirst r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using r_first_def.
  Qed.

  Lemma r_step_refl_l:
    forall e n r,
    ~ RStep (e, e) n r.
  Proof.
    intros.
    intros N.
    apply r_step_to_first in N.
    apply r_first_refl_l in N.
    assumption.
  Qed.

  Inductive ROne : range -> nat -> Prop :=
  | r_one_def:
    forall e1 e2 n,
    NStep e1 n ->
    NStep e2 (S n) ->
    ROne (e1, e2) n.

  Lemma r_one_to_first:
    forall r n,
    ROne r n ->
    RFirst r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_first_def; eauto.
  Qed.

  Lemma r_one_refl_l:
    forall e n,
    ~ ROne (e, e) n.
  Proof.
    intros.
    intros N.
    apply r_one_to_first in N.
    apply r_first_refl_l in N.
    assumption.
  Qed.

  Definition RHasNext (r:range) :=
    exists n, RFirst r n.

  Inductive RPick : range -> nat -> Prop :=
  | r_pick_def:
    forall e1 e2 n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n < n2 ->
    RPick (e1, e2) n.

  Lemma r_first_to_pick:
    forall r n,
    RFirst r n ->
    RPick r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_pick_def; eauto.
  Qed.

  Inductive RPick2 : range -> nat -> Prop :=
  | r_pick2_def:
    forall e1 e2 n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 <= n ->
    S n < n2 ->
    RPick2 (e1, e2) n.

  Lemma r_first_to_has_next:
    forall r n,
    RFirst r n ->
    RHasNext r.
  Proof.
    intros.
    unfold RHasNext.
    eauto.
  Qed.

  Lemma r_one_to_has_next:
    forall r n,
    ROne r n ->
    RHasNext r.
  Proof.
    intros.
    apply r_one_to_first in H.
    eauto using r_first_to_has_next.
  Qed.

  Lemma r_step_to_has_next:
    forall r n r',
    RStep r n r' ->
    RHasNext r.
  Proof.
    intros.
    apply r_step_to_first in H.
    eauto using r_first_to_has_next.
  Qed.

  Lemma r_first_fun:
    forall r n1 n2,
    RFirst r n1 ->
    RFirst r n2 ->
    n1 = n2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n1 = n2) by eauto using n_step_fun.
    assert (n3 = n4) by eauto using n_step_fun.
    subst.
    reflexivity.
  Qed.

  Lemma r_step_first_fun:
    forall r n1 r' n2,
    RStep r n1 r' ->
    RFirst r n2 ->
    n1 = n2.
  Proof.
    intros.
    apply r_step_to_first in H.
    eauto using r_first_fun.
  Qed.

  Lemma r_first_inv_eq:
    forall n e n',
    RFirst (NNum n, e) n' ->
    n = n'.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using n_step_fun, n_step_num.
  Qed.
 
  Inductive REmpty : range -> Prop :=
  | r_empty_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    REmpty (e1, e2).

  Lemma r_empty_eq:
    forall n,
    REmpty (NNum n, NNum n).
  Proof.
    intros.
    eapply r_empty_def; eauto using n_step_num.
  Qed.

  Inductive RLast : range -> nat -> Prop :=
  | r_last_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 (S n2) ->
    n1 < S n2 ->
    RLast (e1, e2) n2.

  Lemma r_step_last:
    forall r1 n1 n r2,
    RStep r1 n1 r2 ->
    RLast r2 n ->
    RLast r1 n.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
    assert (n2 = S n) by eauto using n_step_num, n_step_fun.
    subst.
    eapply r_last_def; eauto.
  Qed.

  Lemma r_one_to_last:
    forall r n,
    ROne r n ->
    RLast r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_last_def; eauto.
  Qed.

  Lemma r_step_to_pick:
    forall r n r',
    RStep r n r' ->
    RPick r n.
  Proof.
    intros.
    eauto using r_step_to_first, r_first_to_pick.
  Qed.

  Lemma r_step_pick_rev:
    forall r n' r' n,
    RStep r n' r' ->
    RPick r' n ->
    RPick r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n1 = S n') by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_step_pick2_rev:
    forall r n' r' n,
    RStep r n' r' ->
    RPick2 r' n ->
    RPick2 r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n1 = S n') by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply r_pick2_def; eauto.
    lia.
  Qed.

  Lemma r_step_unfold:
    forall r1 n r2,
    RStep r1 n r2 ->
    REmpty r2 \/ RHasNext r2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H2; subst; clear H2. {
      left.
      auto using r_empty_eq.
    }
    right.
    unfold RHasNext.
    exists (S n).
    eapply r_first_def; eauto using n_step_num.
    lia.
  Qed.

  Lemma r_empty_to_has_next:
    forall r,
    REmpty r ->
    ~ RHasNext r.
  Proof.
    intros.
    inversion H; subst; clear H.
    intros N.
    destruct N as (x, N).
    inversion N; subst; clear N.
    assert (x = n1) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_has_next_to_empty:
    forall r,
    RHasNext r ->
    ~ REmpty r.
  Proof.
    intros.
    destruct H as (n, H).
    inversion H; subst; clear H.
    intros N.
    inversion N; subst; clear N.
    assert (n = n1) by eauto using n_step_fun.
    assert (n0 = n2) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_last_to_pick:
    forall r n,
    RLast r n ->
    RPick r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_last_to_eq:
    forall e1 e2 n,
    RLast (e1, e2) n ->
    NStep (NBin NMinus e2 (NNum 1)) n.
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (R1: n = eval_nbin NMinus (S n) 1). {
      simpl.
      lia.
    }
    rewrite R1.
    apply n_step_bin; auto.
    auto using n_step_num.
  Qed.

  Lemma r_first_to_eq:
    forall e1 e2 n,
    RFirst (e1, e2) n ->
    NStep e1 n.
  Proof.
    intros.
    inversion H; subst; clear H.
    assumption.
  Qed.

  Lemma r_step_inv_next_eq:
    forall r n r' n',
    RStep r n r' ->
    RFirst r' n' ->
    n' = S n.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (n' = S n) by eauto using n_step_num, n_step_fun.
    auto.
  Qed.

  Lemma r_step_to_pick2:
    forall r n r',
    RStep r n r' ->
    RHasNext r' ->
    RPick2 r n.
  Proof.
    intros.
    destruct r as (e1, e2).
    inversion H; subst; clear H.
    destruct H0 as (n', Hx).
    inversion Hx; subst; clear Hx.
    assert (n' = S n) by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply r_pick2_def; eauto.
  Qed.

  Lemma r_one_to_pick:
    forall r n,
    ROne r n ->
    RPick r n.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply r_pick_def; eauto.
  Qed.


  Lemma r_last_proper:
    forall e1 e1' e2 e2' n,
    NEq e1 e1' ->
    NEq e2 e2' ->
    RLast (e1, e2) n ->
    RLast (e1', e2') n.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    rewrite H in H4.
    rewrite H0 in H5.
    eauto using r_last_def.
  Qed.

  Definition RDefined (r:range) :=
    let (e1, e2) := r in
    (exists n1, NStep e1 n1) /\ (exists n2, NStep e2 n2).

  Lemma r_has_next_to_last:
    forall r,
    RHasNext r ->
    exists m, RLast r m.
  Proof.
    intros.
    destruct H as(n, Hr).
    invc Hr.
    destruct n2. {
      lia.
    }
    eexists.
    eapply r_last_def; eauto.
  Qed.

  Lemma r_has_next_to_first:
    forall r,
    RHasNext r ->
    exists m, RFirst r m.
  Proof.
    intros.
    destruct H as (n, H).
    eauto.
  Qed.

  Lemma n_eq_def:
    forall e1 e2 n,
    NStep e1 n ->
    NStep e2 n ->
    NEq e1 e2.
  Proof.
    intros.
    split; intros;
      assert (n0 = n) by eauto using n_step_fun; subst; auto. 
  Qed.

  Global Instance n_eq_proper_5: Proper (NEq * NEq ==> eq ==> iff) RLast.
  Proof.
    unfold Proper, respectful, RelCompFun, RelProd.
    intros (e1,e2) (e1', e2') (Ha, Hb) n' n ?.
    subst.
    unfold RelCompFun in *.
    simpl in *.
    split; intros Hi.
    - eauto using r_last_proper.
    - symmetry in Ha.
      symmetry in Hb.
      eauto using r_last_proper.
  Qed.
 
  Lemma r_pick_inv_first:
    forall e1 e2 n,
    RPick (e1, e2) n ->
    RFirst (e1, e2) n \/ RPick (NBin NPlus (NNum 1) e1, e2) n.
  Proof.
    intros.
    invc H.
    assert (X: n = n1 \/ (S n1 <= n < n2)) by lia.
    destruct X as [?|X]. {
      subst.
      left.
      eapply r_first_def; eauto.
      lia.
    }
    right.
    eapply r_pick_def; eauto.
    assert (r1: S n1 = 1 + n1) by lia.
    rewrite r1.
    apply n_step_plus; auto using n_step_num.
  Qed.
 
  (* ------------------------------------ RPRED ------------------- *)

  Inductive RPred (P:nat -> nat -> Prop): range -> Prop :=
  | r_pred_def:
    forall e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    P n1 n2 ->
    RPred P (e1, e2).

  Lemma r_pred_eq:
    forall (P: nat -> nat -> Prop) n1 n2,
    P n1 n2 ->
    RPred P (NNum n1, NNum n2).
  Proof.
    intros.
    eapply r_pred_def; eauto using n_step_num.
  Qed.
 (*
  Lemma r_subst_not_in_rw:
    forall x e,
    ~ RFree e x ->
    forall v,
    r_subst x v e = e.
  Proof.
    intros.
    destruct e as (e1, e2).
    simpl.
    apply not_r_in_to_in in H.
    destruct H.
    rewrite n_subst_not_in_rw; auto.
    rewrite n_subst_not_in_rw; auto.
  Qed.*)

  Lemma r_subst_subst_eq_1:
    forall e1 e2 x r,
    r_subst x e1 (r_subst x e2 r)
    =
    r_subst x (n_subst x e1 e2) r.
  Proof.
    intros.
    destruct r as (r1, r2).
    simpl.
    rewrite n_subst_subst_eq_1.
    rewrite n_subst_subst_eq_1.
    reflexivity.
  Qed.

  Lemma r_free_inv_subst_eq:
    forall x r e,
    RFree (r_subst x e r) x ->
    NFree e x.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    destruct H; apply n_free_inv_subst_eq in H; auto.
  Qed.

  Lemma r_subst_subst_neq_4:
    forall r e1 e2 x y,
    NClosed e1 -> 
    x <> y ->
    r_subst y e1 (r_subst x e2 r) =
    r_subst y e1 (r_subst x (n_subst y e1 e2) r).
  Proof.
    intros (e1', e2') e1 e2 x y Hc Hn.
    simpl.
    apply eq_pair_def.
    - rewrite n_subst_subst_neq_4; auto.
    - rewrite n_subst_subst_neq_4; auto.
  Qed.

  Lemma r_subst_subst_neq_5:
    forall r x y e1 e2,
    NClosed e1 ->
    x <> y ->
    r_subst y e1 (r_subst x e2 r) =
    r_subst x (n_subst y e1 e2) (r_subst y e1 r).
  Proof.
    intros (e1', e2') x y e1 e2 Hc Hn.
    simpl.
    rewrite n_subst_subst_neq_5; auto.
    rewrite n_subst_subst_neq_5 with (e3:=e2'); auto.
  Qed.
End Defs.

Module RExpNotations.
  Import NExpNotations.
  Notation "x '∈'  r " := (RPick r x) (at level 30, only printing) : exp_scope.
  Notation "r [ x := v ]" := (r_subst x v r) (at level 30, only printing) : exp_scope. 
End RExpNotations.