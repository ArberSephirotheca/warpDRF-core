Require Import Coq.Classes.RelationPairs.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Require Import NExp.
Require Import Tictac.
Require Import Util.

Section Defs.
  Definition range := (nexp * nexp) % type.

  Definition r_subst x v (r:range) :=
  let (n1, n2) := r in
  (n_subst x v n1, n_subst x v n2).

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
    ~ NFree y v1 ->
    ~ NFree x v2 ->
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
    ~ NFree x v ->
    r_subst x e (r_subst x v r) = r_subst x v r.
  Proof.
    intros.
    destruct r.
    simpl in *.
    rewrite n_subst_subst_eq_2; auto.
    rewrite n_subst_subst_eq_2; auto.
  Qed.

  Definition RFree x r :=
    match r with
    | (e1, e2) => NFree x e1 \/ NFree x e2
    end.

  Lemma r_subst_not_free:
    forall x v r,
    ~ RFree x r ->
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
    ~ RFree x e ->
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
    RFree x (r_subst y v e) ->
    ~ NFree x v ->
    RFree x e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    destruct H; eauto using n_free_subst_neq.
  Qed.

  Lemma r_free_inv_subst:
    forall e x y v,
    RFree x (r_subst y v e) ->
    NFree x v \/
    RFree x e.
  Proof.
    intros.
    destruct e.
    simpl in *.
    destruct H as [H|H]; eapply n_free_inv_subst in H; intuition.
  Qed.

  Lemma r_free_subst_eq:
    forall x y e,
    ~ RFree x e ->
    RFree x (r_subst y (NVar x) e) ->
    RFree y e.
  Proof.
    intros x y (nx, ny); simpl in *; intros.
    destruct H0.
    - left.
      eauto using n_free_subst_eq.
    - right.
      eauto using n_free_subst_eq.
  Qed.

  (* ------------------------ RSTEP --------------------------- *)

  Import Morphisms.

  Variable tid: nat.

  Notation NEq := (NEq tid).

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

  Notation NStep := (NStep tid).

  Inductive RStep : range -> nat -> range -> Prop :=
  | r_step_def:
    forall e1 e2 e3 e4 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    NStep e3 (S n1) ->
    NStep e4 n2 ->
    n1 < n2 ->
    RStep (e1, e2) n1 (e3, e4).

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

  Lemma r_pick2_to_pick:
    forall r n,
    RPick2 r n ->
    RPick r n.
  Proof.
    intros.
    invc H.
    eapply r_pick_def; eauto.
    lia.
  Qed.

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


  (* ------------------------------ RPick --------------------------- *)

  (* ------------------------------ RLast --------------------------- *)
  Lemma r_last_fun:
    forall r n,
    RLast r n ->
    forall n',
    RLast r n' ->
    n' = n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (x: S n = S n') by eauto using n_step_fun.
    invc x.
    reflexivity.
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


  (* ------------------------------------- *)

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
    invc H.
    invc H4. {
      left.
      eapply r_empty_def; eauto.
    }
    right.
    unfold RHasNext.
    exists (S n).
    eapply r_first_def; eauto.
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

  Lemma r_pick_to_has_next:
    forall r n,
    RPick r n ->
    RHasNext r.
  Proof.
    intros.
    invc H.
    apply r_first_to_has_next with (n1).
    eapply r_first_def; eauto with *.
  Qed.

  Lemma r_pick_to_empty:
    forall r n,
    RPick r n ->
    ~ REmpty r.
  Proof.
    intros.
    apply r_has_next_to_empty.
    eauto using r_pick_to_has_next.
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

  Lemma r_one_pick_fun:
    forall r n1 n2,
    ROne r n2 ->
    RPick r n1 ->
    n1 = n2.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n2 = n0) by eauto using n_step_fun.
    assert (n3 = S n2) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_one_fun:
    forall r n1 n2,
    ROne r n1 ->
    ROne r n2 ->
    n1 = n2.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n1 = n2) by eauto using n_step_fun.
    auto.
  Qed.

  Lemma r_one_last_fun:
    forall r n1 n2,
    ROne r n2 ->
    RLast r n1 ->
    n1 = n2.
  Proof.
    intros.
    apply r_one_to_last in H.
    eauto using r_last_fun.
  Qed.

  Definition RDefined (r:range) :=
    let (e1, e2) := r in
    (exists n1, NStep e1 n1) /\ (exists n2, NStep e2 n2).

  (* ------------------------- HAS NEXT ------------------- *)

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

  Lemma r_pick_subst:
    forall x v1 r n,
    RPick (r_subst x v1 r) n ->
    forall v2 m,
    NStep v1 m ->
    NStep v2 m ->
    RPick (r_subst x v2 r) n.
  Proof.
    intros.
    invc H.
    destruct r as (e1', e2').
    simpl in *.
    rename_hyp ((_,_) = _) as Hx.
    invc Hx.
    assert (rx: NEq v1 v2) by eauto using n_eq_def.
    rewrite rx in *.
    eauto using r_pick_def.
  Qed.

  Lemma r_pick2_subst:
    forall x v1 r n,
    RPick2 (r_subst x v1 r) n ->
    forall v2 m,
    NStep v1 m ->
    NStep v2 m ->
    RPick2 (r_subst x v2 r) n.
  Proof.
    intros.
    invc H.
    destruct r as (e1', e2').
    simpl in *.
    rename_hyp ((_,_) = _) as Hx.
    invc Hx.
    assert (rx: NEq v1 v2) by eauto using n_eq_def.
    rewrite rx in *.
    eauto using r_pick2_def.
  Qed.

  Lemma r_step_empty_fun:
    forall r n r' n',
    RStep r n r' ->
    RLast r n' ->
    REmpty r' ->
    n = n'.
  Proof.
    intros.
    invc H.
    invc H0.
    invc H1.
    assert (n = n1) by eauto using n_step_fun.
    assert (S n' = n2) by eauto using n_step_fun.
    assert (n0 = S n) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_step_last_2:
    forall r n r' n',
    RStep r n r' ->
    RLast r n' ->
    RHasNext r' ->
    RLast r' n'.
  Proof.
    intros.
    apply r_has_next_to_last in H1.
    destruct H1 as (n'', Hl).
    assert (RLast r n'') by eauto using r_step_last.
    assert (n'' = n') by eauto using r_last_fun.
    subst.
    assumption.
  Qed.

  Lemma r_first_subst:
    forall x v1 r n,
    RFirst (r_subst x v1 r) n ->
    forall v2 m,
    NStep v1 m ->
    NStep v2 m ->
    RFirst (r_subst x v2 r) n.
  Proof.
    intros.
    invc H.
    destruct r as (e1', e2').
    simpl in *.
    rename_hyp ((_,_) = _) as Hx.
    invc Hx.
    assert (rx: NEq v1 v2) by eauto using n_eq_def.
    rewrite rx in *.
    eauto using r_first_def.
  Qed.

  Lemma r_has_next_subst:
    forall x v1 r,
    RHasNext (r_subst x v1 r) ->
    forall v2 n,
    NStep v1 n ->
    NStep v2 n ->
    RHasNext (r_subst x v2 r).
  Proof.
    intros.
    destruct H as (n', Hr).
    eapply r_first_subst in Hr; eauto.
    unfold RHasNext.
    eauto.
  Qed.
  (* ---------------------- NEq -------------------------------- *)

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

  Lemma r_pick_inv_last:
    forall e1 e2 n,
    RPick (e1, e2) n ->
    RLast (e1, e2) n \/ RPick (e1, NBin NMinus e2  (NNum 1)) n.
  Proof.
    intros.
    invc H.
    assert (X: n = n2 - 1 \/ (n1 <= n < n2 - 1)) by lia.
    destruct X as [X|X]. {
      subst.
      left.
      eapply r_last_def; eauto; try lia.
      assert (r1: S (n2 - 1) = n2) by lia.
      rewrite r1.
      assumption.
    }
    right.
    eapply r_pick_def; eauto.
    apply n_step_minus; auto using n_step_num.
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
    RFree x (r_subst x e r) ->
    NFree x e.
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

  Definition RClosed r :=
    forall x,
    ~ RFree x r.


  Lemma r_first_to_closed:
    forall r n,
    RFirst r n ->
    RClosed r.
  Proof.
    intros.
    destruct r as (e1, e2).
    invc H.
    intros x N.
    destruct N as [N|N];
      contradict N;
      eauto using n_step_to_not_free.
  Qed.

  Lemma r_first_subst_1:
    forall r n,
    RFirst r n ->
    forall x v,
    RFirst (r_subst x v r) n.
  Proof.
    intros.
    assert (Hx := H).
    apply r_first_to_closed in H.
    rewrite r_subst_not_free; auto.
  Qed.


  Lemma r_pick_impl_1:
    forall e1 e2 n,
    RPick (NBin NPlus (NNum 1) e1, e2) n ->
    RPick (e1, e2) n.
  Proof.
    intros.
    invc H.
    apply n_step_inv_succ_l in H2.
    destruct H2 as (n', (Hn1, ?)).
    subst.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_pick_impl_2:
    forall e1 e2 m,
    RPick ((NBin NPlus (NNum 1) e1), e2) m ->
    RPick (e1, e2) (Nat.sub m 1).
  Proof.
    intros.
    invc H.
    rename_hyp (NStep _ n1) as Hn1.
    apply n_step_inv_succ_l in Hn1.
    destruct Hn1 as (n', (Hn1, ?)).
    subst.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_pick_impl_3:
    forall e1 e2 m,
    RPick ((NBin NPlus (NNum 1) e1), e2) m ->
    exists n, m = S n /\ RPick2 (e1, e2) n.
  Proof.
    intros.
    invc H.
    apply n_step_inv_succ_l in H2.
    destruct H2 as (n', (Hn1, ?)).
    subst.
    destruct m. {
      lia.
    }
    exists m.
    split; auto.
    eapply r_pick2_def; eauto.
    - lia.
    - lia.
  Qed.

  Lemma r_pick_impl_4:
    forall e1 e2 n,
    RPick (e1, e2) n ->
    exists m, RPick (e1, e2) m /\ NStep (NBin NMinus e2 (NNum 1)) m.
  Proof.
    intros.
    invc H.
    destruct n2. {
      lia.
    }
    exists n2.
    split. {
      eapply r_pick_def; eauto.
      lia.
    }
    assert (rx: n2 = S n2 - 1) by lia.
    rewrite rx.
    apply n_step_bin; auto using n_step_num.
  Qed.

  Lemma r_pick_advance:
    forall e1 e2 n,
    RPick (e1, (NBin NMinus e2 (NNum 1))) n ->
    RPick (NBin NPlus (NNum 1) e1, e2) (S n).
  Proof.
    intros.
    invc H.
    apply r_pick_def with (n1:=S n1) (n2:=S n2).
    - eapply n_step_add_eq; eauto using n_step_num.
    - destruct n2. { lia. }
      auto using n_step_inv_dec.
    - lia.
  Qed.

  Lemma r_pick2_advance:
    forall e1 e2 n,
    RPick2 (e1, e2) n ->
    RPick (NBin NPlus (NNum 1) e1, e2) (S n).
  Proof.
    intros.
    invc H.
    apply r_pick_def with (n1:=S n1) (n2:=n2); eauto using n_step_add_eq, n_step_num.
    lia.
  Qed.

  Lemma r_pick2_to_pick_r:
    forall r n,
    RPick2 r n ->
    RPick r (S n).
  Proof.
    intros.
    invc H.
    eapply r_pick_def; eauto.
  Qed.

  Lemma r_one_to_n_step_minus_1:
    forall e1 e2 n,
    ROne (e1, e2) n ->
    NStep (NBin NMinus e2 (NNum 1)) n.
  Proof.
    intros.
    invc H.
    eapply n_step_minus_eq; eauto using n_step_num.
    lia.
  Qed.

  Lemma r_step_to_closed_l:
    forall r n r',
    RStep r n r' ->
    RClosed r.
  Proof.
    intros.
    invc H.
    unfold RClosed.
    intros.
    intros N.
    destruct N as [N|N]; contradict N; eauto using n_step_to_not_free.
  Qed.

  Lemma r_subst_closed:
    forall x v r,
    RClosed r ->
    r_subst x v r = r.
  Proof.
    intros.
    unfold RClosed in *.
    apply r_subst_not_free.
    auto.
  Qed.

  Definition REq (r1 r2:range) := NEq (fst r1) (fst r2) /\ NEq (snd r1) (snd r2).

  Lemma r_eq_subst:
    forall x r v1 v2,
    NEq v1 v2 ->
    REq (r_subst x v1 r) (r_subst x v2 r).
  Proof.
    intros x (n1, n2) v1 v2 Ha.
    split; simpl.
    all: rewrite Ha.
    all: reflexivity.
  Qed.

  Global Instance r_eq_subst_proper: Proper (eq ==> NEq ==> eq ==> REq) r_subst.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    auto using r_eq_subst.
  Qed.

  Lemma r_eq_step:
    forall r1 r1' r2 r2' n,
    REq r1 r1' ->
    REq r2 r2' ->
    RStep r1 n r2 <-> RStep r1' n r2'.
  Proof.
    intros (e1, e2) (e1', e2') (e3, e4) (e3', e4') n (ha, hb) (hc, hd).
    simpl in *.
    split.
    all: intros Hx. {
      invc Hx.
      rewrite ha in *.
      rewrite hb in *.
      rewrite hc in *.
      rewrite hd in *.
      econstructor; eauto.
    }
    invc Hx.
    rewrite <- ha in *.
    rewrite <- hb in *.
    rewrite <- hc in *.
    rewrite <- hd in *.
    econstructor; eauto.
  Qed.

  Global Instance r_eq_step_proper: Proper (REq ==> eq ==> REq ==> iff) RStep.
  Proof.
    unfold Proper, respectful.
    intros r1 r1' Hr n' n ? r2 r2' Hr2.
    subst.
    eauto using r_eq_step.
  Qed.

  Lemma r_eq_empty:
    forall r r',
    REq r r' ->
    REmpty r <-> REmpty r'.
  Proof.
    intros (e1, e2) (e1', e2') (ha, hb).
    simpl in *.
    split.
    all: intros Hx. {
      invc Hx.
      rewrite ha in *.
      rewrite hb in *.
      econstructor; eauto.
    }
    invc Hx.
    rewrite <- ha in *.
    rewrite <- hb in *.
    econstructor; eauto.
  Qed.

  Global Instance r_eq_empty_proper: Proper (REq ==> iff) REmpty.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    eauto using r_eq_empty.
  Qed.

  Lemma r_eq_refl:
    forall e,
    REq e e.
  Proof.
    intros.
    split; reflexivity.
  Qed.

  Lemma r_eq_sym:
    forall e1 e2,
    REq e1 e2 ->
    REq e2 e1.
  Proof.
    unfold REq; intros.
    intuition.
  Qed.

  Lemma r_eq_trans:
    forall e1 e2 e3,
    REq e1 e2 ->
    REq e2 e3 ->
    REq e1 e3.
  Proof.
    unfold REq.
    intros.
    intuition.
    - transitivity (fst e2); auto.
    - transitivity (snd e2); auto.
  Qed.

  (** Register [NEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ REq
    reflexivity proved by r_eq_refl
    symmetry proved by r_eq_sym
    transitivity proved by r_eq_trans
    as r_eq_setoid.

  Lemma r_step_to_closed_r:
    forall r n r',
    RStep r n r' ->
    RClosed r'.
  Proof.
    intros.
    invc H.
    unfold RClosed.
    intros.
    intros N.
    destruct N as [N|N]; contradict N; eauto using n_step_to_not_free.
  Qed.

  Lemma r_step_to_closed:
    forall r n r',
    RStep r n r' ->
    RClosed r /\ RClosed r'.
  Proof.
    intros.
    split; eauto using r_step_to_closed_l, r_step_to_closed_r.
  Qed.

  Lemma r_step_inv_r:
    forall e1 e2 n1 r n2,
    RStep (e1, e2) n1 r ->
    RPick (NBin NPlus (NNum 1) e1, e2) n2 ->
    RPick r n2.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n4 = n3) by eauto using n_step_fun.
    subst.
    eapply r_pick_def; eauto.
    apply n_step_inv_succ_l in H2.
    destruct H2 as (n', (Hn, ?)).
    subst.
    assert (n1 = n') by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_step_inv_first:
    forall r n r',
    RStep r n r' ->
    RFirst r n \/ RPick r' n.
  Proof.
    intros.
    assert (hp: RPick r n) by eauto using r_step_to_pick.
    destruct r as (e1, e2).
    apply r_pick_inv_first in hp.
    destruct hp as [hp|hp]. {
      auto.
    }
    right.
    eauto using r_step_inv_r.
  Qed.

  Lemma r_pick_to_pick2:
    forall r n,
    RPick r n ->
    RPick r (S n) ->
    RPick2 r n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n0 = n1) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    subst.
    eapply r_pick2_def; eauto; lia.
  Qed.

  Lemma r_step_pick_advance:
    forall r n r',
    RStep r n r' ->
    forall n',
    RPick r n' ->
    n' = n \/ RPick r' n'.
  Proof.
    intros.
    destruct r as (e1, e2).
    apply r_pick_inv_first in H0.
    destruct H0 as [hp|hp]. {
      eauto using r_step_to_first, r_first_fun.
    }
    eapply r_step_inv_r in hp; eauto.
  Qed.

  Lemma r_step_pick2_advance:
    forall r n r',
    RStep r n r' ->
    forall n',
    RPick2 r n' ->
    (n' = n /\ RFirst r' (S n)) \/ RPick2 r' n'.
  Proof.
    intros.
    assert (hp: RPick r n') by eauto using r_pick2_to_pick.
    destruct r as (e1, e2).
    apply r_pick_inv_first in hp.
    destruct hp as [hp|hp]. {
      left.
      assert (n' = n). {
        assert (RFirst (e1, e2) n) by eauto using r_step_to_first.
        eauto using r_first_fun.
      }
      subst.
      split; auto.
      destruct r' as (e1', e2').
      invc H.
      invc H0.
      assert (n1 = n) by eauto using n_step_fun.
      assert (n0 = n2) by eauto using n_step_fun.
      subst.
      eapply r_first_def; eauto.
    }
    right.
    destruct r' as (e1', e2').
    apply r_pick2_advance in H0.
    eapply r_step_inv_r in H0; eauto.
    eapply r_step_inv_r in hp; eauto.
    eauto using r_pick_to_pick2.
  Qed.

  Lemma r_one_to_not_pick2:
    forall r n,
    ROne r n ->
    forall n',
    ~ RPick2 r n'.
  Proof.
    intros.
    intros N.
    invc N.
    invc H.
    assert (n1 = n) by eauto using n_step_fun.
    assert (n2 = S n) by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma r_step_to_defined_r:
    forall r n r',
    RStep r n r' ->
    RDefined r'.
  Proof.
    intros.
    unfold RDefined.
    destruct r' as (e1, e2).
    invc H.
    eauto.
  Qed.

  Lemma r_defined_subst:
    forall r x v,
    NClosed v ->
    RDefined r ->
    r_subst x v r = r.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    destruct H0 as ((n1, Ha), (n2, Hb)).
    rewrite n_subst_not_free; eauto using n_step_to_not_free.
    rewrite n_subst_not_free; eauto using n_step_to_not_free.
  Qed.

  Lemma r_step_subst:
    forall x e1 e2 r n n' r',
    RStep (r_subst x e1 r) n (r_subst x e1 r') ->
    NStep e1 n' ->
    NStep e2 n' ->
    RStep (r_subst x e2 r) n (r_subst x e2 r').
  Proof.
    intros.
    destruct r as (e, e').
    destruct r' as (f, f').
    simpl in *.
    invc H.
    apply r_step_def with (n2:=n2); eauto using NExp.n_step_subst.
  Qed.

  Lemma r_one_subst:
    forall x e1 e2 r n n',
    ROne (r_subst x e1 r) n ->
    NStep e1 n' ->
    NStep e2 n' ->
    ROne (r_subst x e2 r) n.
  Proof.
    intros.
    destruct r as (e, e').
    simpl in *.
    invc H.
    eauto using r_one_def, NExp.n_step_subst.
  Qed.

End Defs.

Module RExpNotations.
  Import NExpNotations.
(*   Notation "x '∈'  r " := (RPick r x) (at level 30, only printing) : exp_scope. *)
  Notation "r [ x := v ]" := (r_subst x v r) (at level 30, only printing) : exp_scope. 
End RExpNotations.