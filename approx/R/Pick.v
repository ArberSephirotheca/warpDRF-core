Require Import RExp.
Require Import NExp.
Require Import Tictac.
From Stdlib Require Import Lia.
Require R.Last.
Require R.First.
Require R.Pick2.

Section Defs.
  Variable tid: nat.
  Inductive t : range -> nat -> Prop :=
  | def:
    forall e1 e2 n1 n2 n,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    n1 <= n < n2 ->
    t (e1, e2) n.

  Lemma from_last:
    forall r n,
    Last.t tid r n ->
    t r n.
  Proof.
    intros.
    invc H.
    eapply def; eauto.
    lia.
  Qed.

  Lemma from_first:
    forall r n,
    First.t tid r n ->
    t r n.
  Proof.
    intros.
    invc H.
    eapply def; eauto.
  Qed.

  Lemma inv_first:
    forall e1 e2 n,
    t (e1, e2) n ->
    First.t tid (e1, e2) n \/ t (NBin NPlus (NNum 1) e1, e2) n.
  Proof.
    intros.
    invc H.
    assert (X: n = n1 \/ (S n1 <= n < n2)) by lia.
    destruct X as [?|X]. {
      subst.
      left.
      eapply First.def; eauto.
      lia.
    }
    right.
    eapply def; eauto.
    assert (r1: S n1 = 1 + n1) by lia.
    rewrite r1.
    apply n_step_plus; auto using n_step_num.
  Qed.

  Lemma inv_last:
    forall e1 e2 n,
    t (e1, e2) n ->
    Last.t tid (e1, e2) n \/ t (e1, NBin NMinus e2  (NNum 1)) n.
  Proof.
    intros.
    invc H.
    assert (X: n = n2 - 1 \/ (n1 <= n < n2 - 1)) by lia.
    destruct X as [X|X]. {
      subst.
      left.
      eapply Last.def; eauto; try lia.
      assert (r1: S (n2 - 1) = n2) by lia.
      rewrite r1.
      assumption.
    }
    right.
    eapply def; eauto.
    apply n_step_minus; auto using n_step_num.
  Qed.
 

  Lemma impl_1:
    forall e1 e2 n,
    t (NBin NPlus (NNum 1) e1, e2) n ->
    t (e1, e2) n.
  Proof.
    intros.
    invc H.
    apply n_step_inv_succ_l in H2.
    destruct H2 as (n', (Hn1, ?)).
    subst.
    eapply def; eauto.
    lia.
  Qed.

  Lemma impl_2:
    forall e1 e2 m,
    t ((NBin NPlus (NNum 1) e1), e2) m ->
    t (e1, e2) (Nat.sub m 1).
  Proof.
    intros.
    invc H.
    rename_hyp (NStep _ _ n1) as Hn1.
    apply n_step_inv_succ_l in Hn1.
    destruct Hn1 as (n', (Hn1, ?)).
    subst.
    eapply def; eauto.
    lia.
  Qed.

  Lemma from_pick2:
    forall r n,
    Pick2.t tid r n ->
    t r n.
  Proof.
    intros.
    invc H.
    eapply def; eauto.
    lia.
  Qed.

  Lemma impl_3:
    forall e1 e2 m,
    t ((NBin NPlus (NNum 1) e1), e2) m ->
    exists n, m = S n /\ Pick2.t tid (e1, e2) n.
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
    eapply Pick2.def; eauto.
    all: lia.
  Qed.

  Lemma impl_4:
    forall e1 e2 n,
    t (e1, e2) n ->
    exists m, t (e1, e2) m /\ NStep tid (NBin NMinus e2 (NNum 1)) m.
  Proof.
    intros.
    invc H.
    destruct n2. {
      lia.
    }
    exists n2.
    split. {
      eapply def; eauto.
      lia.
    }
    assert (rx: n2 = S n2 - 1) by lia.
    rewrite rx.
    apply n_step_bin; auto using n_step_num.
  Qed.

  Lemma advance:
    forall e1 e2 n,
    t (e1, (NBin NMinus e2 (NNum 1))) n ->
    t (NBin NPlus (NNum 1) e1, e2) (S n).
  Proof.
    intros.
    invc H.
    apply def with (n1:=S n1) (n2:=S n2).
    - eapply n_step_add_eq; eauto using n_step_num.
    - destruct n2. { lia. }
      auto using n_step_inv_dec.
    - lia.
  Qed.

  Lemma from_pick2_inc:
    forall e1 e2 n,
    Pick2.t tid (e1, e2) n ->
    t (NBin NPlus (NNum 1) e1, e2) (S n).
  Proof.
    intros.
    invc H.
    apply def with (n1:=S n1) (n2:=n2); eauto using n_step_add_eq, n_step_num.
    lia.
  Qed.

  Lemma from_pick2_succ:
    forall r n,
    Pick2.t tid r n ->
    t r (S n).
  Proof.
    intros.
    invc H.
    eapply def; eauto.
  Qed.

  Lemma to_pick2:
    forall r n,
    t r n ->
    t r (S n) ->
    Pick2.t tid r n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n0 = n1) by eauto using n_step_fun.
    assert (n3 = n2) by eauto using n_step_fun.
    subst.
    eapply Pick2.def; eauto; lia.
  Qed.

End Defs.