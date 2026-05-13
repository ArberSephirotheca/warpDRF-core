Require Import NExp.
Require Import RExp.
Require Import Tictac.
Require R.First.
Require R.HasNext.
Require R.Last.
Require R.Pick.
Require R.Empty.

From Stdlib Require Import Lia.
Section Defs.
  Variable tid : nat.

  Inductive t : range -> nat -> range -> Prop :=
  | def:
    forall e1 e2 e3 e4 n1 n2,
    NStep tid e1 n1 ->
    NStep tid e2 n2 ->
    NStep tid e3 (S n1) ->
    NStep tid e4 n2 ->
    n1 < n2 ->
    t (e1, e2) n1 (e3, e4).

  Lemma to_first:
    forall r n r',
    t r n r' ->
    First.t tid r n.
  Proof.
    intros.
    invc H.
    eauto using First.def.
  Qed.

  Lemma refl_l:
    forall e n r,
    ~ t (e, e) n r.
  Proof.
    intros.
    intros N.
    invc N.
    assert (n2 = n) by  eauto using n_step_fun.
    subst.
    auto with *.
  Qed.

  Lemma first_fun:
    forall r n1 r' n2,
    t r n1 r' ->
    First.t tid r n2 ->
    n1 = n2.
  Proof.
    intros.
    apply to_first in H.
    eauto using First.func.
  Qed.

  Lemma to_last_2:
    forall r1 n1 n r2,
    t r1 n1 r2 ->
    Last.t tid r1 n ->
    HasNext.t tid r2 ->
    Last.t tid r2 n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n0 = n1) by eauto using n_step_fun.
    subst.
    assert (n2 = S n) by eauto using n_step_fun.
    subst.
    apply Last.def with (n1:=S n1).
    all: auto.
    invc H1.
    assert (n0 = S n1) by eauto using n_step_fun.
    assert (n2 = S n) by eauto using n_step_fun.
    lia.
  Qed.

  Lemma to_last_1:
    forall r1 n1 n r2,
    t r1 n1 r2 ->
    Last.t tid r2 n ->
    Last.t tid r1 n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n0 = S n1) by eauto using n_step_num, n_step_fun.
    assert (n2 = S n) by eauto using n_step_num, n_step_fun.
    subst.
    eapply Last.def; eauto.
  Qed.

  Lemma to_pick:
    forall r n r',
    t r n r' ->
    Pick.t tid r n.
  Proof.
    intros.
    eauto using to_first, Pick.from_first.
  Qed.

  Lemma pick_rev:
    forall r n' r' n,
    t r n' r' ->
    Pick.t tid r' n ->
    Pick.t tid r n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n1 = S n') by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply Pick.def; eauto.
    lia.
  Qed.

  Lemma pick2_rev:
    forall r n' r' n,
    t r n' r' ->
    Pick2.t tid r' n ->
    Pick2.t tid r n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n1 = S n') by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply Pick2.def; eauto.
    lia.
  Qed.

  Lemma unfold_2:
    forall r1 n r2,
    t r1 n r2 ->
    Empty.t tid r2 \/ First.t tid r2 (S n).
  Proof.
    intros.
    invc H.
    invc H4. {
      left.
      eapply Empty.def; eauto.
    }
    right.
    econstructor.
    all: eauto.
    lia.
  Qed.

  Lemma inv_step:
    forall r1 r2 n1 n2 r3,
    t r1 n1 r2 ->
    t r2 n2 r3 ->
    n2 = S n1.
  Proof.
    intros.
    invc H.
    invc H0.
    eauto using n_step_fun.
  Qed.

  Lemma from_has_next:
    forall r,
    HasNext.t tid r ->
    exists n r',
    t r n r'.
  Proof.
    intros.
    invc H.
    exists n1.
    exists (NNum (S n1), e2).
    econstructor; eauto using n_step_num.
  Qed.

  Lemma to_has_next:
    forall r n r',
    t r n r' ->
    HasNext.t tid r.
  Proof.
    intros.
    apply to_first in H.
    eauto using First.to_has_next.
  Qed.

  Lemma to_empty:
    forall r n r',
    t r n r' ->
    ~ Empty.t tid r.
  Proof.
    intros.
    apply Empty.from_has_next.
    eauto using to_has_next.
  Qed. 

  Lemma func_1:
    forall r n r',
    t r n r' ->
    forall n' r'',
    t r n' r'' ->
    n' = n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n' = n) by eauto using n_step_fun.
    subst.
    reflexivity.
  Qed.

  Lemma inv_next_eq:
    forall r n r' n',
    t r n r' ->
    First.t tid r' n' ->
    n' = S n.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n' = S n) by eauto using n_step_num, n_step_fun.
    auto.
  Qed.

  Lemma to_pick2:
    forall r n r',
    t r n r' ->
    HasNext.t tid r' ->
    Pick2.t tid r n.
  Proof.
    intros.
    destruct r as (e1, e2).
    invc H.
    invc H0.
    assert (n1 = S n) by eauto using n_step_fun, n_step_num.
    assert (n0 = n2) by eauto using n_step_fun, n_step_num.
    subst.
    eapply Pick2.def; eauto.
  Qed.

  Lemma to_last:
    forall r1 n r2,
    t r1 n r2 ->
    Empty.t tid r2 ->
    Last.t tid r1 n.
  Proof.
    intros.
    invc H.
    invc H0.
    econstructor.
    all: eauto.
    assert (n1 = S n) by eauto using n_step_fun.
    subst.
    assert (n0 = n2) by eauto using n_step_fun.
    subst.
    assert (S n = n2) by lia.
    subst.
    assumption.
  Qed.

  Lemma func_empty:
    forall r n r' n',
    t r n r' ->
    Last.t tid r n' ->
    Empty.t tid r' ->
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

  Lemma inv:
    forall r1 n r2,
    t r1 n r2 ->
    Empty.t tid r2 \/ HasNext.t tid r2.
  Proof.
    intros.
    invc H.
    invc H4. {
      left.
      eapply Empty.def; eauto.
    }
    right.
    eapply HasNext.def; eauto.
    lia.
  Qed.

  Lemma to_closed_l:
    forall r n r',
    t r n r' ->
    Closed.t r.
  Proof.
    intros.
    invc H.
    unfold Closed.t.
    intros.
    intros N.
    destruct N as [N|N]; contradict N; eauto using n_step_to_not_free.
  Qed.

  Lemma to_closed_r:
    forall r n r',
    t r n r' ->
    Closed.t r'.
  Proof.
    intros.
    invc H.
    unfold Closed.t.
    intros.
    intros N.
    destruct N as [N|N]; contradict N; eauto using n_step_to_not_free.
  Qed.

  Lemma to_closed:
    forall r n r',
    t r n r' ->
    Closed.t r /\ Closed.t r'.
  Proof.
    intros.
    split; eauto using to_closed_l, to_closed_r.
  Qed.

  Lemma from_closed:
    forall r,
    Closed.t r ->
    HasNext.t tid r \/ Empty.t tid r.
  Proof.
    intros.
    destruct r as (e1, e2).
    apply Closed.inv in H.
    destruct H as (Ha, Hb).
    apply n_closed_to_step with (tid:=tid) in Ha.
    apply n_closed_to_step with (tid:=tid) in Hb.
    destruct Ha as (n1, Ha).
    destruct Hb as (n2, Hb).
    assert (Hx: n1 < n2 \/ n1 >= n2) by lia.
    destruct Hx. {
      left.
      eapply HasNext.def; eauto.
    }
    right.
    eapply Empty.def.
    all: eauto.
  Qed.

  Lemma inv_r:
    forall e1 e2 n1 r n2,
    t (e1, e2) n1 r ->
    Pick.t tid (NBin NPlus (NNum 1) e1, e2) n2 ->
    Pick.t tid r n2.
  Proof.
    intros.
    invc H.
    invc H0.
    assert (n4 = n3) by eauto using n_step_fun.
    subst.
    eapply Pick.def; eauto.
    apply n_step_inv_succ_l in H2.
    destruct H2 as (n', (Hn, ?)).
    subst.
    assert (n1 = n') by eauto using n_step_fun.
    subst.
    lia.
  Qed.

  Lemma inv_first:
    forall r n r',
    t r n r' ->
    First.t tid r n \/ Pick.t tid r' n.
  Proof.
    intros.
    assert (hp: Pick.t tid r n) by eauto using to_pick.
    destruct r as (e1, e2).
    apply Pick.inv_first in hp.
    destruct hp as [hp|hp]. {
      auto.
    }
    right.
    eauto using inv_r.
  Qed.

  Lemma pick_advance:
    forall r n r',
    t r n r' ->
    forall n',
    Pick.t tid r n' ->
    n' = n \/ Pick.t tid r' n'.
  Proof.
    intros.
    destruct r as (e1, e2).
    apply Pick.inv_first in H0.
    destruct H0 as [hp|hp]. {
      eauto using to_first, First.func.
    }
    eapply inv_r in hp; eauto.
  Qed.

  Lemma pick2_advance:
    forall r n r',
    t r n r' ->
    forall n',
    Pick2.t tid r n' ->
    (n' = n /\ First.t tid r' (S n)) \/ Pick2.t tid r' n'.
  Proof.
    intros.
    assert (hp: Pick.t tid r n') by eauto using Pick.from_pick2.
    destruct r as (e1, e2).
    apply Pick.inv_first in hp.
    destruct hp as [hp|hp]. {
      left.
      assert (n' = n). {
        assert (First.t tid (e1, e2) n) by eauto using to_first.
        eauto using First.func.
      }
      subst.
      split; auto.
      destruct r' as (e1', e2').
      invc H.
      invc H0.
      assert (n1 = n) by eauto using n_step_fun.
      assert (n0 = n2) by eauto using n_step_fun.
      subst.
      eapply First.def; eauto.
    }
    right.
    destruct r' as (e1', e2').
    apply Pick.from_pick2_inc in H0.
    eapply inv_r in H0; eauto.
    eapply inv_r in hp; eauto.
    eauto using Pick.to_pick2.
  Qed.

End Defs.