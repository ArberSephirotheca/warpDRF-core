From Faial.Approx Require Import RExp.
From Faial.Approx Require Import NExp.
From Faial.Core Require Import Tictac.
Require Import N.Equal.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Classes.RelationPairs.
Require R.Empty.
Require R.Last.
Require R.First.
Require R.Step.

Section Equal.
  Variable tid: nat.
  Inductive t : range -> range -> Prop :=
    def:
      forall e1 e2 e1' e2',
      N.Equal.t tid e1 e1' ->
      N.Equal.t tid e2 e2' ->
      t (e1, e2) (e1', e2').

  Lemma refl:
    forall r,
    t r r.
  Proof.
    intros (e1, e2).
    constructor.
    all: reflexivity.
  Qed.

  Lemma sym:
    forall r1 r2,
    t r1 r2 ->
    t r2 r1.
  Proof.
    intros.
    invc H.
    constructor.
    all: symmetry.
    all: assumption.
  Qed.

  Lemma trans:
    forall r1 r2 r3,
    t r1 r2 ->
    t r2 r3 ->
    t r1 r3.
  Proof.
    intros r1 r2 r3 Ha Hb.
    invc Ha.
    invc Hb.
    apply def.
    all: eauto using N.Equal.trans.
  Qed.

  (** Register [BEq] in Coq's tactics. *)
  Global Add Parametric Relation : _ t
    reflexivity proved by refl
    symmetry proved by sym
    transitivity proved by trans
    as setoid.

  Lemma empty r r':
    t r r' ->
    R.Empty.t tid r ->
    R.Empty.t tid r'.
  Proof.
    intros.
    invc H0.
    invc H.
    rename_hyp (N.Equal.t _ e1 _) as he1.
    rename_hyp (N.Equal.t _ e2 _) as he2.
    rename_hyp (NStep _ e1 _) as hn1.
    apply he1 in hn1.
    rename_hyp (NStep _ e2 _) as hn2.
    apply he2 in hn2.
    eapply Empty.def; eauto.
  Qed.

  #[global] Instance proper_empty: Proper (t ==> iff) (R.Empty.t tid).
  Proof.
    unfold Proper, respectful.
    intros x y Ha.
    split.
    all: intros He.
    - eauto using empty.
    - symmetry in Ha.
      eauto using empty.
  Qed.

  Lemma from_first_last r1 r2:
    forall n1,
    R.First.t tid r1 n1 ->
    R.First.t tid r2 n1 ->
    forall n2,
    R.Last.t tid r1 n2 ->
    R.Last.t tid r2 n2 ->
    t r1 r2.
  Proof.
    intros.
    invc H.
    invc H0.
    invc H1.
    invc H2.
    assert (n0 = n1) by eauto using n_step_fun.
    assert (n4 = S n2) by eauto using n_step_fun.
    assert (n5 = n1) by eauto using n_step_fun.
    subst.
    constructor.
    - constructor.
      all: intros.
      all: assert (n = n1) by eauto using n_step_fun.
      all: subst.
      all: assumption.
    - constructor.
      all: intros.
      all: assert (n = S n2) by eauto using n_step_fun.
      all: subst.
      all: assumption.
  Qed.

  Lemma step:
    forall r1 r1',
    t r1 r1' ->
    forall r2 r2',
    t r2 r2' ->
    forall n,
    Step.t tid r1 n r2 ->
    Step.t tid r1' n r2'.
  Proof.
    intros (e1,e2) (e1', e2') eq1 (f1, f2) (f1', f2') eq2 n s1.
    invc s1.
    invc eq1.
    invc eq2.
    rename_hyp (N.Equal.t _ e1 _) as eq1.
    rename_hyp (N.Equal.t _ e2 _) as eq2.
    rename_hyp (N.Equal.t _ f1 _) as eq3.
    rename_hyp (N.Equal.t _ f2 _) as eq4.
    apply Step.def with (n2:=n2); auto.
    - apply eq1.
      assumption.
    - apply eq2.
      assumption.
    - apply eq3.
      assumption.
    - apply eq4.
      assumption.
  Qed.

  #[global] Instance proper_step: Proper (t ==> eq ==> t ==> iff) (R.Step.t tid).
  Proof.
    unfold Proper, respectful.
    intros r1 r2 Ha n1 n2 eq1 r1' r2' Hb.
    subst.
    split.
    all: intros Hs.
    - eapply step; eauto.
    - symmetry in Ha, Hb.
      eauto using step.
  Qed.

  #[global] Instance proper_pair: Proper (
  N.Equal.t tid * N.Equal.t tid  ==> N.Equal.t tid * N.Equal.t tid
  ==> iff) t.
  Proof.
    unfold Proper, respectful,  RelCompFun, RelProd, relation_conjunction, predicate_intersection, RelCompFun.
    intros (e1, e2) (e3, e4) (eq1, eq2) (e5, e6) (e7, e8) (eq3, eq4).
    simpl in *.
    split.
    all: intros ha.
    all: invc ha.
    all: apply def.
    all: try rewrite eq1 in *.
    all: try rewrite eq2 in *.
    all: try rewrite eq3 in *.
    all: try rewrite eq4 in *.
    all: clear eq1 eq2 eq3 eq4.
    all: auto.
  Qed.

  #[global] Instance proper_subst: Proper (
    eq ==> N.Equal.t tid ==> eq ==> t
  ) r_subst.
  Proof.
    unfold Proper, respectful.
    intros y x eq1.
    subst.
    intros v' v eq1 r' r eq2.
    subst.
    destruct r as (e1, e2).
    simpl.
    rewrite eq1.
    reflexivity.
  Qed.

  Lemma last:
    forall r1 r2 n,
    t r1 r2 ->
    R.Last.t tid r1 n ->
    R.Last.t tid r2 n.
  Proof.
    intros.
    invc H0.
    destruct r2 as (e3, e4).
    invc H.
    rename_hyp (N.Equal.t _ e1 _) as eq1.
    rename_hyp (N.Equal.t _ e2 _) as eq2.
    econstructor; eauto.
    - rewrite <- eq1.
      assumption.
    - rewrite <- eq2.
      assumption.
  Qed.

  #[global] Instance proper_last: Proper (t ==> eq ==> iff) (R.Last.t tid).
  Proof.
    unfold Proper, respectful.
    intros r1 r2 eq1 n n' eq2.
    subst.
    split.
    all: intros ha.
    - eapply last; eauto.
    - symmetry in eq1.
      eapply last; eauto.
  Qed.

  Lemma from_step:
    forall r n r',
    Step.t tid r n r' ->
    forall n' r'',
    Step.t tid r n' r'' ->
    t r' r''.
  Proof.
    intros.
    invc H.
    invc H0.
    constructor.
    all: split.
    all: intros.
    all: repeat match goal with
      [ H1: NStep _ ?x ?n, H2: NStep _ ?x ?m |- _] =>
        assert (n = m) by eauto using n_step_fun; subst; clear H1
    end.
    all: auto.
  Qed.

  Lemma pick:
    forall r1 r2 n,
    t r1 r2 ->
    Pick.t tid r1 n ->
    Pick.t tid r2 n.
  Proof.
    intros.
    invc H0.
    destruct r2 as (e3, e4).
    invc H.
    rename_hyp (N.Equal.t _ e1 _) as eq1.
    rename_hyp (N.Equal.t _ e2 _) as eq2.
    econstructor; eauto.
    - rewrite <- eq1.
      assumption.
    - rewrite <- eq2.
      assumption.
  Qed.

  #[global] Instance proper_pick: Proper (t ==> eq ==> iff) (R.Pick.t tid).
  Proof.
    unfold Proper, respectful.
    intros r1 r2 eq1 n n' eq2.
    subst.
    split.
    all: intros ha.
    - eapply pick; eauto.
    - symmetry in eq1.
      eapply pick; eauto.
  Qed.
(*
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
  
*)
  (* ---------------------- NEq -------------------------------- *)
(*
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
*)
End Equal.