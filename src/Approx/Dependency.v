From Faial.Core Require Import Tictac.
From Faial.Approx Require Import Var.
Module Dependency.
  Inductive t: Type :=
    | Independent: t
    | Dependent: t
    .

  Definition merge (d1 d2: t) :=
    match d1,d2 with
    | Independent, Independent => Independent
    | _, _ => Dependent
  end.
  
  Lemma merge_independent_l:
    forall d,
    merge Independent d = d.
  Proof.
    intros []; simpl; reflexivity.
  Qed.

  Lemma merge_independent_r:
    forall d,
    merge d Independent = d.
  Proof.
    intros []; simpl; reflexivity.
  Qed.

  Lemma merge_inv_indep:
    forall d1 d2,
    merge d1 d2 = Independent ->
    d1 = Independent /\ d2 = Independent.
  Proof.
    intros [] [] H.
    all: simpl in H.
    all: intuition.
  Qed.

  Lemma merge_refl:
    forall d,
    merge d d = d.
  Proof.
    intros [].
    all: reflexivity.
  Qed.

  Module Le.
    Inductive t : Dependency.t -> Dependency.t -> Prop :=
    | le_eq:
      forall d,
      t d d
    | le_ind:
      forall d,
      t Independent d.

    Lemma merge_l:
      forall d1 d2,
      t d1 (merge d1 d2).
    Proof.
      intros [] [].
      all: simpl.
      all: constructor.
    Qed.

    Lemma merge_r:
      forall d1 d2,
      t d2 (merge d1 d2).
    Proof.
      intros [] [].
      all: simpl.
      all: constructor.
    Qed.

    Lemma merge:
      forall d1 d2 d1' d2',
      t d1' d1 ->
      t d2' d2 ->
      t (merge d1' d2') (merge d1 d2).
    Proof.
      intros.
      invc H.
      all: invc H0.
      - constructor.
      - rewrite merge_independent_r.
        auto using merge_l.
      - rewrite merge_independent_l.
        auto using merge_r.
      - simpl.
        constructor.
    Qed.

    Lemma inv_independent_r:
      forall d,
      t d Independent ->
      d = Independent.
    Proof.
      intros [] H; auto.
      invc H.
    Qed.
  End Le.
End Dependency.


Lemma add_4:
  forall {A:Type} k (v1:A) v2 m,
  Map_VAR.MapsTo k v1 (Map_VAR.add k v2 m) ->
  v1 = v2.
Proof.
  intros.
  assert (Map_VAR.MapsTo k v2 (Map_VAR.add k v2 m)) by eauto using Map_VAR.add_1.
  eauto using Map_VAR_Facts.MapsTo_fun.
Qed.


Module Env.
  Definition t := Map_VAR.t Dependency.t.
  Module Le.
    Definition t (env1 env2:Env.t) : Prop :=
      forall x d,
        Map_VAR.MapsTo x d env2 ->
        exists d', Dependency.Le.t d' d /\ Map_VAR.MapsTo x d' env1.

    Lemma inv {G:Env.t} {G':Env.t} (le:t G G'):
      forall x d,
      Map_VAR.MapsTo x d G' ->
      exists d', Dependency.Le.t d' d /\ Map_VAR.MapsTo x d' G.
    Proof.
      intros.
      apply le in H.
      assumption.
    Qed.

    Lemma add_1:
      forall d d',
      Dependency.Le.t d' d ->
      forall x env,
      t (Map_VAR.add x d' env) (Map_VAR.add x d env).
    Proof.
      intros.
      unfold t.
      intros k d1 hm.
      destruct (Set_VAR.MF.eq_dec k x). {
        subst.
        assert (d1 = d) by eauto using add_4.
        subst.
        exists d'.
        split; auto using Map_VAR.add_1.
      }
      apply Map_VAR.add_3 in hm; auto.
      exists d1.
      split. {
        constructor.
      }
      auto using Map_VAR.add_2.
    Qed.
  End Le.
End Env.

