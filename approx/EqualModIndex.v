From Stdlib Require Import Sorting.SetoidList.
Require Import AExp.
Require Import Tictac.

Section Def.
  Inductive t : access_val -> access_val -> Prop :=
    def:
     forall o i i' m,
      t {| av_owner := o; av_index := i; av_mode := m |}
        {| av_owner := o; av_index := i'; av_mode := m |}.

  Lemma refl:
    forall x : access_val, t x x.
  Proof.
    intros [o i m].
    constructor.
  Qed.

  Lemma sym:
    forall x y : access_val,
    t x y ->
    t y x.
  Proof.
    intros [o i m] [o' i' m'] H.
    invc H.
    constructor.
  Qed.

  Lemma trans:
    forall x y z : access_val,
    t x y ->
    t y z ->
    t x z.
  Proof.
    intros.
    invc H.
    invc H0.
    constructor.
  Qed.

  #[global] Instance Equiv: Equivalence t.
  Proof.
    constructor.
    - unfold Reflexive.
      apply refl.
    - unfold Symmetric.
      apply sym.
    - unfold Transitive.
      apply trans.
  Qed.

  Lemma from_step tid:
    forall a1 a2 v1 v2,
    ae_mode a1 = ae_mode a2 ->
    AStep tid a1 v1 ->
    AStep tid a2 v2 ->
    t v1 v2.
  Proof.
    intros.
    invc H0.
    invc H1.
    simpl in *.
    subst.
    constructor.
  Qed.

End Def.