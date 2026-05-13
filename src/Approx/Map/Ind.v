From Faial.Core Require Import Var.
Require Import Dependency.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import Tictac.

Section Ind.
  Import Dependency.
  Definition t (keys: list var) (m: Map_VAR.t Dependency.t) : Prop :=
    forall k, List.In k keys <-> Map_VAR.MapsTo k Independent m.

  Lemma to_maps_to:
    forall env G,
    t env G ->
    forall x,
    In x env ->
    Map_VAR.MapsTo x Independent G.
  Proof.
    intros.
    apply H.
    assumption.
  Qed.

  Lemma add_dep:
    forall env G,
    t env G ->
    forall x,
    ~ List.In x env -> 
    t env (Map_VAR.add x Dependent G).
  Proof.
    unfold t.
    intros.
    rewrite H.
    split; intros Ha. {
      assert (x <> k). {
        intros N.
        subst.
        rename_hyp (~ _ ) as hm.
        contradict hm.
        rewrite H.
        assumption.
      }
      auto using Map_VAR.add_2.
    }
    destruct (Set_VAR.MF.eq_dec k x). {
      subst.
      apply add_4 in Ha.
      invc Ha.
    }
    eauto using Map_VAR.add_3.
  Qed.
(*
  Lemma add_dep:
    forall env G,
    t env G ->
    forall x,
    ~ Map_VAR.In x G -> 
    t env (Map_VAR.add x Dependent G).
  Proof.
    unfold t.
    intros.
    rewrite H; clear H.
    split; intros Ha. {
      assert (x <> k). {
        intros N.
        subst.
        rename_hyp (~ _ ) as hm.
        contradict hm.
        eauto using Map_VAR_Extra.mapsto_to_in.
      }
      auto using Map_VAR.add_2.
    }
    eapply Map_VAR.add_3; eauto.
    intros N.
    subst.
    apply add_4 in Ha.
    invc Ha.
  Qed.
*)
  Lemma add_indep:
    forall env G,
    t env G ->
    forall x,
    t (x :: env) (Map_VAR.add x Independent G).
  Proof.
    unfold t.
    intros.
    simpl.
    rewrite H.
    split.
    all: intros Ha.
    - destruct Ha as [Ha|Ha].
      + subst.
        apply Map_VAR.add_1.
        reflexivity.
      + destruct (Set_VAR.MF.eq_dec k x). {
          subst.
          auto using Map_VAR.add_1.
        }
        eapply Map_VAR.add_2; auto.
    - destruct (Set_VAR.MF.eq_dec x k). { intuition. }
      right.
      eauto using Map_VAR.add_3.
  Qed.

End Ind.
