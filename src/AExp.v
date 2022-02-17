Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.

Require Import NExp.
Require Import BExp.
Require Import Var.

Class Access := {
  access_exp: Type;
  access_val: Type;
  AFree: var -> access_exp -> Prop;
  access_subst: var -> nexp -> access_exp -> access_exp;
  access_step: (access_exp * nexp) -> access_val -> Prop;
  access_eval1: (access_exp * nexp) -> option access_val;
  access_safe: access_val -> access_val -> Prop;
  access_tid: access_val -> nat;
  access_eq : access_exp -> access_exp -> Prop;

  access_safe_eq_tid:
    forall v1 v2,
    access_tid v1 = access_tid v2 ->
    access_safe v1 v2;
  access_step_fun:
    forall e l1 l2,
    access_step e l1 ->
    access_step e l2 ->
    l1 = l2;
  access_eval1_to_step:
    forall e v,
    access_eval1 e = Some v ->
    access_step e v;
  access_step_to_eval1:
    forall e l,
    access_step e l ->
    access_eval1 e = Some l;

  access_step_inv_tid:
    forall e en n v,
    access_step (e, en) v ->
    NStep en n -> 
    access_tid v = n;

  access_step_next:
    forall x n a v,
    access_step (access_subst x (NNum n) a, NNum n) v ->
    forall m,
    exists v',
    access_step (access_subst x (NNum m) a, NNum m) v';

  access_safe_sym:
    forall x y,
    access_safe x y ->
    access_safe y x;

  access_subst_subst_eq:
    forall x n1 n2 a,
    access_subst x (NNum n1) (access_subst x (NNum n2) a) =
    access_subst x (NNum n2) a;

  access_subst_subst_eq_2:
    forall x n v e,
    ~ NFree x v ->
    access_subst x e (access_subst x v n) = access_subst x v n;

  access_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    access_subst x (NNum n1) (access_subst y (NNum n2) a) =
    access_subst y (NNum n2) (access_subst x (NNum n1) a);

  access_subst_subst_neq_2:
    forall x y z n i,
    x <> z ->
    y <> z ->
    access_subst x (NVar y) (access_subst z (NNum n) i)
    =
    access_subst z (NNum n) (access_subst x (NVar y) i);

  access_subst_subst_neq_3:
    forall e x y v1 v2,
    x <> y ->
    ~ NFree y v1 ->
    ~ NFree x v2 ->
    access_subst x v1 (access_subst y v2 e)
    =
    access_subst y v2 (access_subst x v1 e);

  access_subst_subst_trans:
    forall e x v y,
    ~ AFree x e ->
    access_subst x v (access_subst y (NVar x) e) = access_subst y v e;

  access_subst_not_free:
    forall x v e,
    ~ AFree x e ->
    access_subst x v e = e;

  access_free_inv_subst:
    forall e x y v,
    AFree x (access_subst y v e) ->
    NFree x v \/
    AFree x e;

  access_in_subst_neq:
    forall e x y v,
    AFree x (access_subst y v e) ->
    ~ NFree x v ->
    AFree x e;

  (* Make sure the equivalence relation is properly specified. *)
  access_eq_refl: forall x, access_eq x x;
  access_eq_sym: forall x y, access_eq x y -> access_eq y x;
  access_eq_trans: forall x y z, access_eq x y -> access_eq y z -> access_eq x z;

  (* Allow rewriting nexp under an access substitution. *)
  access_step_proper:
    forall e' e n n' h, 
    access_eq e e' ->
    NEq n n' ->
    access_step (e, n) h ->
    access_step (e', n') h;

  access_subst_proper:
    forall x v v' e,
    NEq v v' ->
    access_eq (access_subst x v e) (access_subst x v' e);
  access_subst_subst_eq_1:
    forall (e1 e2 : nexp) (x : Var.VAR.t) a,
       access_subst x e1 (access_subst x e2 a)
       = access_subst x (n_subst x e1 e2) a;

  access_subst_subst_neq_5:
    forall e3 x y e1 e2,
    NClosed e1 ->
    x <> y ->
    access_subst y e1 (access_subst x e2 e3) =
    access_subst x (n_subst y e1 e2) (access_subst y e1 e3);

  access_free_inv_subst_eq:
    forall x e a,
    AFree x (access_subst x e a) ->
    NFree x e;
}.

Section Defs.
  Context `{A:Access}.

  Global Add Parametric Relation : _ access_eq
    reflexivity proved by access_eq_refl
    symmetry proved by access_eq_sym
    transitivity proved by access_eq_trans
    as access_eq_setoid.

  Global Instance access_proper_1: Proper (eq ==> NEq ==> eq ==> access_eq) access_subst.
  Proof.
    unfold Proper, respectful.
    intros.
    subst.
    auto using access_subst_proper.
  Qed.

  (* Allow rewriting under access_step with NEq and access_eq. *)

  Global Instance access_proper_2: Proper (access_eq * NEq ==> eq ==> iff) access_step.
  Proof.
    unfold Proper, respectful.
    intros.
    split; intros.
    + subst.
      destruct x as (a1, e1).
      destruct y as (a2, e2).
      destruct H as (Ha, Hb).
      unfold RelCompFun in *.
      simpl in *.
      eapply access_step_proper; eauto.
    + subst.
      destruct x as (a1, e1).
      destruct y as (a2, e2).
      destruct H as (Ha, Hb).
      unfold RelCompFun in *.
      simpl in *.
      symmetry in Ha.
      symmetry in Hb.
      eapply access_step_proper; eauto.
  Qed.

End Defs.
