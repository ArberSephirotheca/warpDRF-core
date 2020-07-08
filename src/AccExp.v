Require Import Coq.Lists.List.

Require Import Exp.
Require Import Var.

Class Access := {
  access_exp: Type;
  access_val: Type;
  access_in: var -> access_exp -> Prop;
  access_subst: var -> nexp -> access_exp -> access_exp;
  access_step: (access_exp * nexp) -> list access_val -> Prop;
  access_eval1: (access_exp * nexp) -> option (list access_val);
  access_safe: access_val -> access_val -> Prop;
  access_tid: access_val -> nat;
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
    forall e l,
    access_eval1 e = Some l ->
    access_step e l;
  access_step_to_eval1:
    forall e l,
    access_step e l ->
    access_eval1 e = Some l;

  access_step_inv_tid:
    forall e en n l,
    access_step (e, en) l ->
    NStep en n -> 
    Forall (fun a=> access_tid a = n) l;

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

  access_subst_subst_trans:
    forall e x v y,
    ~ access_in x e ->
    access_subst x v (access_subst y (NVar x) e) = access_subst y v e;

  access_subst_not_in:
    forall x e v,
    ~ access_in x e ->
    access_subst x v e = e;

  access_in_subst_neq:
    forall e x y v,
    access_in x (access_subst y v e) ->
    ~ NIn x v ->
    access_in x e;

}.

Section Defs.
  Context `{A:Access}.

  Definition cond_access := (access_exp * bexp) % type.

  Definition cond_access_subst x v (p:cond_access) :=
    let (e, b) := p in
    (access_subst x v e, b_subst x v b).

  Definition cond_access_cond (e:cond_access) : bexp := snd e.

  Inductive CStep: (cond_access * nexp) ->  list access_val -> Prop :=
  | c_step_true:
    forall b e n l,
    BStep b true ->
    access_step (e,n) l ->
    CStep ((e,b),n) l
  | c_step_false:
    forall b e n l,
    BStep b false ->
    access_step (e,n) l ->
    CStep ((e,b),n) nil.

  Definition cond_access_eval1 (p:cond_access * nexp) :=
    match p with
      ((e,b),n) =>
      match access_eval1 (e,n), b_step b with
      | Some l, Some true => Some l
      | Some _, Some false => Some nil
      | _, _ => None
      end
    end.
  (* Make sure simple doesn't unfold this definition.
     The workaround is to require the user to [unfold cond_access_eval1].
     *)
  Global Arguments cond_access_eval1 _ : simpl never.

  Inductive CIn (x:var): cond_access -> Prop :=
  | c_in_access:
    forall e b,
    access_in x e ->
    CIn x (e,b)
  | c_in_cond:
    forall e b,
    BIn x b ->
    CIn x (e,b).

  Lemma c_step_to_b_step:
    forall e b n v,
    CStep ((e,b), n) v ->
    exists b',
    BStep b b'.
  Proof.
    intros.
    inversion H; subst; clear H; eauto.
  Qed.

  Lemma c_step_inv_true:
    forall e b n l,
    CStep (e, b, n) l ->
    BStep b true ->
    access_step (e, n) l.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
    assert (N: true = false) by eauto using b_step_fun.
    inversion N.
  Qed.

  Lemma c_step_inv_false:
    forall e b n l,
    CStep (e, b, n) l ->
    BStep b false ->
    l = nil.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
    assert (N: true = false) by eauto using b_step_fun.
    inversion N.
  Qed.

  Lemma c_step_fun:
    forall e l1 l2,
    CStep e l1 ->
    CStep e l2 ->
    l1 = l2.
  Proof.
    intros ((e,b),n) l1 l2 Hc1 Hc2.
    destruct c_step_to_b_step with (e:=e) (b:=b) (n:=n) (v:=l1) as ([], Hb); auto.
    - apply c_step_inv_true in Hc1; auto.
      apply c_step_inv_true in Hc2; auto.
      eauto using access_step_fun.
    - apply c_step_inv_false in Hc1; auto.
      apply c_step_inv_false in Hc2; auto.
      subst; reflexivity.
  Qed.

  Lemma cond_access_eval1_to_step:
    forall e l,
    cond_access_eval1 e = Some l ->
    CStep e l.
  Proof.
    intros ((e,b), n) l H.
    unfold cond_access_eval1 in H.
    simpl in H.
    destruct (access_eval1 _) as [v|] eqn:Hae; try (inversion H; fail).
    destruct (b_step _) as [[]|] eqn:Hbe;
      try (inversion H; fail);
      inversion H; subst; clear H;
      apply access_eval1_to_step in Hae;
      apply b_step_to_prop in Hbe.
    - eauto using c_step_true.
    - eauto using c_step_false.
  Qed.

  Lemma cond_access_step_to_eval1:
    forall e l,
    CStep e l ->
    cond_access_eval1 e = Some l.
  Proof.
    intros ((e,b), n) v Hr.
    inversion Hr; subst; clear Hr.
    - apply access_step_to_eval1 in H4.
      apply prop_to_b_step in H3.
      unfold cond_access_eval1.
      simpl.
      rewrite H3.
      rewrite H4.
      reflexivity.
    - apply access_step_to_eval1 in H4.
      apply prop_to_b_step in H3.
      unfold cond_access_eval1.
      simpl.
      rewrite H3.
      rewrite H4.
      reflexivity.
  Qed.

  Lemma cond_access_step_inv_tid:
    forall e en n l,
    CStep (e, en) l ->
    NStep en n -> 
    Forall (fun a=> access_tid a = n) l.
  Proof.
    intros.
    inversion H; subst; clear H.
    - eauto using access_step_inv_tid.
    - apply Forall_nil.
  Qed.

  Lemma cond_access_step_next:
    forall x n a v,
    CStep (cond_access_subst x (NNum n) a, NNum n) v ->
    forall m,
    exists v',
    CStep (cond_access_subst x (NNum m) a, NNum m) v'.
  Proof.
    intros x n (e,b) v H m.
    inversion H; subst; clear H;
      apply access_step_next with (m0:=m) in H5; auto;
      destruct H5 as (v', Hs);
      apply b_step_subst_next with (m:=m) in H4;
      destruct H4 as ([], Hb); eauto using c_step_true;
      exists nil;
      eapply c_step_false; eauto.
  Qed.

  Lemma cond_access_subst_subst_eq:
    forall x n1 n2 a,
    cond_access_subst x (NNum n1) (cond_access_subst x (NNum n2) a) =
    cond_access_subst x (NNum n2) a.
  Proof.
    intros x n1 n2 (e,b).
    simpl.
    rewrite access_subst_subst_eq.
    rewrite b_subst_subst_eq.
    reflexivity.
  Qed.

  Lemma cond_access_subst_subst_neq:
    forall x y n1 n2 a,
    x <> y ->
    cond_access_subst x (NNum n1) (cond_access_subst y (NNum n2) a) =
    cond_access_subst y (NNum n2) (cond_access_subst x (NNum n1) a).
  Proof.
    intros x y n1 n2 (e,b) Hn.
    simpl.
    rewrite access_subst_subst_neq; auto.
    rewrite b_subst_subst_neq; auto.
  Qed.

  Lemma cond_access_subst_subst_neq_2:
    forall x y z n a,
    x <> z ->
    y <> z ->
    cond_access_subst x (NVar y) (cond_access_subst z (NNum n) a)
    =
    cond_access_subst z (NNum n) (cond_access_subst x (NVar y) a).
  Proof.
    intros x y z n (e,b) Hn1 Hn2.
    simpl.
    rewrite access_subst_subst_neq_2; auto.
    rewrite b_subst_subst_neq_2; auto.
  Qed.

  Lemma cond_access_subst_subst_trans:
    forall e x v y,
    ~ CIn x e ->
    cond_access_subst x v (cond_access_subst y (NVar x) e)
    =
    cond_access_subst y v e.
  Proof.
    intros (e,b) x v y Hn.
    simpl.
    assert (~ access_in x e). {
      intros N.
      contradict Hn.
      auto using c_in_access.
    }
    rewrite access_subst_subst_trans; auto.
    rewrite b_subst_subst_trans; auto.
    intros N.
    contradict Hn.
    auto using c_in_cond.
  Qed.

  Lemma cond_access_subst_not_in:
    forall x e v,
    ~ CIn x e ->
    cond_access_subst x v e = e.
  Proof.
    intros x (e,b) v Hn.
    simpl.
    rewrite access_subst_not_in; auto. {
      rewrite b_subst_not_in; auto.
      intros N.
      contradict Hn.
      auto using c_in_cond.
    }
    intros N.
    contradict Hn.
    auto using c_in_access.
  Qed.

  Lemma cond_access_in_subst_neq:
    forall e x y v,
    CIn x (cond_access_subst y v e) ->
    ~ NIn x v ->
    CIn x e.
  Proof.
    intros (e,b) x y v Hi Hn.
    simpl in *.
    inversion Hi; subst; clear Hi.
    + eauto using c_in_access, access_in_subst_neq.
    + eauto using c_in_cond, in_b_subst_neq.
  Qed.
End Defs.
