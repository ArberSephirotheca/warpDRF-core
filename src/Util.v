Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Aniceto.Graphs.Graph.

Section clos_trans_refl.
  Lemma clos_refl_trans_to_clos_trans:
    forall (A:Type) (R:relation A) x y,
    clos_refl_trans A R x y ->
    clos_trans A R x y \/ x = y.
  Proof.
    intros.
    induction H.
    - left.
      auto using t_step.
    - intuition.
    - destruct IHclos_refl_trans1 as [Hx|Hx]. {
        destruct IHclos_refl_trans2 as [Hy|Hy]. {
          left.
          apply t_trans with (y:=y); auto.
        }
        subst.
        intuition.
      }
      destruct IHclos_refl_trans2 as [Hy|Hy]; subst; intuition.
  Qed.
End clos_trans_refl.

Section LinWalk2.
  Variable A:Type.
  Variable Edge: A * A -> Prop.

  Lemma walk2_inv_3:
    forall v1 vn w,
    Walk2 Edge v1 vn w ->
    (w = (v1,vn)::nil /\ Edge (v1, vn)) \/
    (exists v2, Edge (v1, v2) /\ exists w' e', w = (v1, v2) :: e' :: w' /\ Walk2 Edge v2 vn (e' :: w')).
  Proof.
    intros.
    destruct w. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    destruct w. {
      apply walk2_inv_pair in H.
      destruct H.
      subst.
      intuition.
    }
    right.
    apply walk2_inv in H.
    destruct H as (v2, (?, (?, ?))).
    exists v2.
    intuition.
    exists w.
    subst.
    exists p0.
    intuition.
  Qed.

  Lemma walk2_inv_fst_edge:
    forall x y w,
    Walk2 Edge x y w ->
    exists v, Edge (x, v).
  Proof.
    intros.
    apply walk2_inv_3 in H.
    destruct H as [(?,Hx)|(v2, (Hx,_))]. {
      subst.
      eauto.
    }
    eauto.
  Qed.

  Lemma reaches_inv_fst_edge:
    forall x y,
    Reaches Edge x y ->
    exists v, Edge (x, v).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using walk2_inv_fst_edge.
  Qed.

  Lemma ends_with_to_in:
    forall w (x:A),
    EndsWith w x ->
    exists v, List.In (v, x) w.
  Proof.
    induction w; intros. {
      apply ends_with_nil_inv in H.
      contradiction.
    }
    destruct w. {
      destruct a as (a1, a2).
      apply ends_with_inv_cons_nil in H.
      subst.
      eauto using in_eq.
    }
    apply ends_with_inv in H.
    apply IHw in H.
    destruct H as (v, Hi).
    eauto using in_cons.
  Qed.

  Lemma walk2_inv_snd_edge:
    forall x y w,
    Walk2 Edge x y w ->
    exists v, Edge (v, y).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply ends_with_to_in in H1.
    destruct H1 as (v, Hi).
    exists v.
    apply in_edge with (w:=w); auto.
  Qed.

  Lemma reaches_inv_snd_edge:
    forall x y,
    Reaches Edge x y ->
    exists v, Edge (v, y).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using walk2_inv_snd_edge.
  Qed.

  Variable edge_fun: forall a b c,
    Edge (a, b) ->
    Edge (a, c) ->
    b = c.

  Variable irreflexive:
    forall x,
    ~ clos_trans A (fun a b => Edge (a, b)) x x.

  Let walk2_irreflexive:
    forall x w, ~ Walk2 Edge x x w.
  Proof.
    intros.
    intros N.
    apply walk2_to_clos_trans with (R:=fun a b=>Edge (a,b)) in N. {
      apply irreflexive in N.
      contradiction.
    }
    tauto.
  Qed.

  (** If the edge behaves like a function, then there is only one path to
      arrive at each node. *)
  Lemma walk2_linear_fun:
    forall w1 a b w2,
    Walk2 Edge a b w1 ->
    Walk2 Edge a b w2 ->
    w1 = w2.
  Proof.
    induction w1; intros. {
      apply walk2_nil_inv in H.
      contradiction.
    }
    apply walk2_inv_3 in H.
    destruct H as [(Hr,?)|(v2,(He, (w, (e,(Hx, Hy)))))]. {
      inversion Hr; subst; clear Hr.
      apply walk2_inv_3 in H0.
      destruct H0 as [(Hr, ?)|(v2,(?,(w,(e,(Hx,Hy)))))]. {
        subst.
        reflexivity.
      }
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    inversion Hx; subst; clear Hx.
    apply walk2_inv_3 in H0.
    destruct H0 as [(?,?)|(v3,(Hf,(w',(e',(Hx,Hz)))))]. {
      subst.
      assert (v2 = b) by eauto.
      subst.
      apply walk2_irreflexive in Hy.
      contradiction.
    }
    subst.
    assert (v3 = v2) by eauto.
    subst.
    apply IHw1 in Hz; auto.
    inversion Hz; subst; clear Hz.
    reflexivity.
  Qed.
End LinWalk2.

Section BigStep.
  Variable A:Type.
  Variable R: relation A.
  Variable Value: A -> Prop.
  Inductive BigStep: A -> A -> Prop :=
  | big_step_cons:
    forall x y z,
    R x y ->
    BigStep y z ->
    BigStep x z
  | big_step_nil:
    forall x,
    Value x ->
    BigStep x x.
End BigStep.
