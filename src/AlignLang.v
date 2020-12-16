Require Import AccExp.
Require Import Tasks.
Require Import Conc.
Require Import NExp.
Require Import RExp.
Require Import Var.
Require Import WLang.
Require Import Tictac.
Require Import Util.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.
Import NExpNotations.
Import RExpNotations.
Import CLangNotations.

Open Scope exp_scope.
Open Scope lang_scope.

Section Defs.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Inductive n_inst :=
  | NSync: Conc.inst -> n_inst
  | NSeq: n_inst -> n_inst -> n_inst
  | NFor : n_inst -> var -> range -> n_inst -> n_inst.  

  Fixpoint subst x v i :=
    match i with
    | NSync c => NSync (Conc.i_subst x v c)
    | NSeq i1 i2 => NSeq (subst x v i1) (subst x v i2)
    | NFor P y r Q =>
      let Q' := if VAR.eq_dec x y
        then Q
        else subst x v Q
      in
      NFor (subst x v P) y (r_subst x v r) Q'
    end.

  Fixpoint Var x P :=
    match P with
    | NSync c => Conc.Var x c
    | NSeq P Q => Var x P \/ Var x Q
    | NFor P y _ Q =>
      x = y \/
      Var x P \/ Var x Q
    end.

  Definition p_inst := (n_inst * Conc.inst) % type.

  Fixpoint n_seq (c:Conc.inst) (n:n_inst) : n_inst :=
    match n with
    | NSync c' => NSync (c_seq c c')
    | NSeq i j => NSeq (n_seq c i) j
    | NFor i x r j => NFor (n_seq c i) x r j
    end.

  Definition p_seq (i:p_inst) (j:p_inst) :=
   match i, j with
    | (i,ci), (j, cj) => (NSeq i (n_seq ci j), cj)
    end.


  Inductive IPairIn (p:access_val*access_val) : n_inst -> Prop :=
  | i_pair_in_sync:
    (* 
       p \in c
       ------------
       p \in c;sync
      *)
    forall c,
    CPairIn p c ->
    IPairIn p (NSync c)
  | i_pair_in_seq_l:
    forall i j,
    IPairIn p i ->
    IPairIn p (NSeq i j)
  | i_pair_in_seq_r:
    forall i j,
    IPairIn p j ->
    IPairIn p (NSeq i j)
  | i_pair_in_for_1:
    forall x r i j,
    IPairIn p i ->
    IPairIn p (NFor i x r j)
  | i_pair_in_for_2:
    forall r n i j x,
    RPick r n ->
    IPairIn p (subst x (NNum n) j) ->
    IPairIn p (NFor i x r j)
  .

  (*
    p \in P \/ p \in c 
    ------------------
    p \in [P, c]
    *)

  Definition PPairIn a (p:p_inst) : Prop :=
    match p with
    | (i, c) => IPairIn a i \/ CPairIn a c
    end.

  Inductive IFirst a : n_inst -> Prop :=
  | i_first_sync:
    forall c,
    CIn a c ->
    IFirst a (NSync c)
  | i_first_seq:
    forall P Q,
    IFirst a P ->
    IFirst a (NSeq P Q)
  | i_first_for:
    forall P x r Q,
    IFirst a P ->
    IFirst a (NFor P x r Q)
  .

  Definition DRF (P:p_inst) :=
    forall p,
    PPairIn p P ->
    access_safe (fst p) (snd p).

End Defs.


Module PLangNotations.
  Import Conc.CLangNotations.
  Infix ";" := NSeq (at level 50, only printing)
    : lang_scope.
  Notation "c [ x := v ]" := (subst x v c) (at level 30, only printing)
    : lang_scope.
  Infix ";;" := n_seq (at level 50, only printing)
    : lang_scope.
  Notation "P1 ';' 'for' x 'in' r '{' P2 '}' " := (NFor P1 x r P2) (at level 50, only printing)
    : lang_scope.
  Infix "∈" := IPairIn (at level 30, only printing)
    : lang_scope.
End PLangNotations.

Open Scope lang_scope.

Section Props.
  Import PLangNotations.
  Import ALangNotations.
  Context `{T:Tasks}.
  Context {A:Access}.

  Lemma n_seq_seq:
    forall i c c',
    n_seq (Conc.Seq c c') i = n_seq c (n_seq c' i).
  Proof.
    induction i; intros.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHi1.
      auto.
    - simpl.
      rewrite IHi1.
      reflexivity.
  Qed.


  Lemma n_seq_c_seq:
    forall i c1 c2,
    n_seq (c_seq c1 c2) i = n_seq c1 (n_seq c2 i).
  Proof.
    induction i; intros; simpl.
    - rewrite c_seq_seq.
      auto.
    - rewrite IHi1.
      auto.
    - rewrite IHi1.
      auto.
  Qed.

  (*
  
   ---------------
    p \in [[ P ]]
  
    *)

  Lemma snd_p_seq:
    forall i j,
    snd (p_seq i j) = snd j.
  Proof.
    intros (i, ci) (j, cj).
    destruct i; intros; simpl; auto.
  Qed.

  Lemma p_seq_inv_snd:
    forall P Q c Q' c',
    p_seq P (Q, c) = (Q', c') ->
    c' = c.
  Proof.
    intros.
    destruct P as (P, c1).
    simpl in *.
    inversion H; subst; clear H.
    reflexivity.
  Qed.

  Lemma i_first_inv_n_seq:
    forall a c P,
    IFirst a (n_seq c P) ->
    CIn a c \/ IFirst a P.
  Proof.
    intros a c P H.
    remember (n_seq _ _) as Q.
    generalize dependent c.
    generalize dependent P.
    induction H; intros P' c' Heq; simpl in Heq.
    - destruct P'; simpl in Heq; invc Heq.
      apply c_in_inv_c_seq in H.
      intuition.
      right.
      auto using i_first_sync.
    - destruct P'; simpl in Heq; invc Heq.
      assert (IHIFirst := IHIFirst _ _ eq_refl).
      intuition.
      right.
      constructor.
      assumption.
    - destruct P'; simpl in Heq; invc Heq.
      assert (IHIFirst := IHIFirst _ _ eq_refl).
      intuition.
      right.
      constructor.
      assumption.
  Qed.

  Definition NOneOf (p:access_val*access_val) c P :=
    let (a1, a2) := p in
    (CIn a1 c /\ IFirst a2 P)
    \/
    (CIn a2 c /\ IFirst a1 P).

  Lemma i_pair_in_inv_n_seq:
    forall a c P,
    IPairIn a (n_seq c P) ->
    CPairIn a c \/ IPairIn a P \/ NOneOf a c P.
  Proof.
    intros a c P H.
    remember (n_seq _ _) as Q.
    generalize dependent c.
    generalize dependent P.
    induction H; intros P' c' Heq; simpl in Heq; destruct P'; simpl in Heq; invc Heq.
    - apply c_pair_in_inv_c_seq in H.
      destruct a as (a1, a2).
      unfold Conc.OneOf in *.
      simpl.
      intuition.
      + auto using c_pair_in_def.
      + right.
        right.
        auto using i_first_sync.
      + right.
        right.
        auto using i_first_sync.
      + auto using i_pair_in_sync, c_pair_in_def.
    - assert (IHIPairIn := IHIPairIn _ _ eq_refl).
      intuition.
      + auto using i_pair_in_seq_l.
      + unfold NOneOf in *.
        destruct a as (a1, a2).
        intuition.
        * right.
          auto using i_first_seq.
        * right.
          auto using i_first_seq.
    - eauto using i_pair_in_seq_r.
    - assert (IHIPairIn := IHIPairIn _ _ eq_refl).
      intuition.
      + auto using i_pair_in_for_1.
      + unfold NOneOf in *.
        destruct a as (a1, a2).
        intuition.
        * right.
          auto using i_first_for.
        * right.
          auto using i_first_for.
    - right.
      eauto using i_pair_in_for_2.
  Qed.

  Lemma subst_n_seq:
    forall P x v c,
    subst x v (n_seq c P) =
      n_seq (Conc.i_subst x v c) (subst x v P).
  Proof.
    induction P; simpl; intros.
    - rewrite c_subst_c_seq.
      auto.
    - rewrite IHP1.
      auto.
    - rewrite IHP1.
      auto.
  Qed.

  Lemma p_pair_in_sync:
    forall a c,
    PPairIn a (NSync c, Skip) ->
    WLang.IPairIn a (WSync c).
  Proof.
    intros a c Hi.
    simpl in *.
    destruct Hi as [Hi|Hi].
    - invc Hi.
      auto using WLang.i_pair_in_sync.
    - apply c_pair_in_skip in Hi.
      contradiction.
  Qed.

  Definition c_seq c (P:p_inst) :=
    let (Q, c2) := P in
    (n_seq c Q, c2).

  Definition p_subst x v (P:p_inst) :=
    match P with
    (Q, c) => (subst x v Q, Conc.i_subst x v c)
    end.

  Lemma n_seq_subst:
    forall x v c P,
    subst x v (n_seq c P) = n_seq (Conc.i_subst x v c) (subst x v P).
  Proof.
    induction P; intros; simpl; auto.
    - rewrite Conc.c_seq_subst.
      reflexivity.
    - rewrite IHP1.
      reflexivity.
    - rewrite IHP1.
      auto.
  Qed.

  Fixpoint IFree (P : n_inst)  (x : var) {struct P} : Prop :=
    match P with
    | NSync c => Conc.CFree c x
    | NSeq P Q => IFree P x \/ IFree Q x
    | NFor P y r Q =>
        IFree P x \/ RFree r x \/ (x <> y /\ IFree Q x)
    end.

  Lemma i_free_inv_subst_eq:
    forall x v P,
    ~ Var x P ->
    IFree (subst x v P) x ->
    NFree v x.
  Proof.
    induction P; simpl; intros.
    - eauto using c_free_inv_subst_eq.
    - intuition.
    - intuition.
      + eauto using r_free_inv_subst_eq.
      + destruct (Set_VAR.MF.eq_dec x v0) as [?|_]; try contradiction.
        auto.
  Qed.

  Lemma i_first_subst:
    forall a x v1 P,
    IFirst a (subst x v1 P) ->
    forall n,
    NStep v1 n ->
    forall v2,
    NStep v2 n ->
    IFirst a (subst x v2 P).
  Proof.
  Admitted.

  Lemma i_pair_in_subst:
    forall p x e1 P n,
    NStep e1 n ->
    IPairIn p (subst x e1 P) ->
    forall e2,
    NStep e2 n ->
    IPairIn p (subst x e2 P).
  Proof.
  Admitted.

  Lemma subst_subst_eq_1:
    forall e1 e2 x P,
    subst x e1 (subst x e2 P) = subst x (n_subst x e1 e2) P.
  Proof.
    induction P; intros; simpl.
    - rewrite i_subst_subst_eq_1.
      reflexivity.
    - rewrite IHP1.
      rewrite IHP2.
      reflexivity.
    - rewrite IHP1.
      rewrite r_subst_subst_eq_1.
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      rewrite IHP2.
      reflexivity.
  Qed.

  Definition IClosed P :=
    forall x,
    ~ IFree P x.

  Lemma i_closed_inv_r:
    forall P v r Q,
    IClosed (NFor P v r Q) ->
    RClosed r.
  Proof.
    unfold IClosed, RClosed.
    intros.
    intros N.
    assert (H := H x).
    simpl in *.
    intuition.
  Qed.



  Lemma eq_n_seq_def:
    forall P Q P' Q',
    P = P' ->
    Q = Q' ->
    n_seq P Q = n_seq P' Q'.
  Proof.
    intros; subst.
    reflexivity.
  Qed.

  Lemma eq_n_for_def:
    forall P P' x x' r r' Q Q',
    P = P' ->
    x = x' ->
    r = r' ->
    Q = Q' ->
    NFor P x r Q = NFor P' x' r' Q'.
  Proof.
    intros.
    subst.
    reflexivity.
  Qed.

  Lemma subst_subst_neq_5:
    forall P x y e1 e2,
    y <> x ->
    NClosed e1 ->
    ~ Var y P ->
    subst y e1 (subst x e2 P) = subst x (n_subst y e1 e2) (subst y e1 P).
  Proof.
    induction P; intros.
    - simpl.
      rewrite Conc.c_subst_subst_neq_5; auto.
    - simpl in *.
      rewrite IHP1; auto.
      rewrite IHP2; auto.
    - simpl in *.
      rename v into z.
      (* P = NFor P z r Q *) 
      simpl in *.
      rewrite IHP1; auto.
      apply eq_n_for_def; auto. {
        rewrite r_subst_subst_neq_5; auto.
      }
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        (* z = y *)
        destruct (Set_VAR.MF.eq_dec x z). {
          subst.
          contradiction.
        }
        rename z into y.
        intuition.
        (* P = P; for y \in r { Q } *)
        (* subst y e1 (subst x e2 P) != subst x e1 (subst x e2 P) *)
        (* z <> x *)
        (* rewrite n_subst_not_free; auto. *)
      }
      destruct (Set_VAR.MF.eq_dec x z). {
        subst.
        reflexivity.
      }
      rewrite IHP2; auto.
  Qed.

  Fixpoint Distinct P :=
    match P with
    | NSync _ => True
    | NSeq P Q => Distinct P /\ Distinct Q
    | NFor P x _ Q => Distinct P /\ ~ Var x Q /\ Distinct Q
    end.

  Definition PDistinct (P:p_inst) :=
    let (P, c) := P in
    Distinct P /\ Conc.Distinct c.

  Definition PVar x (P:p_inst) :=
    let (P, c) := P in
    Var x P \/ Conc.Var x c.

  Lemma c_var_inv_c_seq:
    forall x c1 c2,
    Conc.Var x (Conc.c_seq c1 c2) ->
    Conc.Var x c1 \/ Conc.Var x c2.
  Proof.
    induction c1; simpl; intros; try (intuition; fail).
    apply IHc1_1 in H.
    intuition.
    apply IHc1_2 in H0.
    intuition.
  Qed.

  Lemma var_inv_n_seq:
    forall x P c,
    Var x (n_seq c P) ->
    Conc.Var x c \/ Var x P.
  Proof.
    induction P; simpl; intros.
    - apply c_var_inv_c_seq in H.
      intuition.
    - intuition.
      apply IHP1 in H0.
      intuition.
    - intuition.
      apply IHP1 in H.
      intuition.
  Qed.

  Lemma var_inv_subst:
    forall x y (v:nexp) P,
    Var x (subst y v P) ->
    Var x P.
  Proof.
    induction P; simpl; intros.
    - eauto using c_var_inv_subst.
    - intuition.
    - intuition.
      destruct (Set_VAR.MF.eq_dec x v0). {
        intuition.
      }
      intuition.
      destruct (Set_VAR.MF.eq_dec y v0). {
        subst.
        intuition.
      }
      intuition.
  Qed.


  Lemma distinct_subst:
    forall P,
    Distinct P ->
    forall x v,
    Distinct (subst x v P).
  Proof.
    induction P; simpl; intros; auto. {
      destruct H; eauto.
    }
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      intuition.
    }
    simpl.
    intuition.
    rename_hyp (Var v _) as Hv.
    apply var_inv_subst in Hv.
    contradiction.
  Qed.

  Lemma i_first_n_seq_l:
    forall a c,
    CIn a c ->
    forall P,
    IFirst a (n_seq c P).
  Proof.
    induction P; simpl; intros.
    - constructor.
      auto using c_in_c_seq_l.
    - auto using i_first_seq.
    - constructor.
      auto.
  Qed.

  Lemma i_first_n_seq_r:
    forall a P,
    IFirst a P ->
    forall c,
    IFirst a (n_seq c P).
  Proof.
    induction P; intros; invc H; constructor.
    + auto using c_in_c_seq_r.
    + auto.
    + auto.
  Qed.

End Props.
