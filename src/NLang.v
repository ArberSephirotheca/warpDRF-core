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
    p \in P \/ p \in c 
    ------------------
    p \in [P, c]
    *)

  Definition PPairIn a (p:p_inst) : Prop :=
    match p with
    | (i, c) => IPairIn a i \/ CPairIn a c
    end.

  Definition PLast a (P:p_inst) :=
    match P with
    | (Q, c) => Conc.CIn a c
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

  Definition  PFirst a (P:p_inst) :=
    match P with
    | (Q, _) => IFirst a Q
    end.

  Definition POneOf (p:access_val * access_val) (P:p_inst) (Q:p_inst) : Prop :=
     let (a1, a2) := p in
     (PLast a1 P /\ PFirst a2 Q)
     \/
     (PLast a2 P /\ PFirst a1 Q).

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
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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

  Fixpoint tr (w:w_inst) : p_inst :=
    match w with
    | WSync c => (NSync c, Conc.Skip)
    | WSeq P Q =>
      let (P', c1) := tr P in
      let (Q', c2) := tr Q in
      (NSeq P' (n_seq c1 Q'), c2)
    | WFor c1 x (e1, e2) P c2 =>
      let (P_x, c_x) := tr P in
      let P_e1 := subst x e1 P_x in
      let c_e1 := i_subst x e1 c_x in
      let dec_x := NBin NMinus (NVar x) (NNum 1) in
      let dec_e2 := NBin NMinus e2 (NNum 1) in
      let c_dec_x := i_subst x dec_x c_x in
      let c2_dec_x := i_subst x dec_x c2 in
      let c_dec_e2 := i_subst x dec_e2 c_x in
      let c2_dec_e2 := i_subst x dec_e2 c2 in
      (NFor (n_seq c1 P_e1) x (NBin NPlus (NNum 1) e1, e2)
                        (n_seq c_dec_x (n_seq c2_dec_x P_x)),
                     Conc.c_seq c_dec_e2 c2_dec_e2)
    end.

  Let eq_n_seq_def:
    forall P Q P' Q',
    P = P' ->
    Q = Q' ->
    n_seq P Q = n_seq P' Q'.
  Proof.
    intros; subst.
    reflexivity.
  Qed.

  Let eq_n_for_def:
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

  Fixpoint IFree (P : n_inst)  (x : var) {struct P} : Prop :=
    match P with
    | NSync c => Conc.CFree c x
    | NSeq P Q => IFree P x \/ IFree Q x
    | NFor P y r Q =>
        IFree P x \/ RFree r x \/ (x <> y /\ IFree Q x)
    end.

  Lemma i_free_inv_subst_eq:
    forall x v P,
    IFree (subst x v P) x ->
    NFree v x.
  Proof.
    induction P; simpl; intros.
    - eauto using c_free_inv_subst_eq.
    - destruct H; auto.
    - destruct H as [H|[H|(?,H)]];
      eauto using r_free_inv_subst_eq.
      destruct (Set_VAR.MF.eq_dec x v0) as [?|_]; try contradiction.
      auto.
  Qed.

  Lemma c_pair_in_subst:
    forall p x e1 c n,
    NStep e1 n ->
    CPairIn p (i_subst x e1 c) ->
    forall e2,
    NStep e2 n ->
    CPairIn p (i_subst x e2 c).
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

  Lemma var_inv_tr:
    forall x P,
    PVar x (tr P) ->
    WVar x P.
  Proof.
    induction P; simpl; intros; try (intuition; fail).
    - destruct (tr P1) as (P1', c1).
      destruct (tr P2) as (P2', c2).
      simpl in *.
      destruct H as [[H|H]|H]; auto.
      apply var_inv_n_seq in H.
      intuition.
    - destruct r as (e1, e2).
      destruct (tr P) as (Px, cx).
      simpl in *.
      intuition.
      + rename_hyp (Var _ (n_seq _ _)) as Hc.
        apply var_inv_n_seq in Hc.
        intuition.
        rename_hyp (Var _ (subst _ _ _)) as Hv.
        apply var_inv_subst in Hv.
        intuition.
      + rename_hyp (Var _ (n_seq _ _)) as Hv.
        apply var_inv_n_seq in Hv.
        intuition.
        rename_hyp (Conc.Var _ _) as Hc.
        apply c_var_inv_subst in Hc.
        intuition.
        rename_hyp (Var _ (n_seq _ _)) as Hc.
        apply var_inv_n_seq in Hc.
        intuition.
        rename_hyp (Conc.Var _ _) as Hc.
        apply c_var_inv_subst in Hc.
        intuition.
      + rename_hyp (Conc.Var _ (Conc.c_seq _ _ )) as Hc.
        apply c_var_inv_c_seq in Hc.
        intuition.
        * rename_hyp (Conc.Var _ (i_subst _ _ _)) as Hc.
          apply c_var_inv_subst in Hc.
          intuition.
        * rename_hyp (Conc.Var _ (i_subst _ _ _)) as Hc.
          apply c_var_inv_subst in Hc.
          intuition.
  Qed.

  Lemma var_inv_tr_l:
    forall x P P_x c_x,
    Var x P_x ->
    tr P = (P_x, c_x) ->
    WVar x P.
  Proof.
    intros.
    assert (PVar x (tr P)). {
      rewrite H0.
      simpl.
      auto.
    }
    auto using var_inv_tr.
  Qed.

  Lemma var_inv_tr_r:
    forall x P P_x c_x,
    Conc.Var x c_x ->
    tr P = (P_x, c_x) ->
    WVar x P.
  Proof.
    intros.
    assert (PVar x (tr P)). {
      rewrite H0.
      simpl.
      auto.
    }
    auto using var_inv_tr.
  Qed.

  Lemma tr_subst:
    forall P e x,
    NClosed e ->
    ~ WVar x P ->
    (* [[ P ]] [x := e ] = [[ P[x := e] ]] *)
    p_subst x e (tr P) = tr (w_subst x e P).
  Proof.
    induction P; intros e' y Hc Hd; simpl in *.
    - auto.
    - destruct (tr P1) as (P1_x, c1_x) eqn:Ht1.
      destruct (tr P2) as (P2_x, c2_x) eqn:Ht2.
      simpl.
      rewrite <- IHP1; auto; clear IHP1.
      rewrite <- IHP2; auto; clear IHP2.
      destruct (p_subst y e' (P1_x, c1_x)) as (xP1_x, xc1_x) eqn:Ht1x.
      destruct (p_subst y e' (P2_x, c2_x)) as (xP2_x, xc2_x) eqn:Ht2x.
      simpl in *.
      invc Ht1x.
      invc Ht2x.
      repeat rewrite subst_n_seq.
      auto.
    - rename v into x.
      destruct r as (e1, e2).
      simpl.
      destruct (tr P) as (P_x, c_x) eqn:Ht.
      assert (~ Var y P_x). {
        intros N.
        eapply var_inv_tr_l with (x:=y) in N; eauto.
      }
      assert (~ Conc.Var y c_x). {
        intros N.
        eapply var_inv_tr_r with (x:=y) in N; eauto.
      }
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        simpl.
        rewrite Ht.
        remove_eq x x.
        rewrite subst_n_seq.
        rewrite c_seq_subst.
        apply eq_pair_def; auto. {
          apply eq_n_for_def; auto.
          apply eq_n_seq_def; auto.
          rewrite subst_subst_eq_1.
          reflexivity.
        }
        apply eq_c_seq_def. {
          repeat rewrite i_subst_subst_eq_1.
          simpl.
          reflexivity.
        }
        repeat rewrite i_subst_subst_eq_1.
        simpl.
        reflexivity.
      }
      simpl.
      (* y <> x *)
      remove_eq y x.
      simpl.
      destruct (tr (w_subst y e' P)) as (P_t, c_t) eqn:Ht'.
      repeat rewrite subst_n_seq.
      repeat rewrite c_seq_subst.
      apply eq_pair_def. {
        apply eq_n_for_def; auto. {
          apply eq_n_seq_def; auto.
          rewrite <- IHP in Ht'; auto.
          2: { intuition. }
          invc Ht'.
          rewrite subst_subst_neq_5; auto.
        }
        apply eq_n_seq_def. {
          rewrite <- IHP in Ht'; auto.
          2: { intuition. }
          simpl in Ht'.
          invc Ht'.
          rewrite i_subst_subst_neq_3; auto.
          simpl.
          intuition.
        }
        apply eq_n_seq_def. {
          rewrite i_subst_subst_neq_3; auto.
          simpl.
          intuition.
        }
        rewrite <- IHP in Ht'; auto.
        2: { intuition. }
        simpl in Ht'.
        invc Ht'.
        reflexivity.
      }
      rewrite <- IHP in Ht'; auto.
      2: { intuition. }
      simpl in Ht'.
      invc Ht'.
      apply eq_c_seq_def. {
        rewrite c_subst_subst_neq_5; auto.
      }
      rewrite c_subst_subst_neq_5; auto.
      intuition.
  Qed.

  Lemma tr_to_subst:
    forall P P_x c_x,
    tr P = (P_x, c_x) ->
    forall x v,
    NClosed v ->
    ~ WVar x P ->
    tr (w_subst x v P) = (subst x v P_x, i_subst x v c_x).
  Proof.
    intros.
    rewrite <- tr_subst; auto.
    rewrite H.
    auto.
  Qed.

(*
  Fixpoint tr_first (P:w_inst) :=
    match P with
    | WSync c => c
    | WSeq P _ => tr_first P
    | WFor c1 x (e1, e2) P _ =>
      Conc.c_seq c1 (i_subst x e1 (tr_first P))
    end.
*)

  Lemma i_first_n_seq_l:
    forall a c,
    CIn a c ->
    forall P,
    IFirst a (n_seq c P).
  Proof.
  Admitted.

  Lemma i_first_n_seq_r:
    forall a P,
    IFirst a P ->
    forall c,
    IFirst a (n_seq c P).
  Proof.
  Admitted.

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

  (* ----------------------- GET FIRST ------------------------ *)

  Lemma get_first_tr_1:
    forall P c,
    GetFirst P c ->
    WLang.Distinct P ->
    forall a,
    CIn a c ->
    IFirst a (fst (tr P)).
  Proof.
    intros P c H.
    induction H; simpl; intros Hd a Hc.
    - constructor.
      auto.
    - destruct (tr P) as (Px1, cx1) eqn:Ht1.
      destruct (tr Q) as (Px2, cx2) eqn:Ht2.
      simpl.
      apply i_first_seq.
      intuition.
    - destruct r as (e1, e2).
      destruct (tr P) as (Px, cx) eqn:Ht.
      simpl.
      apply c_in_inv_c_seq in Hc.
      constructor.
      destruct Hc as [Hc|Hc]. {
        auto using i_first_n_seq_l.
      }
      apply IHGetFirst in Hc.
      apply tr_to_subst with (x:=x) (v:=NNum n) in Ht.
      2: { eauto using n_step_to_closed, n_step_num. }
      2: { intuition. }
      2: { apply WLang.distinct_subst. intuition. }
      rewrite Ht in Hc.
      simpl in Hc.
      apply i_first_n_seq_r.
      apply i_first_subst with
        (v1:=NNum n) (n:=n);
        auto using n_step_num.
      eauto using r_first_to_eq.
  Qed.

  Lemma get_first_tr_2:
    forall P c,
    GetFirst P c ->
    WLang.Distinct P ->
    forall a,
    IFirst a (fst (tr P)) ->
    CIn a c.
  Proof.
    intros P c H.
    induction H; simpl; intros Hd a Hf; invc Hf.
    - assumption.
    - destruct (tr P).
      destruct (tr Q).
      invc H0.
    - destruct (tr P) as (Px1, cx1) eqn:Ht1.
      destruct (tr Q) as (Px2, cx2) eqn:Ht2.
      simpl in *.
      destruct Hd.
      invc H0.
      eauto.
    - destruct (tr P) as (P_t, c_P) eqn:HP.
      destruct (tr Q) as (Q_t, c_Q) eqn:HQ.
      simpl in *.
      destruct Hd.
      invc H0.
    - destruct r, (tr P).
      invc H1.
    - destruct r, (tr P).
      invc H1.
    - destruct r as (e1, e2).
      destruct (tr P) as (P_t, c_P) eqn:HP.
      simpl in *.
      invc H1.
      rename_hyp (IFirst _ _) as Hi.
      apply i_first_inv_n_seq in Hi.
      destruct Hi as [Hi|Hi].
      + auto using c_in_c_seq_l.
      + apply c_in_c_seq_r.
        apply IHGetFirst. {
          apply WLang.distinct_subst.
          intuition.
        }
        apply tr_to_subst with (x:=x) (v:=NNum n) in HP.
        2: { eauto using n_step_to_closed, n_step_num. }
        2: { intuition. }
        rewrite HP.
        simpl.
        apply i_first_subst with
          (v1:=e1) (n:=n); auto.
        eapply r_first_to_eq; eauto.
        auto using n_step_num.
  Qed.

  Corollary i_first_tr:
    forall P,
    CanRun P ->
    WLang.Distinct P ->
    forall a,
    IFirst a (fst (tr P)) <->
    WLang.IFirst a P.
  Proof.
    intros P Hc Hd.
    apply get_first_exists in Hc.
    destruct Hc as (c, Hg).
    split; intros.
    - eapply get_first_tr_2 in H; eauto.
      rewrite get_first_spec; eauto.
    - eapply get_first_tr_1; eauto.
      rewrite <- get_first_spec; eauto.
  Qed.

  Lemma i_first_tr_1:
    forall v r n P x P_x c_x,
    WLang.Distinct P ->
    CanRun (w_subst x (NNum n) P) ->
    tr P = (P_x, c_x) ->
    NStep v n ->
    RPick r n ->
    ~ WVar x P ->
    forall a,
    IFirst a (subst x v P_x) ->
    WLang.IFirst a (w_subst x v P).
  Proof.
    intros.
    rename_hyp (tr _ = _) as Ht.
    apply tr_to_subst with (x:=x) (v:=v) in Ht;
      eauto using n_step_to_closed.
    assert (CanRun (w_subst x v P)). {
      eauto using can_run_subst.
    }
    apply i_first_tr; auto. {
      auto using distinct_subst.
    }
    rewrite Ht.
    simpl.
    assumption.
  Qed.

  (* -------------------------------- GET LAST ------------------------ *)

  Lemma get_last_tr_1:
    forall P c,
    GetLast P c ->
    WLang.Distinct P ->
    ~ WVar TID P ->
    forall a,
    CIn a c ->
    CIn a (snd (tr P)).
  Proof.
    intros P c H.
    induction H; simpl; intros Hd Htid a Hc.
    - assumption.
    - destruct (tr P) as (P',c_p) eqn:Ht1.
      destruct (tr Q) as (Q',c_q) eqn:Ht2.
      intuition.
    - destruct r as (e1, e2).
      destruct (tr P) as (P',c_p) eqn:Ht1.
      simpl.
      apply c_in_inv_c_seq in Hc.
      apply tr_to_subst with (x:=x) (v:=NNum n) in Ht1;
        eauto using n_step_to_closed, n_step_num.
      2: { intuition. }
      destruct Hc as [Hc|Hc].
      + apply c_in_c_seq_l.
        apply IHGetLast in Hc; clear IHGetLast.
        2: { apply WLang.distinct_subst. intuition. }
        2: { intros N. apply wvar_inv_subst in N. intuition. }
        rewrite Ht1 in Hc.
        simpl in *.
        apply c_in_subst with (v:=NNum n) (n0 := n);
          eauto using n_step_num, r_last_to_eq.
      + apply c_in_c_seq_r.
        apply c_in_subst with (v:=NNum n) (n0 := n);
          eauto using n_step_num, r_last_to_eq.
  Qed.

  Lemma get_last_tr_2:
    forall P c,
    GetLast P c ->
    WLang.Distinct P ->
    ~ WVar TID P ->
    forall a,
    CIn a (snd (tr P)) ->
    CIn a c.
  Proof.
    intros P c H.
    induction H; simpl; intros Hd Hv a Hf; invc Hf.
    - invc H0.
    - destruct (tr P).
      destruct (tr Q) as (Q',c_q) eqn:Ht2.
      intuition.
      simpl in *.
      auto using c_in_def.
    - simpl in *.
      destruct r as (e1, e2).
      destruct (tr P) as (P',c_p) eqn:Ht1.
      simpl in *.
      apply tr_to_subst with (x:=x) (v:=NNum n) in Ht1;
        eauto using n_step_to_closed, n_step_num.
      2: { intuition. }
      rename_hyp (IIn _ _) as Hi.
      apply i_in_inv_c_seq in Hi.
      destruct Hi as [Hi|Hi].
      + apply c_in_c_seq_l.
        apply c_in_def in Hi; auto.
        rewrite Ht1 in *.
        simpl in *.
        apply IHGetLast; clear IHGetLast.
        * intuition.
          auto using WLang.distinct_subst.
        * intros N. apply wvar_inv_subst in N. intuition.
        * apply c_in_subst with (v:=NBin NMinus e2 1) (n0 := n);
          eauto using n_step_num, r_last_to_eq.
      + apply c_in_def in Hi; auto.
        apply c_in_c_seq_r.
        apply c_in_subst with (v:=NBin NMinus e2 1) (n0 := n);
          eauto using n_step_num, r_last_to_eq.
  Qed.

  Corollary i_last_tr:
    forall P,
    CanRun P ->
    WLang.Distinct P ->
    ~ WVar TID P ->
    forall a,
    CIn a (snd (tr P)) <->
    WLang.ILast a P.
  Proof.
    intros P Hc Hd Hv.
    apply get_last_exists in Hc.
    destruct Hc as (c, Hg).
    split; intros.
    - eapply get_last_tr_2 in H; eauto.
      rewrite get_last_spec; eauto.
    - eapply get_last_tr_1; eauto.
      rewrite <- get_last_spec; eauto.
  Qed.

  Lemma i_last_tr_1:
    forall v r n P x P_x c_x,
    WLang.Distinct P ->
    CanRun (w_subst x (NNum n) P) ->
    tr P = (P_x, c_x) ->
    NStep v n ->
    RPick r n ->
    ~ WVar TID P ->
    ~ WVar x P ->
    forall a,
    CIn a (i_subst x v c_x) ->
    WLang.ILast a (w_subst x v P).
  Proof.
    intros.
    rename_hyp (tr _ = _) as Ht.
    apply tr_to_subst with (x:=x) (v:=v) in Ht;
      eauto using n_step_to_closed.
    assert (CanRun (w_subst x v P)). {
      eauto using can_run_subst.
    }
    apply i_last_tr; auto.
    - auto using distinct_subst.
    - intros N.
      apply wvar_inv_subst in N.
      intuition.
    - rewrite Ht.
      simpl.
      assumption.
  Qed.

  (* -------------------- IPairIn Translation ------------------------ *)

  Lemma i_pair_in_tr_for_1:
    forall p c1 x r P c2,
    (forall n,
     RPick r n ->
     forall p,
     PPairIn p (tr (w_subst x n P)) -> WLang.IPairIn p (w_subst x n P)) ->
    ~ WVar x P ->
    forall P_x c_x,
    tr P = (P_x, c_x) ->
    forall e n,
    RPick r n ->
    NStep e n ->
    IPairIn p (subst x e P_x) ->
    WLang.IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    eapply WLang.i_pair_in_for_1 with (e0:=NNum n); eauto using n_step_num.
    apply H; auto.
    assert (IPairIn p (subst x (NNum n) P_x)). {
      eauto using i_pair_in_subst, n_step_num.
    }
    rewrite <- tr_subst; auto using n_closed_num.
    rewrite H1.
    simpl.
    auto.
  Qed.

  Lemma i_pair_in_tr_for_2:
    forall p c1 x r P c2,
    (forall n,
     RPick r n ->
     forall p,
     PPairIn p (tr (w_subst x n P)) -> WLang.IPairIn p (w_subst x n P)) ->
    ~ WVar x P ->
    forall P_x c_x,
    tr P = (P_x, c_x) ->
    forall e n,
    RPick r n ->
    NStep e n ->
    CPairIn p (i_subst x e c_x) ->
    WLang.IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    eapply WLang.i_pair_in_for_1 with (e0:=NNum n); eauto using n_step_num.
    apply H; auto.
    apply tr_to_subst with (x:=x) (v:=NNum n) in H1; auto using n_closed_num.
    rewrite H1.
    simpl.
    right.
    eapply c_pair_in_subst; eauto using n_step_num.
  Qed.

  Lemma n_step_inv_succ:
    forall e n,
    NStep (NBin NPlus (NNum 1) e) n -> 
    exists n', NStep e n' /\ n = S n'.
  Proof.
    intros.
    invc H.
    assert (n1 = 1) by eauto using n_step_num, n_step_fun.
    subst.
    exists n2.
    split; eauto.
  Qed.

  Lemma r_pick_impl_1:
    forall e1 e2 n,
    RPick (NBin NPlus (NNum 1) e1, e2) n ->
    RPick (e1, e2) n.
  Proof.
    intros.
    invc H.
    apply n_step_inv_succ in H2.
    destruct H2 as (n', (Hn1, ?)).
    subst.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_pick_impl_2:
    forall e1 e2 m,
    RPick ((NBin NPlus 1 e1), e2) m ->
    RPick (e1, e2) (Nat.sub m 1).
  Proof.
    intros.
    invc H.
    rename_hyp (NStep _ n1) as Hn1.
    apply n_step_inv_succ in Hn1.
    destruct Hn1 as (n', (Hn1, ?)).
    subst.
    eapply r_pick_def; eauto.
    lia.
  Qed.

  Lemma r_pick_impl_3:
    forall e1 e2 m,
    RPick ((NBin NPlus 1 e1), e2) m ->
    exists n, m = S n /\ RPick2 (e1, e2) n.
  Proof.
    intros.
    invc H.
    apply n_step_inv_succ in H2.
    destruct H2 as (n', (Hn1, ?)).
    subst.
    destruct m. {
      lia.
    }
    exists m.
    split; auto.
    eapply r_pick2_def; eauto.
    - lia.
    - lia.
  Qed.

  Lemma r_pick_impl_4:
    forall e1 e2 n,
    RPick (e1, e2) n ->
    exists m, RPick (e1, e2) m /\ NStep (NBin NMinus e2 (NNum 1)) m.
  Proof.
    intros.
    invc H.
    destruct n2. {
      lia.
    }
    exists n2.
    split. {
      eapply r_pick_def; eauto.
      lia.
    }
    assert (rx: n2 = S n2 - 1) by lia.
    rewrite rx.
    apply n_step_bin; auto using n_step_num.
  Qed.

  Lemma n_step_succ_minus_one:
    forall n,
    NStep (NBin NMinus (S n) 1) n.
  Proof.
    intros.
    assert (NStep (NBin NMinus (S n) 1) (S n - 1)) by
      (apply n_step_bin; auto using n_step_num).
    remember (S n - 1) as nx.
    assert (r1: nx = n) by lia.
    remember (NBin NMinus (S n) 1) as e.
    rewrite r1 in H.
    assumption.
  Qed.

  Lemma tr_i_pair_in_1:
    forall P,
    CanRun P ->
    WLang.Distinct P ->
    ~ WVar TID P -> 
    forall p,
    PPairIn p (tr P) ->
    WLang.IPairIn p P.
  Proof.
    intros P H.
    induction H; intros Hd H_tid p Hp; simpl in Hp; try (destruct Hp as [Hp|Hp]).
    - invc Hp.
      constructor.
      assumption.
    - apply c_pair_in_skip in Hp.
      contradiction.
    - admit.
    - simpl in *.
      destruct r as (e1, e2).
      destruct (tr P) as (P_x, c_x) eqn:Ht.
      rename_hyp (RHasNext _) as Hr.
      destruct Hr as (n, Hr).
      assert (NStep e1 n) by eauto using r_first_to_eq.
      assert (Hx: RPick (e1,e2) n) by eauto using r_first_to_pick.
      rename_hyp (forall n, RPick (e1, e2) n -> _) as IH.
      simpl in *.
      intuition. {
        rename_hyp (IPairIn _ _) as Hp.
        invc Hp; rename_hyp (IPairIn _ _) as Hp. {
          apply i_pair_in_inv_n_seq in Hp.
          destruct Hp as [Hp|[Hp|Hp]].
          - (* p \in c1 *)
            constructor; auto.
          - (* p \in Px [e1] *)
            eapply i_pair_in_tr_for_1; eauto.
            intros.
            eapply IH; auto using WLang.distinct_subst.
            intros N.
            apply wvar_inv_subst in N.
            intuition.
          - (* a1 \in c1 /\ a2 \in P[e1] *)
            eapply WLang.i_pair_in_for_first_2; eauto.
            destruct p as (a1, a2).
            simpl in *.
            intuition;
             eauto using i_first_tr_1.
        }
        rename n0 into m.
        repeat rewrite subst_n_seq in Hp.
        apply i_pair_in_inv_n_seq in Hp.
        destruct Hp as [Hp|[Hp|Hp]].
        + (* p \in cx [m - 1] *)
          eapply i_pair_in_tr_for_2 with (e:=m - 1) (n:=m - 1); eauto using n_step_num.
          * intros.
            apply IH; auto using WLang.distinct_subst.
            intros N.
            apply WLang.wvar_inv_subst in N.
            intuition.
          * auto using r_pick_impl_2.
          * rewrite i_subst_subst_eq_1 in Hp.
            simpl in Hp.
            remove_eq x x.
            eapply c_pair_in_subst with (e1:=NBin NMinus m 1); eauto using n_step_num.
            apply n_step_bin; auto using n_step_num.
        + apply i_pair_in_inv_n_seq in Hp.
          destruct Hp as [Hp|[Hp|Hp]].
          * (* p \in c2 [m - 1] *)
            rewrite i_subst_subst_eq_1 in Hp.
            simpl in Hp.
            remove_eq x x.
            eapply WLang.i_pair_in_for_2 with (n0:=m - 1); eauto using n_step_num. {
              auto using r_pick_impl_2.
            }
            apply c_pair_in_subst with (e1:=(NBin NMinus m 1)) (n:=m - 1);
              auto using n_step_num.
            simpl.
            apply n_step_bin; auto using n_step_num.
          * (* p \in Px [m] *)
            clear Hx.
            eapply i_pair_in_tr_for_1 with (e:=NNum m);
              eauto using n_step_num, r_pick_impl_1.
            intros.
            apply IH; auto using WLang.distinct_subst.
            intros N.
            apply wvar_inv_subst in N.
            intuition.
          * destruct p as (a1, a2).
            simpl in *.
            rename_hyp (RPick _ m) as Hi.
            assert (Hp_n1 := Hi).
            apply r_pick_impl_3 in Hi.
            destruct Hi as (n1, (?, Hi)).
            subst.
            apply i_pair_in_for_mid_1 with
              (n0:=n1) (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
              auto using n_step_num, n_step_succ_minus_one
            .
            destruct Hp as [(Hp1, Hp2)|(Hp1, Hp2)];
              rewrite i_subst_subst_eq_1 in Hp1;
              simpl in Hp1;
              remove_eq x x.
            {
              (* a1 \in c2[m - 1] /\ a2 \in IFirst (P_x [m]) *)
              simpl.
              left.
              split; auto.
              (* a2 \in IFirst (P_x [m]) *)
              eapply i_first_tr_1 with (n:=S n1);
                eauto using n_step_num, r_pick_impl_1.
            }
            (* a2 \in c2[m - 1] /\ a1 \in IFirst (P_x [ m] ) *)
            simpl.
            right; split; auto.
            eapply i_first_tr_1 with (n:=S n1);
              eauto using n_step_num, r_pick_impl_1.
        + destruct p as (a1, a2).
          simpl in *.
          rename_hyp (RPick _ m) as Hi.
          assert (Hp_n1 := Hi).
          apply r_pick_impl_3 in Hi.
          destruct Hi as (n1, (?, Hi)).
          subst.
          destruct Hp as [(Hp1, Hp2)|(Hp1, Hp2)];
            rewrite i_subst_subst_eq_1 in Hp1;
            simpl in Hp1;
            remove_eq x x
          . {
            apply i_first_inv_n_seq in Hp2.
            destruct Hp2 as [Hp2|Hp2]. {
              (* a1 \in cx[m - 1] /\ a2 \in c2[m - 1] *)
              rewrite i_subst_subst_eq_1 in Hp2; simpl in Hp2; remove_eq x x.
              apply WLang.i_pair_in_for_3
                with (n0:=S n1) (e:=(NBin NMinus (S n1) 1));
                auto using r_pick_impl_1.
              simpl.
              left.
              split; auto.
              eapply i_last_tr_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            (* a1 \in cx[m - 1] /\ a2 \in P[m] *)
            eapply WLang.i_pair_in_for_mid_2 with
              (n0:=n1)
              (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
              eauto using n_step_num, n_step_succ_minus_one.
            simpl.
            left.
            split. {
              eapply i_last_tr_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            eapply i_first_tr_1 with (n:=S n1);
              eauto using n_step_num, r_pick_impl_1.
          }
          apply i_first_inv_n_seq in Hp2.
          destruct Hp2 as [Hp2|Hp2]. {
            rewrite i_subst_subst_eq_1 in Hp2; simpl in Hp2; remove_eq x x.
            apply WLang.i_pair_in_for_3
              with (n0:=S n1) (e:=(NBin NMinus (S n1) 1));
              auto using r_pick_impl_1.
            simpl.
            right.
            split; auto.
            (* a2 \in cx [m] *)
            eapply i_last_tr_1 with (n:=n1) (r:=(e1, e2) );
              eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
          }
          (* a2 \in cx[m - 1] /\ a2 \in P[m] *)
            eapply WLang.i_pair_in_for_mid_2 with
              (n0:=n1)
              (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
              eauto using n_step_num, n_step_succ_minus_one.
            simpl.
            right.
            split. {
              eapply i_last_tr_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            eapply i_first_tr_1 with (n:=S n1);
              eauto using n_step_num, r_pick_impl_1.
     }
     (* p \in cx [ e2 - 1] \/ p \in c2[ e2 - 1] *)
     rename_hyp (CPairIn _ _) as Hi.
     apply c_pair_inv_c_seq in Hi.
     destruct p as (a1, a2).
     destruct Hi as (Ha, Hb).
     unfold Conc.OneOf in *.
     edestruct r_pick_impl_4 as (n2,(Hpick, Hn2)); eauto.
     intuition.
     + (* cx /\ cx *) 
       eapply i_pair_in_tr_for_2 with
        (e:=NBin NMinus e2 (NNum 1)) (n:=n2);
        eauto using n_step_num, c_pair_in_def.
       intros.
       apply IH; auto using WLang.distinct_subst.
       intros N.
       apply wvar_inv_subst in N.
       intuition.
     + (* cx /\ c2 *)
       apply WLang.i_pair_in_for_3
         with (n0:=n2) (e:=(NBin NMinus e2 (NNum 1)));
         auto using r_pick_impl_1.
       simpl.
       eauto using i_last_tr_1.
     + (* c2 /\ cx *)
       apply WLang.i_pair_in_for_3
         with (n0:=n2) (e:=(NBin NMinus e2 (NNum 1)));
         auto using r_pick_impl_1.
       simpl.
       eauto using i_last_tr_1.
     + (* c2 /\ c2 *)
       apply WLang.i_pair_in_for_2 with
        (e:=NBin NMinus e2 (NNum 1)) (n0:=n2);
        auto using c_pair_in_def.
  Admitted.

  Import VHist.
  Open Scope vhist_scope.

  Inductive r_inst :=
  | RSync: Conc.inst -> r_inst
  | RSeq: r_inst -> r_inst -> r_inst
  | RFor: var -> range -> r_inst -> r_inst.

  Fixpoint n_to_r (n:n_inst) : r_inst :=
    match n with
    | NSync c => RSync c
    | NSeq P Q => RSeq (n_to_r P) (n_to_r Q)
    | NFor P x r Q => RSeq (n_to_r P) (RFor x r (n_to_r Q))
    end.

  Fixpoint r_subst x v i :=
    match i with
    | RSync c => RSync (Conc.i_subst x v c)
    | RSeq P Q => RSeq (r_subst x v P) (r_subst x v Q)
    | RFor y r P =>
      let P' := if VAR.eq_dec x y
        then P
        else r_subst x v P
      in
      RFor y (RExp.r_subst x v r) P'
    end.

  Notation history := (list access_val).

  Inductive Run: r_inst -> list (list access_val) -> Prop :=
  | run_sync:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (RSync c) [h]
  | run_seq:
    forall P Q mh_P mh_Q mh,
    Run P mh_P ->
    Run Q mh_Q ->
    mh_P ++ mh_Q = mh ->
    Run (RSeq P Q) mh
  | run_for_step:
    forall r r' n m1 m2 m3 x P,
    RStep r n r' ->
    Run (r_subst x (NNum n) P) m1 ->
    Run (RFor x r' P) m2 ->
    m1 ++ m2 = m3 ->
    Run (RFor x r P) m3
  | run_for_empty:
    forall r x P,
    REmpty r ->
    Run (RFor x r P) [].

  Inductive PRun: p_inst -> list history -> Prop :=
  | p_run_def:
    forall h1 h2 m P c,
    Run (n_to_r P) h1 ->
    CRun c h2 ->
    m = h1 ++ [h2] ->
    PRun (P, c) m.

  Lemma i_subst_c_seq:
    forall c1 c2 x v,
    i_subst x v (Conc.c_seq c1 c2) = Conc.c_seq (Conc.i_subst x v c1) (Conc.i_subst x v c2).
  Proof.
  Admitted.

  Lemma eq_run_def:
    forall P Q h1 h2,
    Run P h1 ->
    h1 = h2 ->
    P = Q ->
    Run Q h2.
  Proof.
    intros.
    subst.
    assumption.
  Qed.


  Lemma eq_r_seq_def:
    forall P P' Q Q',
    P = P' ->
    Q = Q' ->
    RSeq P Q = RSeq P' Q'.
  Proof.
    intros.
    subst.
    reflexivity.
  Qed.

  Lemma eq_n_to_r_def:
    forall x x',
    x = x' ->
    n_to_r x = n_to_r x'.
  Proof.
    intros.
    subst.
    reflexivity.
  Qed.

  Lemma c_run_inv_c_seq:
    forall c1 c2 h,
    CRun (Conc.c_seq c1 c2) h ->
    exists h1 h2,
    CRun c1 h1 /\ CRun c2 h2 /\ h = h1 ++ h2.
  Proof.
  Admitted.

  Lemma run_inv_n_seq:
    forall c P m,
    Run (n_to_r (n_seq c P)) m ->
    exists h1 h2 m', CRun c h1 /\ Run (n_to_r P) (h2 :: m') /\ m = (h1 ++ h2) :: m'.   
  Proof.
  Admitted.

  Lemma v_prefix_prefix:
    forall h1 h2 m,
    v_prefix h1 (v_prefix h2 m) = v_prefix (h1 ++ h2) m.
  Proof.
    destruct m; intros; simpl; auto.
    - rewrite app_assoc.
      reflexivity.
    - rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma v_prefix_seq:
    forall h m1 m2,
    v_prefix h (v_seq m1 m2) =
    v_seq (v_prefix h m1) m2.
  Proof.
    induction m1; simpl; intros.
    - rewrite v_prefix_prefix.
      auto.
    - reflexivity.
  Qed.

  Theorem sound:
    forall P m,
    WRun P m ->
    forall m',
    PRun (tr P) m' ->
    VHist.vhist_to_list m = m'.
  Proof.
    intros P m H; induction H; simpl; intros m' Hr2.
    - invc Hr2; simpl in *.
      rename_hyp (Run (RSync _) _) as Hr.
      invc Hr.
      admit.
    - admit.
    - destruct r as (e1, e2).
      destruct (tr P) as (Px, cx) eqn:Ht.
      simpl in *.
      invc Hr2.
      simpl in *.
      rename_hyp (Run _ _) as Hr.
      invc Hr.
      simpl in *.
      rewrite Ht in *.
      rename_hyp (RStep _ _ _) as Hs.
      invc Hs.
      simpl in *.
      rename_hyp (CRun (Conc.c_seq _ _) _) as Hr.
      apply c_run_inv_c_seq in Hr.
      destruct Hr as (h_cx, (h_c2, (Hr_cx, (Hr_c2, ?)))).
      subst.
      rename_hyp (Run (n_to_r _) _) as Hr.
      apply run_inv_n_seq in Hr.
      destruct Hr as (h_c1, (h_Px, (m_c1_Px, (Hr_c1, (Hr_Px, Ha))))).
      subst.
      remember (h_Px :: m_c1_Px) as h_px.
      (*
      assert (PRun (tr (w_subst x n P)) (h_px ++ [h_cx])). {
        clear H7 H12 H5 H9.
        clear Heqh_px Hr_c1.
      }
      invc Hr2. {
        assert (IHWRun2 := IHWRun2 ([h_cx ++ h_c2])).
        admit.
        (*
        rename_hyp (Run (n_seq _ _) _) as H_c1.
        apply run_inv_n_seq in H_c1. 2: { admit. }
        destruct H_c1 as (c1_h1, (c1_h2, (H_c1, (H_c2, eq1)))).
        *)
      }
      rewrite subst_n_seq in *.
      *)
      admit.
    - destruct r as (e1, e2).
      destruct (tr P) as (Px, cx) eqn:Ht.
      simpl in *.
      invc Hr2.
      rename_hyp (Run _ _) as Hr1.
      invc Hr1.
      rename_hyp (Run (n_to_r (n_seq _ _)) _) as Hr1.
      apply run_inv_n_seq in Hr1.
      destruct Hr1 as (h_c1, (h_P_e1, (m, (H_c1, (H_P_e2, ?))))).
      subst.
      assert (mh_Q = []) by admit.
      subst.
      rename_hyp (Run (RFor _ _ _) _) as Hr2.
      clear Hr2.
      rewrite <- app_nil_end in *.
      rename_hyp (CRun (Conc.c_seq _ _) _) as Hc.
      apply c_run_inv_c_seq in Hc.
      destruct Hc as (h_cx_e1, (h_c2_e1, (H_cx_e1, (H_c2_e1, ?)))).
      subst.
      assert (Hp:  PRun (tr (w_subst x n P)) ((h_P_e1 :: m) ++ [h_cx_e1]) ). {
        destruct (tr (w_subst _ _ _)) as (Px', cx') eqn:Ht'.
        rewrite <- tr_subst in Ht'.
        2: { admit. }
        2: { admit. }
        rewrite Ht in *.
        simpl in Ht'.
        invc Ht'.
        eapply p_run_def; eauto.
        - admit.
        - admit.
      }
      rename h1 into h_c1'.
      rename m1 into m_P_e1'.
      rename h2 into m_c2_e1'.
      rename h_P_e1 into h_Px_e1.
      rename m into m_Px_e1.
      remember ((h_Px_e1 :: m_Px_e1) ++ [h_cx_e1]) as h_Px_e1'.
      rewrite v_prefix_seq.
      assert (IHWRun := IHWRun _ Hp); clear Hp.
      subst.
      
  Admitted.

End Props.
