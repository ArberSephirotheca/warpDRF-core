Require Import AccExp.
Require Import Tasks.
Require Import Conc.
Require Import NExp.
Require Import RExp.
Require Import Var.
Require Import WLang.
Require Import Tictac.
Require Import Util.
Import NExpNotations.
Import RExpNotations.
Import CLangNotations.
Open Scope exp_scope.
Open Scope lang_scope.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.
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

  Definition PFirst a (P:p_inst) :=
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

  Lemma p_first_inv_p_seq:
    forall a P Q,
    PFirst a (p_seq P Q) ->
    PFirst a P.
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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
  Admitted.


  Lemma p_pair_in_inv_p_seq:
    forall a P Q,
    PPairIn a (p_seq P Q) ->
    PPairIn a P \/ PPairIn a Q \/ POneOf a P Q.
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

  Lemma subst_n_seq:
    forall x v c P,
    subst x v (n_seq c P) =
      n_seq (Conc.i_subst x v c) (subst x v P).
  Proof.
  Admitted.

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
(*
  Lemma n_subst_not_in_rw
     : forall (x : var) P,
       ~ PFree x P -> forall v : nexp, subst x v P = P.
  Proof.
  Admitted.
*)
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

  Lemma i_pair_in_n_seq_l:
    forall p c,
    CPairIn p c ->
    forall P,
    IPairIn p (n_seq c P).
  Proof.
  Admitted.

  Lemma i_pair_in_n_seq_r:
    forall p P,
    IPairIn p P ->
    forall c,
    IPairIn p (n_seq c P).
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

  Lemma subst_subst_neq_3
     : forall P (x y : var) (v1 v2 : nexp),
       x <> y ->
       ~ NFree v1 y ->
       ~ NFree v2 x ->
       subst x v1 (subst y v2 P) = subst y v2 (subst x v1 P).
  Proof.
  Admitted.
(*
  Lemma n_subst_subst_neq_5:
    forall e3 e1 e2 x y,
    NClosed e1 ->
    y <> x ->
    n_subst y e1 (n_subst x e2 e3) =
    n_subst x (n_subst y e1 e2) (n_subst y e1 e3).
  Proof.
    induction e3; simpl; intros.
    - reflexivity.
    - rename v into z.
      remove_eq x z. {
        (* x = z *)
        remove_eq y z. {
          rewrite n_subst_not_free with (x:=x); auto.
          admit.
          (* n_subst y e1 e2 = e1 *)
        }
        remove_eq x z. {
          reflexivity.
        }
        (* n_subst y e1 e2 = NVar z *)
        admit.
      }
      remove_eq y z. {
        rewrite n_subst_not_free with (x:=x); auto.
      }
      remove_eq x z. {
        (* NVar z = n_subst y e1 e2 *)
        admit.
      }
      reflexivity.
  Qed.
*)
(*
  Lemma subst_subst_neq_5:
    forall P x y e1 e2,
    NClosed e1 ->
    NClosed e2 ->
    subst y e1 (subst x e2 P) = subst x (n_subst y e1 e2) (subst y e1 P).
  Proof.
    induction P; intros.
    - admit.
    - admit.
    - simpl.
      rename v into z.
      remove_eq y z. {
        remove_eq x z. {
          rewrite IHP1; auto.
          apply eq_n_for_def; auto.
          admit.
        }
        apply eq_n_for_def; auto.
      }
  Qed.
*)
(*
  Lemma subst_subst_neq_4:
    forall P x y e1 e2,
    NClosed e1 ->
    x <> y ->
    subst y e1 (subst x e2 P) =
    subst x (n_subst y e1 e2) (subst y e1 P).
  Proof.
    induction P; intros.
    - simpl.
      admit.
    - simpl.
      rewrite IHP1; auto.
      rewrite IHP2; auto.
    - rename v into z.
      simpl.
      apply eq_n_for_def; auto. {
        admit.
      }
      remove_eq y z. {
        remove_eq x z. {
          reflexivity.
        }
        (* y = z /\ x <> z *)
      }
      rewrite r_subst_subst_neq_4; auto.
      remove_eq x z. {
        subst.
        destruct (Set_VAR.MF.eq_dec y z). {
          subst.
          contradiction.
        }
        auto.
      }
      destruct (Set_VAR.MF.eq_dec y z). {
        subst.
        rewrite IHP1; auto.
        assert (r1: n_subst z e1 e2 = e2). {
          rewrite n_subst_not_free; auto using n_closed_to_not_free.
        }
        rewrite r1.
        reflexivity.
      }
      rewrite IHP1; auto.
  Qed.*)

  Definition WClosed P :=
    forall x,
    ~ WFree P x.

  Lemma w_closed_inv_seq:
    forall P1 P2,
    WClosed (WSeq P1 P2) ->
    WClosed P1 /\ WClosed P2.
  Proof.
    unfold WClosed.
    intros.
    split;
      simpl in *;
      intros;
      assert (H:= H x);
      intuition.
  Qed.

  Lemma w_free_dec:
    forall P x,
    WFree P x \/ ~ WFree P x.
  Proof.
    induction P; intros.
  Admitted.

  Lemma i_pair_in_subst_tr:
    forall P e x,
    WClosed (w_subst x e P) ->
    (*forall y, y <> x -> ~ WFree P y -> *)
    NClosed e ->
    (* [[ P ]] [x := e ] = [[ P[x := e] ]] *)
    p_subst x e (tr P) = tr (w_subst x e P).
  Proof.
    induction P; intros e' y Hw Hc; simpl in *.
    - auto.
    - apply w_closed_inv_seq in Hw.
      destruct Hw as (Hw1, Hw2).
      destruct (tr P1) as (P1_x, c1_x) eqn:Ht1.
      destruct (tr P2) as (P2_x, c2_x) eqn:Ht2.
      simpl.
      rewrite <- IHP1; auto; clear IHP1.
        (*2: { intros z Hn N. apply Hw in Hn. intuition. }*)
      rewrite <- IHP2; auto; clear IHP2.
        (*2: { intros z Hn N. apply Hw in Hn. intuition. } *)
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
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        simpl.
        rewrite Ht.
        simpl.
        remove_eq x x.
        rewrite subst_n_seq.
        simpl.
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
      remove_eq y x.
      simpl.
      destruct (tr (w_subst y e' P)) as (P_t, c_t) eqn:Ht'.
      repeat rewrite subst_n_seq.
      repeat rewrite c_seq_subst.
      apply eq_pair_def. {
        apply eq_n_for_def; auto. {
          apply eq_n_seq_def; auto.
          rewrite <- IHP in Ht'; auto. 2: { admit. }
          simpl in Ht'.
          invc Ht'.
          rewrite subst_subst_neq_3 with (x:=x) (y:=y); auto.
          - (* Show that e1 is closed, which requires P runnable *)
            admit.
          - intros N.
            apply n_free_inv_subst_eq in N.
            apply n_closed_to_not_free in N; auto.
        }
        apply eq_n_seq_def. {
          rewrite <- IHP in Ht'; auto.
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
        simpl in Ht'.
        invc Ht'.
        reflexivity.
      }
      rewrite <- IHP in Ht'; auto.
      simpl in Ht'.
      invc Ht'.
      apply eq_c_seq_def. {
        rewrite c_subst_subst_neq_5; auto.
      }
      rewrite c_subst_subst_neq_5; auto.
  Admitted.


  Lemma tr_i_pair_in_1:
    forall P,
    WLang.CanRun P ->
    forall p,
    PPairIn p (tr P) ->
    WLang.IPairIn p P.
  Proof.
    intros P H.
    induction H; intros p Hp; simpl in Hp; try (destruct Hp as [Hp|Hp]).
    - admit.
    - admit.
    - admit.
    - destruct r as (e1, e2).
      destruct (tr P) as (P_x, c_x) eqn:Ht.
      rename_hyp (RHasNext _) as Hr.
      destruct Hr as (n, Hr).
      assert (NStep e1 n) by eauto using r_first_to_eq.
      assert (Hx: RPick (e1,e2) n) by eauto using r_first_to_pick.
      rename_hyp (forall n, _) as IH.
      simpl in *.
      destruct Hp as [Hp|Hp]. {
        invc Hp; rename_hyp (IPairIn _ _) as Hp. {
          apply i_pair_in_inv_n_seq in Hp.
          destruct Hp as [Hp|[Hp|Hp]].
          - constructor; auto.
          - eapply WLang.i_pair_in_for_1 with (e:=NNum n); eauto using n_step_num.
            apply IH; auto.
            assert (IPairIn p (subst x (NNum n) P_x)). {
              eauto using i_pair_in_subst, n_step_num.
            }
            (*rewrite i_pair_in_subst_tr in Hy; auto using n_closed_num.*)
            admit.
          - admit.
        }
        rename n0 into m.
  Admitted.

End Props.
