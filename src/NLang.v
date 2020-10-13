Require Import AccExp.
Require Import Tasks.
Require Import Conc.
Require Import NExp.
Require Import RExp.
Require Import Var.
Require Import WLang.
Require Import Tictac.
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

  Definition p_seq (i:p_inst) (j:p_inst) :=
   match i, j with
    | (i,ci), (j, cj) => (NSeq i (n_seq ci j), cj)
    end.

  Reserved Notation "P |> Q" (at level 80).

  Inductive Translate : w_inst -> p_inst -> Prop :=
  | translate_sync:
    forall c,
    WSync c |> (NSync c, Conc.Skip)

  | translate_seq:
    forall P P' Q Q' c1 c2,
    P |> (P', c1) ->
    Q |> (Q', c2) ->
    WSeq P Q |> (NSeq P' (n_seq c1 Q'), c2)
 
  | translate_for:
    forall x e1 e2 P c2 c1 P_e1 c_e1 P_dec_e2 P_dec_x c_dec_x c_dec_e2 P_x c_x, 
    w_subst x e1 P |> (P_e1, c_e1) ->
    w_subst x (NBin NMinus (NVar x) (NNum 1)) P |> (P_dec_x , c_dec_x) ->
    P |> (P_x, c_x) ->
    w_subst x (NBin NMinus e2 (NNum 1)) P |> (P_dec_e2, c_dec_e2) ->
    let c2_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c2 in
    let c2_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    WFor c1 x (e1, e2) P c2 |> (NFor
        (n_seq c1 P_e1) x
        (NBin NPlus (NNum 1) e1, e2)
        (n_seq c_dec_x (n_seq c2_dec_x P_x)), c_seq c_dec_e2 c2_dec_e2)
    
  where " P |> Q" := (Translate P Q).


  Reserved Notation "P >> Q" (at level 80).

  Inductive Translate2 : w_inst -> p_inst -> Prop :=
  | translate2_sync:
    forall c,
    WSync c >> (NSync c, Conc.Skip)

  | translate2_seq:
    forall P P' Q Q' c1 c2,
    P >> (P', c1) ->
    Q >> (Q', c2) ->
    WSeq P Q >> (NSeq P' (n_seq c1 Q'), c2)
 
  | translate2_for:
    forall x e1 e2 P c2 c1 P_x c_x, 
    P >> (P_x, c_x) ->
    let P_e1 := subst x e1 P_x in
    let c_e1 := Conc.i_subst x e1 c_x in
    let c_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c_x in
    let c2_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c2 in
    let c_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c_x in
    let c2_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    WFor c1 x (e1, e2) P c2 >> (NFor
        (n_seq c1 P_e1) x
        (NBin NPlus (NNum 1) e1, e2)
        (n_seq c_dec_x (n_seq c2_dec_x P_x)), c_seq c_dec_e2 c2_dec_e2)
    
  where " P >> Q" := (Translate2 P Q).


  Lemma translate_seq_eq:
    forall P P' Q Q' R,
    P |> P' ->
    Q |> Q' ->
    R = p_seq P' Q' ->
    (* --------- *)
    WSeq P Q |> R.
  Proof.
    intros.
    subst.
    unfold p_seq.
    destruct P' as (P', c1).
    destruct Q' as (Q', c2).
    constructor; auto.
  Qed.
(*
  Lemma translate_for_eq:
    forall c1 x e1 e2 P c2,
    forall P_e1 c_e1, 
    w_subst x e1 P |> (P_e1, c_e1) ->
    forall P_dec_x c_dec_x,
    w_subst x (NBin NMinus (NVar x) (NNum 1)) P |> (P_dec_x , c_dec_x) ->
    forall P_x c_x,
    P |> (P_x, c_x) ->
    forall P_dec_e2 c_dec_e2,
    w_subst x (NBin NMinus e2 (NNum 1)) P |> (P_dec_e2, c_dec_e2) ->
    forall P' c',
    let c2_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c2 in
    let c2_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    P' =
      NFor
        (n_seq c1 P_e1) x (e1, e2)
        (n_seq c_dec_x (n_seq c2_dec_x P_x)) ->
    c' = c_seq c_dec_e2 c2_dec_e2 ->
    WFor c1 x (NBin NPlus (NNum 1) e1, e2) P c2 |> (P', c').
  Proof.
    intros.
    subst.
    econstructor; eauto.
  Qed.*)

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

  Inductive CanRun: n_inst -> Prop :=
  | can_run_sync:
    forall c,
    CanRun (NSync c)
  | can_run_seq:
    forall i j,
    CanRun i -> 
    CanRun j ->
    CanRun (NSeq i j)
  | can_run_for:
    forall x r P Q,
    CanRun P ->
    RDefined r ->
    (forall n, RPick r n -> CanRun (subst x (NNum n) Q)) -> 
    CanRun (NFor P x r Q).

  Lemma tr_can_run:
    forall P,
    WLang.CanRun P ->
    forall Q c,
    P |> (Q, c) ->
    CanRun Q.
  Proof.
    intros P.
    induction P.
    - intros H0 Q c H1.
      inversion H1; subst; clear H1.
      apply can_run_sync.
    - intros HW Q c Hs.
      inversion HW; subst; clear HW.
      eapply IHP1 in H1; eauto.
      + eauto.
      admit.
      (*
      + inversion Hs; subst; clear Hs.
        assumption.
      + assumption.
      + 
      *)
    - admit.
    (*
    intros P H.
    induction H; intros; inversion H; subst; clear H.
    - apply can_run_sync.
    - inversion H1; subst; clear H1.
      assert (IHCanRun1 := IHCanRun1 P' c1 H4).
      assert (IHCanRun2 := IHCanRun2 Q' c H6).
      apply can_run_seq.
      + assumption.
      + (* CanRun (n_seq c1 Q') *)Search n_seq.
      *)
    (* TODO: PROVE ME PLEASE *)
  Admitted.

  Lemma can_run_inv_n_seq_r:
    forall c P,
    CanRun (n_seq c P) ->
    CanRun P.
  Proof.
    induction P; simpl; intros.
    - inversion H; subst; clear H.
      constructor.
    - inversion H; subst; clear H.
      auto using can_run_seq.
    - inversion H; subst; clear H.
      eauto using can_run_for.
  Qed.

  Lemma translate_to_i_last:
    forall a P,
    WLang.ILast a P ->
    forall Q,
    P |> Q ->
    PLast a Q.
  Proof.
    intros a P H.
    unfold PLast.
    induction H; intros (Q, c) Ht; inversion Ht; subst; clear Ht.
    - rename_hyp (_ |> (_, c)) as Hc.
      apply IHILast in Hc; auto.
    - assert (Hn: NStep (NBin NMinus e2 (NNum 1)) n) by eauto using r_last_to_eq.
      rename_hyp (_ |> (P_dec_e2, c_dec_e2)) as H_e2.
      rename_hyp (forall e, NStep e _ -> forall Q, _ |> _ -> _) as Hi.
      eapply Hi in H_e2; eauto.
      auto using c_in_c_seq_l.
    - assert (Hn: NStep (NBin NMinus e2 (NNum 1)) n) by eauto using r_last_to_eq.
      apply c_in_c_seq_r.
      unfold c2_dec_e2.
      eauto.
  Qed.

  Lemma tr_not_var:
    forall P c Q,
    P |> (Q, c) ->
    ~ WVar TID P ->
    ~ Var TID Q.
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

  Lemma i_last_to_translate:
    forall P Q,
    P |> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    forall a,
    PLast a Q ->
    WLang.ILast a P.
  Proof.
    intros P Q H.
    induction H; intros.
    - invc_hyp (PLast _ _).
      invc_hyp (IIn _ Skip).
    - simpl in *.
      invc_hyp (WLang.CanRun _).
      assert (CanRun Q') by eauto using can_run_inv_n_seq_r, tr_can_run.
      assert (~ WVar TID Q) by (simpl in *; intuition).
      auto using WLang.i_last_seq.
    - simpl in *.
      subst.
      rename_hyp (CIn a _) as Hi.
      apply c_in_inv_c_seq in Hi.
      invc_hyp (WLang.CanRun _).
      assert (Hx: exists m, RLast (e1, e2) m). {
        auto using r_has_next_to_last.
      }
      destruct Hx as (m, Hl).
      destruct Hi as [Hi|Hi]. {
        (* In c from P |> (Q, c) *)
        assert (Hw: WLang.ILast a (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
          apply IHTranslate4; auto.
          assert (WLang.CanRun (w_subst x (NNum m) P)) by eauto using r_last_to_pick.
          eapply can_run_subst; eauto using n_step_num, r_last_to_eq.
          assert (~ WVar TID P) by intuition.
          eapply wvar_subst_not_in; eauto using r_last_to_eq.
        }
        apply i_last_for_1 with (n:=m); eauto.
        intros.
        assert (NStep (NBin NMinus e2 (NNum 1)) m) by eauto using r_last_to_eq.
        eapply i_last_w_subst; eauto.
      }
      (* In c2 *)
      apply i_last_for_2 with (n:=m); auto.
      intros e He.
      unfold c2_dec_e2 in *.
      apply c_in_subst with (v:=(NBin NMinus e2 (NNum 1))) (n:=m); eauto using r_last_to_eq.
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

  Lemma i_first_1:
    forall P Q,
    P |> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    forall a,
    PFirst a Q ->
    WLang.IFirst a P.
  Proof.
    intros P Q H.
    induction H; intros Hc Hv a Hi; simpl in Hi; try invc Hi; try invc Hc; simpl in *.
    - constructor; auto.
    - constructor; auto.
    - rename_hyp (IFirst _ _) as Hi.
      apply i_first_inv_n_seq in Hi.
      destruct Hi as [Hi|Hi]. {
        auto using WLang.i_first_for_1.
      }
      rename_hyp (RHasNext _) as Hh. 
      destruct Hh as (n, Hf).
      assert (NStep e1 n) by eauto using r_first_to_eq.
      eapply WLang.i_first_for_2; eauto.
      assert (Hp: PFirst a (P_e1, c_e1)). {
        simpl; auto.
      }
      assert (WLang.CanRun (w_subst x e1 P)). {
        assert (WLang.CanRun (w_subst x (NNum n) P)) by eauto using r_first_to_pick.
        eapply WLang.can_run_subst with (e:=NNum n); eauto using n_step_num.
      }
      apply IHTranslate1 in Hp; auto. {
        eapply WLang.i_first_w_subst with (e3:=e1); eauto using n_step_num.
      }
      eapply wvar_subst_not_in; eauto.
      intuition.
  Qed.

  Lemma p_pair_in_inv_p_seq:
    forall a P Q,
    PPairIn a (p_seq P Q) ->
    PPairIn a P \/ PPairIn a Q \/ POneOf a P Q.
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

  Lemma p_one_of_to_one_of:
    forall P P',
    P |> P' ->
    forall Q Q',
    Q |> Q' ->
    forall a,
    POneOf a P' Q' ->
    OneOf a (inr P) (inr Q).
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

  Lemma p_pair_in_seq:
    forall P P' Q Q' a,
    P |> P' ->
    Q |> Q' ->
    PPairIn a (p_seq P' Q') ->
    (PPairIn a P' -> WLang.IPairIn a P) ->
    (PPairIn a Q' -> WLang.IPairIn a Q) ->
    WLang.IPairIn a (WSeq P Q).
  Proof.
    intros.
    rename_hyp (PPairIn _ (p_seq _ _)) as Hi.
    apply p_pair_in_inv_p_seq in Hi.
    destruct Hi as [Hi|[Hi|Hi]].
    - apply WLang.i_pair_in_seq_l; auto.
    - apply WLang.i_pair_in_seq_r; auto.
    - eapply p_one_of_to_one_of in Hi; eauto using WLang.i_pair_in_seq_both.
  Qed.

  Lemma p_par_in_for_last:
    forall e1 e2 x c1 c2 P m a P_dec_e2 c_dec_e2,
    let c2_dec_e2 := i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    w_subst x (NBin NMinus e2 (NNum 1)) P |> (P_dec_e2, c_dec_e2) ->
    CPairIn a (c_seq c_dec_e2 (i_subst x (NBin NMinus e2 (NNum 1)) c2)) ->
    ~ WVar TID P ->
    RLast (e1, e2) m ->
    WLang.CanRun (w_subst x (NBin NMinus e2 (NNum 1)) P) ->
    (CPairIn a c_dec_e2 -> WLang.IPairIn a (w_subst x (NBin NMinus e2 (NNum 1)) P)) ->
    WLang.IPairIn a (WFor c1 x (e1, e2) P c2).
  Proof.
    intros.
    assert (NStep (NBin NMinus e2 (NNum 1)) m) by eauto using r_last_to_eq.
    rename_hyp (CPairIn _ _) as Hi.
    inversion Hi; subst; clear Hi.
    rename_hyp (CIn a1 _) as Ha.
      rename_hyp (CIn a2 _) as Hb.
      apply c_in_inv_c_seq in Ha.
      apply c_in_inv_c_seq in Hb.
      assert (~ WVar TID (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
        simpl in *.
        eapply wvar_subst_not_in; eauto.
      }
      rename_hyp (_ |> _) as Ht.
      assert (RPick (e1, e2) m) by eauto using r_last_to_pick.
      destruct Ha as [Ha|Ha];
        destruct Hb as [Hb|Hb].
      + assert (CPairIn (a1, a2) c_dec_e2) by auto using c_pair_in_def.
        assert (WLang.IPairIn (a1, a2) (w_subst x (NBin NMinus e2 (NNum 1)) P)) by auto.
        (* We must show that r has at least one iteration, which
           allows us to learn that it has a last iteration.
           *)
        eapply WLang.i_pair_in_for_1; eauto.
      + assert (WLang.ILast a1 (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
          apply i_last_to_translate with (a:=a1) in Ht; auto; simpl.
        }
        eapply WLang.i_pair_in_for_3 with (e:=(NBin NMinus e2 (NNum 1))); eauto.
        simpl.
        intuition.
      + assert (WLang.ILast a2 (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
          apply i_last_to_translate with (a:=a2) in Ht; auto; simpl.
        }
        eapply WLang.i_pair_in_for_3 with (e:=(NBin NMinus e2 (NNum 1))); eauto.
        simpl.
        intuition.
      + assert (CPairIn (a1, a2) c2_dec_e2) by auto using c_pair_in_def.
        unfold c2_dec_e2 in *.
        (* We must show that r has at least one iteration, which
           allows us to learn that it has a last iteration.
           *)
        eapply WLang.i_pair_in_for_2; eauto.
  Qed.

  Lemma n_one_of_to_one_of:
    forall x e1 P P_e1 c_e1 m c1 a,
    w_subst x e1 P |> (P_e1, c_e1) ->
    NOneOf a c1 P_e1 ->
    NStep e1 m ->
    OneOf a (inl c1) (inr (w_subst x e1 P)).
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

  Lemma p_pair_in_for_first:
    forall x e1 P P_e1 c_e1 e2 m c2 c1 a,
    w_subst x e1 P |> (P_e1, c_e1) ->
    RFirst (e1, e2) m ->
    IPairIn a (n_seq c1 P_e1) ->
    (IPairIn a P_e1 -> WLang.IPairIn a (w_subst x e1 P)) ->
    WLang.IPairIn a (WFor c1 x (e1, e2) P c2).
  Proof.
    intros.
    assert (NStep e1 m) by eauto using r_first_to_eq.
    assert (RPick (e1, e2) m) by eauto using r_first_to_pick.
    rename_hyp (IPairIn a _) as Hi.
    apply i_pair_in_inv_n_seq in Hi.
    destruct Hi as [Hi|[Hi|Hi]].
    - constructor; auto.
    - eapply WLang.i_pair_in_for_1; eauto.
    - eapply WLang.i_pair_in_for_first_2; eauto.
      eauto using n_one_of_to_one_of.
  Qed.
(*
  Lemma tr_inv_sync:
    forall P c1 c2,
    P |> (NSync c1, c2) ->
    P = (WSync c1) /\ c2 = Skip.
  Proof.
    intros.
    invc H.
    - auto.
    - destruct P'; destruct Q'.
      rename_hyp (_ = _) as r1.
      invc r1.
    - rename_hyp (_ = _) as r1.
      invc r1.
  Qed.

  Lemma tr_inv_seq:
    forall P1 P2 P3 c,
    P1 |> (NSeq P2 P3, c) ->
    exists P' Q' P'' Q'', P1 = WSeq P' Q' /\ P' |> P'' /\ Q' |> Q'' /\ p_seq P'' Q'' = (NSeq P2 P3, c).
  Proof.
    intros.
    invc H.
    - exists P.
      exists Q.
      exists P'.
      exists Q'.
      intuition.
    - invc_hyp (_ = _).
  Qed.
*)
  Definition c_seq c (P:p_inst) :=
    let (Q, c2) := P in
    (n_seq c Q, c2).

  Lemma tr_seq:
    forall P Q,
    P |> Q ->
    forall c,
    WLang.w_seq c P |> c_seq c Q.
  Proof.
    (* TODO: PROVE ME PLEASE *)
  Admitted.

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

  Fixpoint WIn (x:var) P :=
    match P with
    | WSync c => Conc.In x c
    | WSeq P Q => WIn x P \/ WIn x Q
    | WFor c1 y r P c2 => Conc.In x c1 \/
      RIn x r \/ (x <> y /\ (WIn x P \/ Conc.In x c2))
    end.

  Lemma n_in_subst_to_n_in:
    forall x e n,
    NIn x (n_subst x e n) ->
    NIn x e.
  Proof.
    induction n; intros; simpl in *.
    - invc H.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assumption.
      }
      invc H.
      contradiction.
    - invc H; auto.
  Qed.

  Lemma b_in_subst_to_n_in:
    forall x e b,
    BExp.BIn x (BExp.b_subst x e b) ->
    NIn x e.
  Proof.
    induction b; simpl; intros.
    - invc H.
    - invc H;
      eauto using n_in_subst_to_n_in.
    - invc H; auto.
    - invc H; auto.
  Qed.

  Lemma r_in_subst_to_n_in:
    forall x r e,
    RIn x (r_subst x e r) ->
    NIn x e.
  Proof.
    intros.
    destruct r as (e1, e2).
    simpl in *.
    invc H;
      rename_hyp (NIn _ _) as Hi;
      apply n_in_subst_to_n_in in Hi; auto.
  Qed.

  Lemma i_in_subst_to_n_in:
    forall x e c,
    Conc.In x (i_subst x e c) ->
    NIn x e.
  Proof.
    induction c; simpl; intros.
    - contradiction.
    - destruct H as [H|[H|H]]; eauto using b_in_subst_to_n_in.
    - destruct H as [H|H]; eauto.
    - admit.
  Admitted.

  Lemma w_in_subst_to_n_in:
    forall x e P,
    WIn x (w_subst x e P) ->
    NIn x e.
  Proof.
    induction P; simpl; intros.
    - eauto using i_in_subst_to_n_in.
    - intuition.
    - destruct (Set_VAR.MF.eq_dec x v); subst; invc H;
      eauto using i_in_subst_to_n_in.
      + rename_hyp (_ \/ _) as Hx.
        destruct Hx as [Hx|(Hx,Hy)]; eauto using r_in_subst_to_n_in.
        contradiction.
      + rename_hyp (_ \/ _) as Hx.
        destruct Hx as [Hx|(Hx,[Hy|Hy])]; eauto using r_in_subst_to_n_in.
        eauto using i_in_subst_to_n_in.
  Qed.
(*
  Lemma w_subst_not_in_2:
    forall e n,
    NStep e n ->
    forall x P,
    ~ In x (w_subst x e P).
  Proof.
    induction P; intros; simpl.
    - eapply i_subst_not_in_2; eauto.
    - intuition.
    - rename v into y.
      intros N.
      destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        simpl in *.
        destruct N as [N|[N|N]].
        - eapply i_subst_not_in_2 in N; eauto.
        - eapply r_subst_not_in_2 in N; eauto.
        - destruct N; contradiction.
      }
      simpl in *.
      destruct N as [N|[N|(_,[N|N])]]; auto.
      + eapply i_subst_not_in_2 in N; eauto.
      + eapply r_subst_not_in_2 in N; eauto.
      + eapply i_subst_not_in_2 in N; eauto.
  Qed.*)

  Lemma i_subst_not_in_rw:
    forall x c,
    ~ Conc.In x c ->
    forall v,
    i_subst x v c = c.
  Proof.
    induction c; simpl; intros.
    - reflexivity.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
      assert (~ BExp.BIn x b) by intuition.
      rewrite BExp.b_subst_not_in_rw; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - admit.
    - rewrite IHc; auto.
      rewrite r_subst_not_in_rw; auto.
      destruct (Set_VAR.MF.eq_dec x v); subst; auto.
  Admitted.

  Lemma w_subst_not_in_rw:
    forall x P,
    ~ WIn x P ->
    forall v,
    w_subst x v P = P.
  Proof.
    induction P; simpl; intros.
    - rewrite i_subst_not_in_rw; auto.
    - assert (~ WIn x P1) by intuition.
      assert (~ WIn x P2) by intuition.
      rewrite IHP1; auto.
      rewrite IHP2; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        assert (~ Conc.In v i) by intuition.
        rewrite i_subst_not_in_rw; auto.
        rewrite r_subst_not_in_rw; auto.
      }
      rewrite i_subst_not_in_rw; auto.
      rewrite r_subst_not_in_rw; auto.
      assert (~  (WIn x P \/ Conc.In x i0) ) by intuition.
      rewrite i_subst_not_in_rw; auto.
      rewrite IHP; auto.
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

  Let eq_pair_def:
    forall A (x1 x2:A) B (y1 y2:B),
    x1 = x2 ->
    y1 = y2 ->
    (x1,y1)=(x2,y2).
  Proof.
    intros. subst.
    reflexivity.
  Qed.

  Let eq_c_seq_def:
    forall c1 c2 c1' c2',
    c1 = c1' ->
    c2 = c2' ->
    Conc.c_seq c1 c2 = Conc.c_seq c1' c2'.
  Proof.
    intros; subst.
    reflexivity.
  Qed.

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

  Fixpoint In (x : var) (P : n_inst) {struct P} : Prop :=
  match P with
  | NSync c => Conc.In x c
  | NSeq P Q => In x P \/ In x Q
  | NFor P y r Q =>
      In x P \/ RIn x r \/ (x <> y /\ In x Q)
  end.

  Lemma n_subst_not_in_rw
     : forall (x : var) P,
       ~ In x P -> forall v : nexp, subst x v P = P.
  Proof.
  Admitted.

  Lemma in_inv_subst_eq:
    forall x v P,
    In x (subst x v P) ->
    NIn x v.
  Proof.
    induction P; simpl; intros.
    - eauto using i_in_subst_to_n_in.
    - destruct H; auto.
    - destruct H as [H|[H|(?,H)]];
      eauto using r_in_subst_to_n_in.
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

  Lemma e_subst_subst_eq_1:
    forall e1 e2 x e3,
    n_subst x e1 (n_subst x e2 e3)
    =
    n_subst x (n_subst x e1 e2) e3.
  Proof.
    induction e3; intros; simpl in *.
    - reflexivity.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        reflexivity.
      }
      simpl.
      destruct (Set_VAR.MF.eq_dec x v). {
        contradiction.
      }
      reflexivity.
    - rewrite IHe3_1; auto.
      rewrite IHe3_2; auto.
  Qed.

  Lemma r_subst_subst_eq_1:
    forall e1 e2 x r,
    r_subst x e1 (r_subst x e2 r)
    =
    r_subst x (n_subst x e1 e2) r.
  Proof.
    intros.
    destruct r as (r1, r2).
    simpl.
    rewrite e_subst_subst_eq_1.
    rewrite e_subst_subst_eq_1.
    reflexivity.
  Qed.

  Lemma b_subst_subst_eq_1:
    forall e1 e2 x b,
    BExp.b_subst x e1 (BExp.b_subst x e2 b)
    =
    BExp.b_subst x (n_subst x e1 e2) b.
  Proof.
    induction b; intros; simpl.
    - reflexivity.
    - erewrite e_subst_subst_eq_1; eauto.
      erewrite e_subst_subst_eq_1; eauto.
    - rewrite IHb1; auto.
      rewrite IHb2; auto.
    - rewrite IHb; auto.
  Qed.

  Lemma i_subst_subst_eq_1:
    forall e1 e2 x c,
    i_subst x e1 (i_subst x e2 c) = i_subst x (n_subst x e1 e2) c.
  Proof.
    induction c; intros; simpl.
    - reflexivity.
    - erewrite b_subst_subst_eq_1; eauto.
      rewrite IHc1; auto.
      rewrite IHc2; auto.
    - rewrite IHc1; auto.
      rewrite IHc2; auto.
    - admit.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        admit.
      }
      rewrite IHc; auto.
      admit.
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
       ~ NIn y v1 ->
       ~ NIn x v2 ->
       subst x v1 (subst y v2 P) = subst y v2 (subst x v1 P).
  Proof.
  Admitted.


  Lemma i_pair_in_subst_tr:
    forall P e(* n*) x,
    (*
    NStep e n ->
    WLang.CanRun (w_subst x e P) ->
    *)
    p_subst x e (tr P) = tr (w_subst x e P).
  Proof.
    induction P; intros e' y. simpl in *.
    - auto.
    - admit.
    - rename v into x.
      destruct r as (e1, e2).
      simpl.
      destruct (tr P) as (P_x, c_x) eqn:Ht.
      destruct (Set_VAR.MF.eq_dec y x). {
        subst.
        simpl.
        rewrite Ht.
        simpl.
        destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
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
      destruct (Set_VAR.MF.eq_dec y x) as [?|_]; try contradiction.
      simpl.
      destruct (tr (w_subst y e' P)) as (P_t, c_t) eqn:Ht'.
      repeat rewrite subst_n_seq.
      repeat rewrite c_seq_subst.
      apply eq_pair_def. {
        apply eq_n_for_def; auto. {
          apply eq_n_seq_def; auto.
          rewrite <- IHP in Ht'.
          simpl in Ht'.
          invc Ht'.
          rewrite subst_subst_neq_3 with (x:=x) (y:=y); auto.
          - admit.
          - intros N.
            apply n_in_subst_to_n_in in N.
            (* XXX: Assume: NStep e' m *)
            admit. 
        }
        apply eq_n_seq_def. {
          rewrite <- IHP in Ht'.
          simpl in Ht'.
          invc Ht'.
          rewrite i_subst_subst_neq_3; auto.
          - (* XXX: Assume NStep e' n *)
            admit.
          - intros N.
            invc N; rename_hyp (NIn _ _) as N; invc N.
            contradiction.
        }
        apply eq_n_seq_def. {
          rewrite i_subst_subst_neq_3; auto.
          - (* XXX: Assume NStep e' n *)
            admit.
          - intros N.
            invc N; rename_hyp (NIn _ _) as N; invc N.
            contradiction.
        }
        rewrite <- IHP in Ht'.
        simpl in Ht'.
        invc Ht'.
        reflexivity.
      }
      rewrite <- IHP in Ht'.
      simpl in Ht'.
      invc Ht'.
      apply eq_c_seq_def. {
        admit.
      }
      admit.
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
      assert (Hx: RPick (e1,e2) n) by eauto using r_first_to_pick.
      rename_hyp (forall n, _) as IH.
      simpl in *.
      destruct Hp as [Hp|Hp]. {
        invc Hp; rename_hyp (IPairIn _ _) as Hi. {
          apply i_pair_in_inv_n_seq in Hi.
          destruct Hi as [Hi|[Hi|Hi]].
          - constructor; auto.
          - assert (IPairIn p (subst x (NNum n) P_x)) by admit.
            assert (IPairIn p (subst x (NNum n) (fst (tr P)))). {
              rewrite Ht.
              auto.
            }
            
            assert (WLang.IPairIn p (w_subst x e1 P)) by admit.
            apply IH with (p:=p) in Hx. {
              apply WLang.i_pair_in_for_1 with (e:=e1) (n0:=n);
                eauto using r_first_to_pick, r_first_to_eq.
              (* Works because:
                e1 ==> n
                WLang.IPairIn p (w_subst x (NNum n) P)
                -------------------------------------
                WLang.IPairIn p (w_subst x e1 P)
                *)
            }
              (* Works because:
                e1 ==> n
                WLang.IPairIn p (w_subst x (NNum n) P)
                -------------------------------------
                WLang.IPairIn p (w_subst x e1 P)
                *)
            admit.
      }
    induction P; simpl; intros.


  Lemma i_pair_fst_subst:
    forall P p x e n,
    NStep e n ->
    WLang.CanRun (w_subst x e P) ->
    IPairIn p (fst (tr (w_subst x e P))) ->
    IPairIn p (subst x e (fst (tr P))).
  Proof.
    induction P; simpl; intros.
    - assumption.
    - admit.
    - destruct r as (e1, e2).
      simpl.
      destruct (tr P) as (P_x, c_x) eqn:r1.
      simpl.
      rename_hyp (IPairIn _ _) as Hi.
      rename i into c.
      rename v into y.
      assert (r2: i_subst y e c = c) by admit.
      destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        simpl in Hi.
        rewrite r1 in *.
        simpl in *.
        invc Hi.
        - rename_hyp (IPairIn _ _) as Hi.
          rewrite subst_n_seq.
          repeat rewrite r2 in *.
          apply i_pair_in_inv_n_seq in Hi.
          destruct Hi as [Hi|[Hi|Hi]].
          + auto using i_pair_in_for_1, i_pair_in_n_seq_l.
          + apply i_pair_in_for_1.
            apply i_pair_in_n_seq_r.
      }
  Qed.


  Lemma tr_for_1:
    forall r e n p c1 c2 P x,
    RPick r n ->
    NStep e n ->
    PPairIn p (tr (w_subst x e P)) ->
    PPairIn p (tr (WFor c1 x r P c2)).
  Proof.
    intros.
    destruct (tr (w_subst x e P)) as (Px, cx) eqn:Ht.
    destruct (tr (WFor _ _ _ _ _)) as (Pt, ct) eqn:Hx.
    rename_hyp (PPairIn _ _) as Hi.
    destruct r as (e1, e2).
    rename_hyp (RPick _ _) as Hr.
    apply r_pick_inv_first in Hr.
    destruct Hr as [Hr|Hr]. {
      simpl.
      left.
      destruct Hi as [Hi|Hi]. {
        simpl in Hx.
        destruct (tr P) as (Ptx,Ctx) eqn:r1.
        invc Hx.
        apply i_pair_in_for_1.
        apply i_pair_in_n_seq_r.
      }
    simpl.
  Qed.

  (*
  
    a \in P 
    P >> Q
    ------
    a \in Q
    *)
  Lemma translate2_1:
    forall a P,
    WLang.IPairIn a P ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    PPairIn a (tr P).
  Proof.
    intros a P H.
    induction H; intros Hc Hn.
    - admit.
    - admit.
    - admit.
    - admit.
    - (* In P[x:=e] *)
      simpl.
      destruct r as (e1, e2).
      destruct (tr P) as (P_x, c_x) eqn:Ht.
      left.
      rename_hyp (RPick _ _) as Hr.
      apply r_pick_inv_first in Hr.
      destruct Hr as [Hr|Hr]. {
        eapply i_pair_in_for_1.
        apply i_pair_in_n_seq_r.
        eapply i_pair_in_subst; eauto.
        invc Hr.
        assumption.
      }
      apply i_pair_in_for_2 with (n:=n); auto.
      rewrite subst_n_seq.
      apply i_pair_in_for_2 with (n:=n).
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.


  Lemma translate2_1:
    forall a P,
    WLang.IPairIn a P ->
    forall Q,
    P >> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    PPairIn a Q.
  Proof.
    intros a P H.
    induction H; intros Qx Ht Hc Hv; invc Ht.
    - simpl.
      admit.
    - admit.
    - admit.
    - admit.
    - simpl.
      rename_hyp (P >> _) as Ht.
      assert (Hx := Ht).
      apply tr2_subst with (x:=x) (e:=e) in Hx; auto.
      assert  (Hx := tr2_subst P (P_x, c_x) H8 x e).
      simpl in *.
      apply IHIPairIn in Hx.
      2: { admit. }
      2: { admit. }
      simpl in Hx.
      destruct Hx. {
        left.
        rename_hyp (RPick _ _) as Hr.
        apply r_pick_inv_first in Hr.
        destruct Hr as [Hr|Hr]. {
          eapply i_pair_in_for_1.
          apply i_pair_in_n_seq_r.
          unfold P_e1.
          eapply i_pair_in_subst; eauto.
          invc Hr.
          assumption.
        }
        apply i_pair_in_for_2 with (n:=n); auto.
        rewrite subst_n_seq.
        rewrite subst_n_seq.
        apply i_pair_in_n_seq_r.
        apply i_pair_in_n_seq_r.
        eapply i_pair_in_subst; eauto using n_step_num.
      }
      left.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma translate_1:
    forall a P,
    WLang.IPairIn a P ->
    forall Q,
    P |> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    PPairIn a Q.
  Proof.
    intros a P H.
    induction H; intros Qx Ht Hc Hv; invc Ht.
    - simpl.
      left.
      constructor.
      assumption.
    - rename_hyp (i |> _) as Ht1.
      admit.
    - admit.
    - admit.
    - simpl.
      left.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Qed.

  Lemma translate_2:
    forall a Q,
    PPairIn a Q ->
    forall P,
    P |> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    WLang.IPairIn a P.
  Proof.
    intros a (Q, c) H.
    simpl in H.
    destruct H. {
      generalize dependent c.
      induction H; intros cx Px Ht Hc Hv.
      - assert (Hx: Px = WSync c /\ cx = Skip) by auto using tr_inv_sync.
        destruct Hx as (?, ?).
        subst.
        invc Ht.
        constructor; auto.
      - apply tr_inv_seq in Ht.
        destruct Ht as (P1, (P2, ((P1', c1), ((P2', c2), (?, (?, (?, r1))))))).
        simpl in *.
        invc r1.
        rename_hyp (_ |> (i, _)) as Hi.
        apply IHIPairIn in Hi; auto.
        + constructor; auto.
        + invc Hc; auto.
        + simpl in *; intuition.
      - apply tr_inv_seq in Ht.
        destruct Ht as (P1, (P2, ((P1', c1), ((P2', c2), (?, (?, (?, r1))))))).
        simpl in *.
        invc r1.
        rename_hyp (P2 |> _) as Ht2.
        assert (Hx := Ht2).
        apply tr_seq with (c:=c1) in Hx.
        apply IHIPairIn in Hx; auto.
        + apply WLang.i_pair_in_inv_w_seq in Hx.
          destruct Hx as [Hx|[Hx|Hx]].
          * apply WLang.i_pair_in_seq_l.
            admit.
          * admit.
          * admit.
        + admit.
        + admit.
      - admit.
      - admit.
    }
    intros.
    (* ----- *)
    intros P Q H.
    induction H; intros Hc Hv a Hi; invc Hc.
    - auto using p_pair_in_sync.
    - eapply p_pair_in_seq; eauto.
      + intros.
        apply IHTranslate1; auto.
        simpl in *.
        intuition.
      + intros.
        apply IHTranslate2; auto.
        simpl in *.
        intuition.
    - simpl in *.
      subst.
      destruct Hi as [Hi|Hi]. {
        invc Hi.
        - (* First iteration *)
          rename_hyp (RHasNext _) as Hx.
          destruct Hx as (m, Hx).
          eapply p_pair_in_for_first; eauto.
          intros.
          assert (RPick (e1, e2) m) by eauto using r_first_to_pick.
          assert (NStep e1 m) by eauto using r_first_to_eq.
          apply IHTranslate1; auto.
          + eauto using WLang.can_run_subst, n_step_num.
          + eapply wvar_subst_not_in; eauto.
            simpl in *.
            intuition.
        - (* Mid iteration *)
          rename_hyp (IPairIn _ _) as Hi.
          rewrite subst_n_seq in Hi.
          apply i_pair_in_inv_n_seq in Hi.
          rename_hyp (RHasNext _) as r1.
          destruct r1 as (n1, He1).
          destruct Hi as [Hi|[Hi|Hi]].
          + eapply WLang.i_pair_in_for_1 with (e:=NNum n); eauto using n_step_num.
            admit.
          + rewrite subst_n_seq in Hi.
            apply i_pair_in_inv_n_seq in Hi.
            destruct Hi as [Hi|[Hi|Hi]].
            * unfold c2_dec_x in Hi.
              admit.
            * admit.
            * admit.
          + rewrite subst_n_seq in Hi.
            admit.
      }
      (* Last iteration *)
      assert (Hl: exists m, RLast (e1, e2) m) by eauto using r_has_next_to_last.
      destruct Hl as (m, Hl).
      assert (NStep (NBin NMinus e2 (NNum 1)) m) by eauto using r_last_to_eq.
      assert (WLang.CanRun (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
        assert (Hc: WLang.CanRun (w_subst x (NNum m) P)) by auto using r_last_to_pick.
        eapply WLang.can_run_subst in Hc; eauto using n_step_num.
      }
      eapply p_par_in_for_last; eauto.
      + intuition.
      + intros.
        apply IHTranslate4; auto.
        eapply wvar_subst_not_in; eauto.
        intuition.
  Admitted.

  Lemma translate_1:
    forall a i,
    WLang.IPairIn a i ->
    PPairIn a (tr i).
  Proof.
    intros i a H.
    induction H; simpl;
      try rename b into i;
      try destruct r as (e1, e2);
      try remember (fst (i (NNum n))) as i_n.
    - left.
      constructor.
      assumption.
    - auto using p_pair_in_seq_l.
    - auto using p_pair_in_seq_r.
    - admit.
    - (*
      destruct (tr i) as (b, c) eqn:Ht.
      rewrite tr_subst in IHIPairIn.
      simpl.
      left.
      apply i_pair_in_for_1.
      rewrite Ht in *.
      simpl in *. *)
      admit.
    - 
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
End Defs.
