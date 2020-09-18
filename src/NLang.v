Require Import AccExp.
Require Import Tasks.
Require Import Conc.
Require Import NExp.
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

  Fixpoint w_seq (c:Conc.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (c_seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 x r P c2 => WFor (c_seq c c1) x r P c2
   end.

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
  (*
        c ; sync |> ( c, skip )
  *) 
  | translate_sync:
    forall c,
    WSync c |> (NSync c, Conc.Skip)

  | translate_seq:
    forall P P' Q Q' R,
    P |> P' ->
    Q |> Q' ->
    R = p_seq P' Q' ->
    (* --------- *)
    WSeq P Q |> R  
  
  | translate_for:
    forall x e1 e2 P c2 c1 P_e1 c_e1 P_dec_e2 P_dec_x c_dec_x c_dec_e2 P_x c_x P' c', 
    w_subst x e1 P |> (P_e1, c_e1) ->
    w_subst x (NBin NMinus (NVar x) (NNum 1)) P |> (P_dec_x , c_dec_x) ->
    P |> (P_x, c_x) ->
    w_subst x (NBin NMinus e2 (NNum 1)) P |> (P_dec_e2, c_dec_e2) ->
    let c2_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c2 in
    let c2_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    P' =
      NFor
        (n_seq c1 P_e1) x (e1, e2)
        (n_seq c_dec_x (n_seq c2_dec_x P_x)) ->
    c' = c_seq c_dec_e2 c2_dec_e2 ->
    WFor c1 x (e1, e2) P c2 |> (P', c')
    
  where " P |> Q" := (Translate P Q).

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

  Inductive TPairIn a : w_inst -> Prop :=
  | t_pair_in_sync:
    forall c,
    CPairIn a c ->
    TPairIn a (WSync c)
  | t_pair_in_seq_l:
    forall P Q,
    TPairIn a P ->
    TPairIn a (WSeq P Q)
  | t_pair_in_seq_r:
    forall P Q,
    TPairIn a Q ->
    TPairIn a (WSeq P Q)
  | t_pair_in_seq_both:
    forall P Q,
    OneOf a (inr P) (inr Q) ->
    TPairIn a (WSeq P Q)
  | t_pair_in_for_1:
    forall c1 n x r e P c,
    RPick r n ->
    NStep e n ->
    TPairIn a (w_subst x e P) ->
    TPairIn a (WFor c1 x r P c)
  | t_pair_in_for_2:
    forall r e n c1 P x c2,
    RPick r n ->
    NStep e n ->
    CPairIn a (Conc.i_subst x e c2) ->
    TPairIn a (WFor c1 x r P c2)
  .

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
    (* TODO: PLEASE PROVE ME! *)
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
    - destruct Q' as (Q', c').
      assert (c' = c). {
        symmetry.
        eapply p_seq_inv_snd; eauto.
      }
      subst.
      apply IHILast in H3.
      assumption.
    - assert (Hn: NStep (NBin NMinus e2 (NNum 1)) n) by eauto using r_last_to_eq.
      rename_hyp (_ |> (P_dec_e2, c_dec_e2)) as H_e2.
      eapply H1 in H_e2; eauto.
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
    - subst.
      destruct P' as (P', c1).
      destruct Q' as (Q', c2).
      simpl in *.
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
    (* TODO: PROVE ME PLEASE! *)
  Admitted.

  Lemma i_first_inv_n_seq:
    forall a c P,
    IFirst a (n_seq c P) ->
    CIn a c \/ IFirst a P.
  Proof.
    (* TODO: PROVE ME PLEASE! *)
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
    - subst.
      apply p_first_inv_p_seq in Hi.
      constructor; auto.
    - invc_hyp (_ = _).
    - invc_hyp (_ = _).
    - invc_hyp (_ = _).
      rename_hyp (IFirst _ _) as Hi.
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
  Admitted.

  Lemma translate_1:
    forall P Q,
    P |> Q ->
    WLang.CanRun P ->
    ~ WVar TID P ->
    forall a,
    PPairIn a Q ->
    TPairIn a P.
  Proof.
    intros P Q H.
    induction H; intros Hc Hv a Hi; invc Hc.
    - simpl in *.
      destruct Hi as [Hi|Hi].
      + inversion Hi; subst; clear Hi.
        auto using t_pair_in_sync.
      + apply c_pair_in_skip in Hi.
        contradiction.
    - subst.
      (*
      | i_pair_in_seq_l:
        forall p i j,
        IPairIn p i ->
        IPairIn p (WSeq i j)
      | i_pair_in_seq_r:
        forall p i j,
        IPairIn p j ->
        IPairIn p (WSeq i j)
      | i_pair_in_seq_both:
        forall p i j c1 c2,
        GetLast i c1 ->
        GetFirst j c2 ->
        IOneOf p c1 c2 ->
        IPairIn p (WSeq i j)
      *)
      apply p_pair_in_inv_p_seq in Hi.
      destruct Hi as [Hi|[Hi|Hi]].
      + apply t_pair_in_seq_l.
        apply IHTranslate1; auto.
        simpl in *.
        intuition.
      + apply t_pair_in_seq_r.
        apply IHTranslate2; auto.
        simpl in *.
        intuition.
      + eapply p_one_of_to_one_of in Hi; eauto using t_pair_in_seq_both.
    - simpl in *.
      subst.
      destruct Hi as [Hi|Hi]. {
        inversion Hi; subst; clear Hi.
        - (* First iteration *)
          (*
          | i_pair_in_for_first_1:
            forall r c1 p P c2 x,
            CPairIn p c1 ->
            IPairIn p (WFor c1 x r P c2)
          | i_pair_in_for_first_2:
            forall r e n c1 c3 p P x c2,
            RFirst r n ->
            NStep e n ->
            GetFirst (w_subst x e P) c3 ->
            IOneOf p c1 c3 ->
            IPairIn p (WFor c1 x r P c2)
          *)
          (* Prove:
            IPairIn a (n_seq c1 P_e1) ->
            CPairIn a c1 \/ CPairIn a P_e1 \/ OneOf c1 (GetFirst P_e1) *)
          admit.
        - (* Mid iteration *)
          (*
          | i_pair_in_for_mid_1:
            forall r n c1 c3 p x P c2 e e',
            RPick2 r n ->
            NStep e n ->
            NStep e' (S n) ->
            GetFirst (w_subst x e' P) c3 ->
            IOneOf p (Conc.i_subst x e c2) c3 ->
            IPairIn p (WFor c1 x r P c2)

          | i_pair_in_for_mid_2:
            forall r n e e' P x c2 c1 c c' p,
            RPick2 r n ->
            NStep e n ->
            NStep e' (S n) ->
            GetLast (w_subst x e P) c ->
            GetFirst (w_subst x e' P) c' ->
            IOneOf p c c' ->
            IPairIn p (WFor c1 x r P c2)
           *)
          admit.
      }
      (* Last iteration *)
      unfold c2_dec_e2 in Hi.
      inversion Hi; subst; clear Hi.
      rename_hyp (CIn a1 _) as Ha.
      rename_hyp (CIn a2 _) as Hb.
      apply c_in_inv_c_seq in Ha.
      apply c_in_inv_c_seq in Hb.
      assert (Hl: exists m, RLast (e1, e2) m) by eauto using r_has_next_to_last.
      destruct Hl as (m, Hl).
      assert (NStep (NBin NMinus e2 (NNum 1)) m) by eauto using r_last_to_eq.
      assert (WLang.CanRun (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
        assert (Hc: WLang.CanRun (w_subst x (NNum m) P)) by auto using r_last_to_pick.
        eapply WLang.can_run_subst in Hc; eauto using n_step_num.
      }
      assert (~ WVar TID (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
        simpl in *.
        eapply wvar_subst_not_in; eauto.
        intuition.
      }
      destruct Ha as [Ha|Ha];
        destruct Hb as [Hb|Hb].
      + (*
        | i_pair_in_for_1:
          forall r e n c1 P c2 p x,
          RPick r n ->
          NStep e n ->
          IPairIn p (w_subst x e P) ->
          IPairIn p (WFor c1 x r P c2)
        *)
        assert (CPairIn (a1, a2) c_dec_e2) by auto using c_pair_in_def.
        assert (TPairIn (a1, a2) (w_subst x (NBin NMinus e2 (NNum 1)) P)) by auto.
        (* We must show that r has at least one iteration, which
           allows us to learn that it has a last iteration.
           *)
        eapply t_pair_in_for_1; eauto using r_last_to_pick.
      + (*
        | i_pair_in_for_3:
          forall r e n c1 c3 x p P c2,
          RPick r n ->
          GetLast (w_subst x e P) c3 ->
          IOneOf p c3 (Conc.i_subst x e c2) ->
          IPairIn p (WFor c1 x r P c2)
        *)
        assert (WLang.ILast a1 (w_subst x (NBin NMinus e2 (NNum 1)) P)). {
          apply i_last_to_translate with (a:=a1) in H2; auto; simpl.
        }
        admit.
      + (*
        | i_pair_in_for_3:
          forall r e n c1 c3 x p P c2,
          RPick r n ->
          GetLast (w_subst x e P) c3 ->
          IOneOf p c3 (Conc.i_subst x e c2) ->
          IPairIn p (WFor c1 x r P c2)
        *)
        admit.
      + assert (CPairIn (a1, a2) c2_dec_e2) by auto using c_pair_in_def.
        unfold c2_dec_e2 in *.
        (* We must show that r has at least one iteration, which
           allows us to learn that it has a last iteration.
           *)
        eapply t_pair_in_for_2; eauto using r_last_to_pick.
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
