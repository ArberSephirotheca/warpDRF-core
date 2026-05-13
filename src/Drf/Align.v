From Faial.Core Require Import AVal.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Var.
Require Import WLang.
Require Import ULang.
Require Import Pure.NExp.
Require Import Pure.RExp.
From Faial.Core Require Import Tictac.
Require Import ALang.
From Faial.Core Require Import Util.
From Stdlib Require Import Lia.
Require SIMT.NExp.

Section Props.
  Context `{T:Tasks}.
  Notation from_pure := SIMT.NExp.from_pure.
  (*
    ~~~~~ Function align (Figure 3) ~~~~~~~
   *)
  Fixpoint align (w:w_inst) : p_inst :=
    match w with
    | WSync c => (NSync c, ULang.Skip)
    | WSeq P Q =>
      let (P', c1) := align P in
      let (Q', c2) := align Q in
      (NSeq P' (n_seq c1 Q'), c2)
    | WFor c1 x (e1, e2) P c2 =>
      let (P_x, c_x) := align P in
      let P_e1 := subst x e1 P_x in
      let c_e1 := i_subst x (from_pure e1) c_x in
      let dec_x := from_pure (NBin NMinus (NVar x) (NNum 1)) in
      let dec_e2 := from_pure (NBin NMinus e2 (NNum 1)) in
      let c_dec_x := i_subst x dec_x c_x in
      let c2_dec_x := i_subst x dec_x c2 in
      let c_dec_e2 := i_subst x dec_e2 c_x in
      let c2_dec_e2 := i_subst x dec_e2 c2 in
      (NFor (n_seq c1 P_e1) x (NBin NPlus (NNum 1) e1, e2)
                        (n_seq c_dec_x (n_seq c2_dec_x P_x)),
                     ULang.c_seq c_dec_e2 c2_dec_e2)
    end.


  Lemma var_inv_align:
    forall x P,
    PVar x (align P) ->
    WVar x P.
  Proof.
    induction P; simpl; intros; try (intuition; fail).
    - destruct (align P1) as (P1', c1).
      destruct (align P2) as (P2', c2).
      simpl in *.
      destruct H as [[H|H]|H]; auto.
      apply var_inv_n_seq in H.
      intuition.
    - destruct r as (e1, e2).
      destruct (align P) as (Px, cx).
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
        rename_hyp (ULang.Var _ _) as Hc.
        apply ULang.var_inv_subst in Hc.
        intuition.
        rename_hyp (Var _ (n_seq _ _)) as Hc.
        apply var_inv_n_seq in Hc.
        intuition.
        rename_hyp (ULang.Var _ _) as Hc.
        apply ULang.var_inv_subst in Hc.
        intuition.
      + rename_hyp (ULang.Var _ (ULang.c_seq _ _ )) as Hc.
        apply ULang.var_inv_c_seq in Hc.
        intuition.
        * rename_hyp (ULang.Var _ (i_subst _ _ _)) as Hc.
          apply ULang.var_inv_subst in Hc.
          intuition.
        * rename_hyp (ULang.Var _ (i_subst _ _ _)) as Hc.
          apply ULang.var_inv_subst in Hc.
          intuition.
  Qed.

  Lemma var_inv_align_l:
    forall x P P_x c_x,
    Var x P_x ->
    align P = (P_x, c_x) ->
    WVar x P.
  Proof.
    intros.
    assert (PVar x (align P)). {
      rewrite H0.
      simpl.
      auto.
    }
    auto using var_inv_align.
  Qed.

  Lemma var_inv_align_r:
    forall x P P_x c_x,
    ULang.Var x c_x ->
    align P = (P_x, c_x) ->
    WVar x P.
  Proof.
    intros.
    assert (PVar x (align P)). {
      rewrite H0.
      simpl.
      auto.
    }
    auto using var_inv_align.
  Qed.

  Lemma align_subst:
    forall P e x,
    NClosed e ->
    ~ WVar x P ->
    (* [[ P ]] [x := e ] = [[ P[x := e] ]] *)
    p_subst x e (align P) = align (w_subst x e P).
  Proof.
    induction P; intros e' y Hc Hd; simpl in *.
    - auto.
    - destruct (align P1) as (P1_x, c1_x) eqn:Ht1.
      destruct (align P2) as (P2_x, c2_x) eqn:Ht2.
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
      destruct (align P) as (P_x, c_x) eqn:Ht.
      assert (~ Var y P_x). {
        intros N.
        eapply var_inv_align_l with (x:=y) in N; eauto.
      }
      assert (~ ULang.Var y c_x). {
        intros N.
        eapply var_inv_align_r with (x:=y) in N; eauto.
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
          rewrite <- NExp.n_subst_from_pure.
          simpl.
          reflexivity.
        }
        repeat rewrite i_subst_subst_eq_1.
        rewrite <- NExp.n_subst_from_pure.
        simpl.
        reflexivity.
      }
      simpl.
      (* y <> x *)
      remove_eq y x.
      simpl.
      destruct (align (w_subst y e' P)) as (P_t, c_t) eqn:Ht'.
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
          - rewrite <- NExp.n_free_from_pure.
            auto.
          - assert (hx :
              NExp.NBin NMinus (NExp.NVar x) (NExp.NNum 1) =
              from_pure (NBin NMinus (NVar x) (NNum 1))
            ) by reflexivity.
            simpl.
            intuition.
        }
        apply eq_n_seq_def. {
          rewrite i_subst_subst_neq_3; auto.
          - rewrite <- NExp.n_free_from_pure.
            auto.
          - assert (hx :
              NExp.NBin NMinus (NExp.NVar x) (NExp.NNum 1) =
              from_pure (NBin NMinus (NVar x) (NNum 1))
            ) by reflexivity.
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
        rewrite i_subst_subst_neq_5; auto.
        + rewrite <- NExp.n_subst_from_pure.
          reflexivity.
        + rewrite <- NExp.n_closed_from_pure.
          assumption.
      }
      rewrite i_subst_subst_neq_5; auto.
      + rewrite <- NExp.n_subst_from_pure.
        reflexivity.
      + rewrite <- NExp.n_closed_from_pure.
        assumption.
      + intuition.
  Qed.

  Lemma align_to_subst:
    forall P P_x c_x,
    align P = (P_x, c_x) ->
    forall x v,
    NClosed v ->
    ~ WVar x P ->
    align (w_subst x v P) = (subst x v P_x, i_subst x (from_pure v) c_x).
  Proof.
    intros.
    rewrite <- align_subst; auto.
    rewrite H.
    auto.
  Qed.

  (* ----------------------- GET FIRST ------------------------ *)

  Lemma get_first_align_1:
    forall P c,
    GetFirst P c ->
    WLang.Distinct P ->
    forall a,
    CIn a c ->
    IFirst a (fst (align P)).
  Proof.
    intros P c H.
    induction H.
    all: simpl.
    all: intros Hd a Hc.
    - constructor.
      auto.
    - destruct (align P) as (Px1, cx1) eqn:Ht1.
      destruct (align Q) as (Px2, cx2) eqn:Ht2.
      simpl.
      apply i_first_seq.
      intuition.
    - destruct r as (e1, e2).
      destruct (align P) as (Px, cx) eqn:Ht.
      simpl.
      apply c_in_inv_c_seq in Hc.
      constructor.
      destruct Hc as [Hc|Hc]. {
        auto using i_first_n_seq_l.
      }
      apply IHGetFirst in Hc.
      apply align_to_subst with (x:=x) (v:=NNum n) in Ht.
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

  Lemma get_first_align_2:
    forall P c,
    GetFirst P c ->
    WLang.Distinct P ->
    forall a,
    IFirst a (fst (align P)) ->
    CIn a c.
  Proof.
    intros P c H.
    induction H; simpl; intros Hd a Hf; invc Hf.
    - assumption.
    - destruct (align P).
      destruct (align Q).
      invc H0.
    - destruct (align P) as (Px1, cx1) eqn:Ht1.
      destruct (align Q) as (Px2, cx2) eqn:Ht2.
      simpl in *.
      destruct Hd.
      invc H0.
      eauto.
    - destruct (align P) as (P_t, c_P) eqn:HP.
      destruct (align Q) as (Q_t, c_Q) eqn:HQ.
      simpl in *.
      destruct Hd.
      invc H0.
    - destruct r, (align P).
      invc H1.
    - destruct r, (align P).
      invc H1.
    - destruct r as (e1, e2).
      destruct (align P) as (P_t, c_P) eqn:HP.
      simpl in *.
      invc H1.
      rename_hyp (IFirst _ _) as Hi.
      apply i_first_inv_n_seq in Hi.
      destruct Hi as [Hi|Hi].
      + auto using c_in_c_seq_l.
      + apply c_in_c_seq_r.
        apply IHGetFirst.
        * apply WLang.distinct_subst.
          intuition.
        * apply align_to_subst with (x:=x) (v:=NNum n) in HP;
            eauto using n_step_to_closed, n_step_num. {
            rewrite HP.
            simpl.
            apply i_first_subst with
              (v1:=e1) (n:=n); auto.
            eapply r_first_to_eq; eauto.
            auto using n_step_num.
          }
          intuition.
  Qed.

  Corollary i_first_align:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    forall a,
    IFirst a (fst (align P)) <->
    WLang.IFirst a P.
  Proof.
    intros P Hc Hd Hv.
    apply get_first_exists in Hc.
    destruct Hc as (c, Hg).
    split; intros.
    - eapply get_first_align_2 in H; eauto.
      rewrite get_first_spec; eauto.
    - eapply get_first_align_1; eauto.
      rewrite <- get_first_spec; eauto.
  Qed.

  Lemma i_first_align_1:
    forall v r n P x P_x c_x,
    WLang.Distinct P ->
    WLang.CanRun (w_subst x (NNum n) P) ->
    align P = (P_x, c_x) ->
    NStep v n ->
    RPick r n ->
    ~ WVar x P ->
    forall a,
    IFirst a (subst x v P_x) ->
    WLang.IFirst a (w_subst x v P).
  Proof.
    intros.
    rename_hyp (align _ = _) as Ht.
    apply align_to_subst with (x:=x) (v:=v) in Ht;
      eauto using n_step_to_closed.
    assert (WLang.CanRun (w_subst x v P)). {
      eapply WLang.can_run_subst; eauto using n_step_num.
    }
    apply i_first_align; auto.
    - auto using WLang.distinct_subst.
    - rewrite Ht.
      simpl.
      assumption.
  Qed.

  (* -------------------------------- GET LAST ------------------------ *)

  Lemma get_last_align_1:
    forall P c,
    GetLast P c ->
    WLang.Distinct P ->
    forall a,
    CIn a c ->
    CIn a (snd (align P)).
  Proof.
    intros P c H.
    induction H; simpl; intros Hd a Hc.
    - assumption.
    - destruct (align P) as (P',c_p) eqn:Ht1.
      destruct (align Q) as (Q',c_q) eqn:Ht2.
      intuition.
    - destruct r as (e1, e2).
      destruct (align P) as (P',c_p) eqn:Ht1.
      simpl.
      apply c_in_inv_c_seq in Hc.
      apply align_to_subst with (x:=x) (v:=NNum n) in Ht1;
        eauto using n_step_to_closed, n_step_num.
      2: { intuition. }
      destruct Hc as [Hc|Hc].
      + apply c_in_c_seq_l.
        apply IHGetLast in Hc; clear IHGetLast.
        2: { apply WLang.distinct_subst. intuition. }
        rewrite Ht1 in Hc.
        simpl in *.
        assert (hx:
          NExp.NBin NMinus (from_pure e2) (NExp.NNum 1) =
          from_pure (NBin NMinus e2 (NNum 1))
        ) by reflexivity.
        rewrite hx.
        apply c_in_subst with (v:=NNum n) (n := n);
          eauto using n_step_num, r_last_to_eq.
      + apply c_in_c_seq_r.
        assert (hx:
          NExp.NBin NMinus (from_pure e2) (NExp.NNum 1) =
          from_pure (NBin NMinus e2 (NNum 1))
        ) by reflexivity.
        rewrite hx.
        apply c_in_subst with (v:=NNum n) (n := n);
          eauto using n_step_num, r_last_to_eq.
  Qed.

  Lemma get_last_align_2:
    forall P c,
    GetLast P c ->
    WLang.Distinct P ->
    forall a,
    CIn a (snd (align P)) ->
    CIn a c.
  Proof.
    intros P c H.
    induction H; simpl; intros Hd a Hf; invc Hf.
    - invc H0.
    - destruct (align P).
      destruct (align Q) as (Q',c_q) eqn:Ht2.
      intuition.
      simpl in *.
      auto using c_in_def.
    - simpl in *.
      destruct r as (e1, e2).
      destruct (align P) as (P',c_p) eqn:Ht1.
      simpl in *.
      apply align_to_subst with (x:=x) (v:=NNum n) in Ht1;
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
        * assert (hx: NExp.NNum n = from_pure (NNum n) ) by reflexivity.
          rewrite hx.
          apply c_in_subst with (v:=NBin NMinus e2 (NNum 1)) (n := n);
          eauto using n_step_num, r_last_to_eq.
      + apply c_in_def in Hi; auto.
        apply c_in_c_seq_r.
        assert (hx: NExp.NNum n = from_pure (NNum n) ) by reflexivity.
        rewrite hx.
        apply c_in_subst with (v:=NBin NMinus e2 (NNum 1)) (n := n);
          eauto using n_step_num, r_last_to_eq.
  Qed.

  Corollary i_last_align:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    forall a,
    CIn a (snd (align P)) <->
    WLang.ILast a P.
  Proof.
    intros P Hc Hd Hv.
    apply get_last_exists in Hc.
    destruct Hc as (c, Hg).
    split; intros.
    - eapply get_last_align_2 in H; eauto.
      rewrite get_last_spec; eauto.
    - eapply get_last_align_1; eauto.
      rewrite <- get_last_spec; eauto.
  Qed.

  Lemma i_last_align_1:
    forall v r n P x P_x c_x,
    WLang.Distinct P ->
    WLang.CanRun (w_subst x (NNum n) P) ->
    align P = (P_x, c_x) ->
    NStep v n ->
    RPick r n ->
    ~ WVar x P ->
    forall a,
    CIn a (i_subst x (from_pure v) c_x) ->
    WLang.ILast a (w_subst x v P).
  Proof.
    intros.
    rename_hyp (align _ = _) as Ht.
    apply align_to_subst with (x:=x) (v:=v) in Ht;
      eauto using n_step_to_closed.
    assert (WLang.CanRun (w_subst x v P)). {
      eapply can_run_subst; eauto using n_step_num.
    }
    apply i_last_align; auto.
    - auto using WLang.distinct_subst.
    - rewrite Ht.
      simpl.
      assumption.
  Qed.

  (* -------------------- IPairIn Translation ------------------------ *)

  Lemma i_pair_in_align_for_1:
    forall p c1 x r P c2,
    (forall n,
     RPick r n ->
     forall p,
     PPairIn p (align (w_subst x (NNum n) P)) -> WLang.IPairIn p (w_subst x (NNum n) P)) ->
    ~ WVar x P ->
    forall P_x c_x,
    align P = (P_x, c_x) ->
    forall e n,
    RPick r n ->
    NStep e n ->
    IPairIn p (subst x e P_x) ->
    WLang.IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    eapply WLang.i_pair_in_for_1 with (e:=NNum n); eauto using n_step_num.
    apply H; auto.
    assert (IPairIn p (subst x (NNum n) P_x)). {
      eapply i_pair_in_subst; eauto using n_step_num.
    }
    rewrite <- align_subst; auto using n_closed_num.
    rename_hyp (align P = _) as rx.
    rewrite rx.
    simpl.
    auto.
  Qed.

  Import ALangNotations.

  Lemma i_pair_in_align_for_2:
    forall p c1 x r P c2,
    (forall n,
     RPick r n ->
     forall p,
     PPairIn p (align (w_subst x (NNum n) P)) -> WLang.IPairIn p (w_subst x (NNum n) P)) ->
    ~ WVar x P ->
    forall P_x c_x,
    align P = (P_x, c_x) ->
    forall e n,
    RPick r n ->
    NStep e n ->
    CPairIn p (i_subst x (from_pure e) c_x) ->
    WLang.IPairIn p (WFor c1 x r P c2).
  Proof.
    intros.
    eapply WLang.i_pair_in_for_1 with (e:=NNum n); eauto using n_step_num.
    apply H; auto.
    rename_hyp (align _ = _) as hr.
    apply align_to_subst with (x:=x) (v:=NNum n) in hr; auto using n_closed_num.
    rewrite hr.
    simpl.
    right.
    assert (hx: NExp.NNum n = from_pure (NNum n) ) by reflexivity.
    rewrite hx.
    eapply c_pair_in_subst; eauto using n_step_num.
  Qed.

  Import NExpNotations.

  Lemma in_1:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    forall p,
    PPairIn p (align P) ->
    WLang.IPairIn p P.
  Proof.
    intros P H.
    induction H; intros Hd p Hp; simpl in Hp; try (destruct Hp as [Hp|Hp]).
    - invc Hp.
      constructor.
      assumption.
    - apply c_pair_in_skip in Hp.
      contradiction.
    - rename i into P.
      rename j into Q.
      destruct (align P) as (P', c1) eqn:Ht1.
      destruct (align Q) as (Q', c2) eqn:Ht2.
      simpl in *.
      destruct Hd as (Hd1, Hd2).
      destruct Hp as [Hp|Hp]. {
        invc Hp. {
          apply WLang.i_pair_in_seq_l.
          auto.
        }
        rename_hyp (IPairIn _ _) as Hp.
        apply i_pair_in_inv_n_seq in Hp.
        destruct Hp as [Hp|[Hp|Hp]].
        - apply WLang.i_pair_in_seq_l.
          auto.
        - apply WLang.i_pair_in_seq_r.
          auto.
        - destruct p as (a1, a2).
          simpl in *.
          destruct Hp as [(Hp1, Hp2)|(Hp1,Hp2)]; apply WLang.i_pair_in_seq_both; simpl.
          + left.
            split. {
              apply i_last_align; auto.
              rewrite Ht1.
              auto.
            }
            apply i_first_align; auto.
            rewrite Ht2.
            auto.
          + right.
            split. {
              apply i_last_align; auto.
              rewrite Ht1.
              auto.
            }
            apply i_first_align; auto.
            rewrite Ht2.
            auto.
      }
      apply WLang.i_pair_in_seq_r.
      auto.
    - simpl in *.
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:Ht.
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
            eapply i_pair_in_align_for_1; eauto.
            intros.
            eapply IH; auto using WLang.distinct_subst.
          - (* a1 \in c1 /\ a2 \in P[e1] *)
            eapply WLang.i_pair_in_for_first_2; eauto.
            destruct p as (a1, a2).
            simpl in *.
            intuition;
             eauto using i_first_align_1.
        }
        rename n0 into m.
        repeat rewrite subst_n_seq in Hp.
        apply i_pair_in_inv_n_seq in Hp.
        destruct Hp as [Hp|[Hp|Hp]].
        + (* p \in cx [m - 1] *)
          eapply i_pair_in_align_for_2 with (e:=m - 1) (n:=m - 1); eauto using n_step_num.
          * intros.
            apply IH; auto using WLang.distinct_subst.
          * auto using r_pick_impl_2.
          * rewrite i_subst_subst_eq_1 in Hp.
            simpl in Hp.
            remove_eq x x.
            assert (hy: NExp.NNum (m - 1) =
              from_pure (NNum (m - 1))
            ) by reflexivity.
            rewrite hy.
            eapply c_pair_in_subst with (e1:=NBin NMinus m 1); eauto using n_step_num.
            apply n_step_bin; auto using n_step_num.
        + apply i_pair_in_inv_n_seq in Hp.
          destruct Hp as [Hp|[Hp|Hp]].
          * (* p \in c2 [m - 1] *)
            rewrite i_subst_subst_eq_1 in Hp.
            simpl in Hp.
            remove_eq x x.
            eapply WLang.i_pair_in_for_2 with (n:=m - 1); eauto using n_step_num. {
              auto using r_pick_impl_2.
            }
            apply c_pair_in_subst with (e1:=(NBin NMinus m 1)) (n:=m - 1);
              auto using n_step_num.
            simpl.
            apply n_step_bin; auto using n_step_num.
          * (* p \in Px [m] *)
            clear Hx.
            eapply i_pair_in_align_for_1 with (e:=NNum m);
              eauto using n_step_num, r_pick_impl_1.
            intros.
            apply IH; auto using WLang.distinct_subst.
          * destruct p as (a1, a2).
            simpl in *.
            rename_hyp (RPick _ m) as Hi.
            assert (Hp_n1 := Hi).
            apply r_pick_impl_3 in Hi.
            destruct Hi as (n1, (?, Hi)).
            subst.
            apply i_pair_in_for_mid_1 with
              (n:=n1) (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
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
              eapply i_first_align_1 with (n:=S n1);
                eauto using n_step_num, r_pick_impl_1.
            }
            (* a2 \in c2[m - 1] /\ a1 \in IFirst (P_x [ m] ) *)
            simpl.
            right; split; auto.
            eapply i_first_align_1 with (n:=S n1);
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
                with (n:=n1) (e:=(NBin NMinus (S n1) 1));
                auto using r_pick_impl_1, r_pick2_to_pick, n_step_succ_minus_one.
              simpl.
              left.
              split; auto.
              eapply i_last_align_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            (* a1 \in cx[m - 1] /\ a2 \in P[m] *)
            eapply WLang.i_pair_in_for_mid_2 with
              (n:=n1)
              (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
              eauto using n_step_num, n_step_succ_minus_one.
            simpl.
            left.
            split. {
              eapply i_last_align_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            eapply i_first_align_1 with (n:=S n1);
              eauto using n_step_num, r_pick_impl_1.
          }
          apply i_first_inv_n_seq in Hp2.
          destruct Hp2 as [Hp2|Hp2]. {
            rewrite i_subst_subst_eq_1 in Hp2; simpl in Hp2; remove_eq x x.
            apply WLang.i_pair_in_for_3
              with (n:=n1) (e:=(NBin NMinus (S n1) 1));
              auto using r_pick_impl_1, r_pick2_to_pick, n_step_succ_minus_one.
            simpl.
            right.
            split; auto.
            (* a2 \in cx [m] *)
            eapply i_last_align_1 with (n:=n1) (r:=(e1, e2) );
              eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
          }
          (* a2 \in cx[m - 1] /\ a2 \in P[m] *)
            eapply WLang.i_pair_in_for_mid_2 with
              (n:=n1)
              (e:=(NBin NMinus (S n1) 1)) (e':=NNum (S n1));
              eauto using n_step_num, n_step_succ_minus_one.
            simpl.
            right.
            split. {
              eapply i_last_align_1 with (n:=n1) (r:=(e1, e2) );
                eauto using n_step, n_step_succ_minus_one, r_pick_impl_2, r_pick2_to_pick.
            }
            eapply i_first_align_1 with (n:=S n1);
              eauto using n_step_num, r_pick_impl_1.
     }
     (* p \in cx [ e2 - 1] \/ p \in c2[ e2 - 1] *)
     rename_hyp (CPairIn _ _) as Hi.
     apply c_pair_in_inv_c_seq in Hi.
     destruct p as (a1, a2).
     destruct Hi as (Ha, Hb).
     unfold ULang.OneOf in *.
     edestruct r_pick_impl_4 as (n2,(Hpick, Hn2)); eauto.
     intuition.
     + (* cx /\ cx *) 
       eapply i_pair_in_align_for_2 with
        (e:=NBin NMinus e2 (NNum 1)) (n:=n2);
        eauto using n_step_num, c_pair_in_def.
       intros.
       apply IH; auto using WLang.distinct_subst.
     + (* cx /\ c2 *)
       apply WLang.i_pair_in_for_3
         with (n:=n2) (e:=(NBin NMinus e2 (NNum 1)));
         auto using r_pick_impl_1.
       simpl.
       eauto using i_last_align_1.
     + (* c2 /\ cx *)
       apply WLang.i_pair_in_for_3
         with (n:=n2) (e:=(NBin NMinus e2 (NNum 1)));
         auto using r_pick_impl_1.
       simpl.
       eauto using i_last_align_1.
     + (* c2 /\ c2 *)
       apply WLang.i_pair_in_for_2 with
        (e:=NBin NMinus e2 (NNum 1)) (n:=n2);
        auto using c_pair_in_def.
  Qed.

  Corollary drf_1:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    WLang.DRF P ->
    DRF (align P).
  Proof.
    intros.
    unfold DRF, WLang.DRF.
    intros.
    apply in_1 in H2; auto.
  Qed.

  Lemma i_pair_in_n_seq_r:
    forall p P,
    IPairIn p P ->
    forall c,
    IPairIn p (n_seq c P).
  Proof.
    intros p P H.
    induction H; intros c'; simpl.
    - auto using i_pair_in_sync, c_pair_in_c_seq_r.
    - eauto using i_pair_in_seq_l, c_pair_in_seq_l.
    - eauto using i_pair_in_seq_r, c_pair_in_seq_r.
    - auto using i_pair_in_for_1.
    - eauto using i_pair_in_for_2, c_pair_in_seq_l.
  Qed.

  Lemma i_pair_in_n_seq_l:
    forall P p c,
    CPairIn p c ->
    IPairIn p (n_seq c P).
  Proof.
    induction P; intros; simpl.
    - auto using i_pair_in_sync, c_pair_in_c_seq_l.
    - eauto using i_pair_in_seq_l.
    - eauto using i_pair_in_for_1.
  Qed.

  Lemma i_pair_in_n_seq_1:
    forall P a1 c a2, 
    CIn a1 c ->
    IFirst a2 P ->
    IPairIn (a1, a2) (n_seq c P).
  Proof.
    induction P; simpl; intros a1 c a2 Hi Hf; invc Hf.
    - assert (CPairIn (a1, a2) (ULang.c_seq c i)). {
        auto using c_pair_in_def, c_in_c_seq_l, c_in_c_seq_r.
      }
      auto using i_pair_in_sync.
    - auto using i_pair_in_seq_l.
    - auto using i_pair_in_for_1.
  Qed.

  Lemma i_pair_in_n_seq_2:
    forall P a1 c a2, 
    IFirst a1 P ->
    CIn a2 c ->
    IPairIn (a1, a2) (n_seq c P).
  Proof.
    induction P; simpl; intros a1 c a2 Hf Hi; invc Hf.
    - assert (CPairIn (a1, a2) (ULang.c_seq c i)). {
        auto using c_pair_in_def, c_in_c_seq_l, c_in_c_seq_r.
      }
      auto using i_pair_in_sync.
    - auto using i_pair_in_seq_l.
    - auto using i_pair_in_for_1.
  Qed.

  Lemma i_first_to_c_in_1:
    forall e n x P P_x c_x a e',
    WLang.Distinct P ->
    NStep e n ->
    ~ WVar x P ->
    align P = (P_x, c_x) ->
    WLang.CanRun (w_subst x e P) ->
    WLang.IFirst a (w_subst x e P) ->
    NStep e' n ->
    IFirst a (subst x e' P_x).
  Proof.
    intros.
    rename_hyp (_ = _) as r1.
    rename_hyp (WLang.IFirst _ _) as hf.
    apply i_first_align in hf; eauto using WLang.distinct_subst.
    rewrite <- align_subst in hf.
    rewrite r1 in hf.
    simpl in *.
    eapply i_first_subst; eauto.
    * eauto using n_step_to_closed.
    * auto.
  Qed.

  Lemma i_last_to_c_in_1:
    forall e e' n x P P_x c_x a,
    NStep e' n ->
    NStep e n ->
    ~ WVar x P ->
    WLang.Distinct P ->
    align P = (P_x, c_x) ->
    WLang.CanRun (w_subst x n P) ->
    ILast a (w_subst x e P) ->
    CIn a (i_subst x (from_pure e') c_x).
  Proof.
    intros.
    rename_hyp (ILast _ _) as hl.
    rename_hyp (align _ = _) as r1.
    apply i_last_align in hl; auto.
    * rewrite <- align_subst in hl; eauto using n_step_to_closed.
      rewrite r1 in hl.
      simpl in hl.
      eapply c_in_subst; eauto using n_step_succ_minus_one.
    * eapply can_run_subst with (v1:=NNum n); eauto using n_step_num.
    * auto using WLang.distinct_subst.
  Qed.

  (* ---------------------------------------------------------------- *)

  Lemma in_2:
    forall p P,
    WLang.IPairIn p P ->
    WLang.CanRun P ->
    WLang.Distinct P ->
    PPairIn p (align P).
  Proof.
    intros p P H.
    induction H; intros Hc Hd; simpl in *.
    - (* i_pair_in_sync *)
      left.
      constructor.
      auto.
    - (* i_pair_in_seq_l *)
      destruct (align i) as (P, c_P) eqn:r1.
      destruct (align j) as (Q, c_Q) eqn:r2.
      simpl in *.
      invc Hc.
      destruct Hd.
      destruct IHIPairIn as [Hi|Hi]; auto. {
        left.
        constructor.
        auto.
      }
      auto using i_pair_in_seq_r, i_pair_in_n_seq_l.
    - (* i_pair_in_seq_r *)
      destruct (align i) as (P, c_P) eqn:r1.
      destruct (align j) as (Q, c_Q) eqn:r2.
      simpl in *.
      invc Hc.
      destruct Hd.
      destruct IHIPairIn as [Hi|Hi];
        auto using i_pair_in_seq_r, i_pair_in_n_seq_r.
    - (* i_pair_in_seq_both *)
      destruct (align P) as (P', c_P) eqn:r1.
      destruct (align Q) as (Q', c_Q) eqn:r2.
      destruct p as (a1, a2).
      simpl in *.
      invc Hc.
      destruct Hd.
      intuition. {
        rename_hyp (ILast _ _) as hl.
        apply i_last_align in hl; auto.
        rewrite r1 in hl.
        simpl in *.
        rename_hyp (WLang.IFirst _ _) as hf.
        assert (IFirst a2 (fst (align Q))). {
          apply i_first_align; auto.
        }
        rewrite r2 in *.
        auto using i_pair_in_n_seq_1, i_pair_in_seq_r.
      }
      rename_hyp (ILast _ _) as hl.
      apply i_last_align in hl; auto.
      rewrite r1 in hl.
      simpl in *.
      rename_hyp (WLang.IFirst _ _) as hf.
      assert (IFirst a1 (fst (align Q))). {
        apply i_first_align; auto.
      }
      rewrite r2 in *.
      simpl in *.
      auto using i_pair_in_n_seq_2, i_pair_in_seq_r.
    - (* i_pair_in_for_1 *)
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      invc Hc.
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      assert (Hx1: WLang.CanRun (w_subst x e P)). {
        assert (Hx1: WLang.CanRun (w_subst x n P)). {
          auto.
        }
        eapply can_run_subst; eauto using n_step_num.
      }
      assert (Hx2: WLang.Distinct (w_subst x e P)). {
        auto using WLang.distinct_subst.
      }
      assert (IHIPairIn := IHIPairIn Hx1 Hx2); clear Hx1 Hx2.
      apply align_to_subst with (x:=x) (v:=e) in r1.
      2: { eauto using n_step_to_closed. }
      2: { intuition. }
      rewrite r1 in IHIPairIn.
      simpl in *.
      destruct IHIPairIn as [Hp|Hp]. {
        left.
        (* Are we in the first phase or phase n+1? *)
        rename_hyp (RPick _ _) as hp.
        apply r_pick_inv_first in hp.
        destruct hp as [hp|hp]. {
          (* first phase *)
          apply i_pair_in_for_1.
          apply i_pair_in_n_seq_r.
          eapply i_pair_in_subst; eauto using r_first_to_eq.
        }
        (* n + 1 *)
        apply i_pair_in_for_2 with (n:=n); auto.
        rewrite subst_n_seq.
        apply i_pair_in_n_seq_r.
        rewrite subst_n_seq.
        apply i_pair_in_n_seq_r.
        eapply i_pair_in_subst; eauto using n_step_num.
      }
      (* since this is the end of the loop's body, then either
         it's inside the loop or it is the last iteration *)
      rename_hyp (RPick _ _) as hp.
      apply r_pick_inv_last in hp.
      destruct hp as [hp|hp]. {
        (* last iteration *)
        right.
        apply c_pair_in_c_seq_l.
        assert (hx:
          NExp.NBin NMinus (from_pure e2) (NExp.NNum 1) =
          from_pure (NBin NMinus e2 (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eapply c_pair_in_subst; eauto using r_last_to_eq.
      }
      (* All but last iteration *)
      left.
      eapply i_pair_in_for_2 with (n:=S n). {
        invc hp.
        destruct n2. {
          lia.
        }
        rename_hyp (NStep _ (S n2)) as hn.
        apply n_step_inv_dec in hn.
        apply r_pick_def with (n1:=S n1) (n2:=S (S n2)); auto.
        - assert (r2: S n1 = 1 + n1). {
            lia.
          }
          rewrite r2.
          apply n_step_add; auto using n_step_num.
        - lia.
      }
      rewrite n_seq_subst.
      apply i_pair_in_n_seq_l.
      rewrite i_subst_subst_eq_1.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      assert (hx:
        NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
        from_pure (NBin NMinus (NNum (S n)) (NNum 1))
      ) by reflexivity.
      rewrite hx.
      eapply c_pair_in_subst; eauto using n_step_num.
      apply n_step_bin_eq with (n1:=S n) (n2:=1); eauto using n_step_num with *.
    - (* i_pair_in_for_2 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      simpl.
      (* At this point we do not know what n refers to. Is n
         in the last iteration (and at the dangling bit),
         or is n inside the for loop. *)
      apply r_pick_inv_last in H.
      destruct H as [H|H]. {
        right.
        apply c_pair_in_c_seq_r.
        assert (hx:
          NExp.NBin NMinus (NExp.from_pure e2) (NExp.NNum 1) =
          from_pure (NBin NMinus e2 (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eapply c_pair_in_subst; eauto using r_last_to_eq.
      }
      left.
      (* In this case we know that n is inside the loop *)
      eapply i_pair_in_for_2 with (n:=S n). {
        invc H.
        destruct n2. {
          lia.
        }
        rename_hyp (NStep _ (S n2)) as hn.
        apply n_step_inv_dec in hn.
        apply r_pick_def with (n1:=S n1) (n2:=S (S n2)); auto.
        - assert (r2: S n1 = 1 + n1). {
            lia.
          }
          rewrite r2.
          apply n_step_add; auto using n_step_num.
        - lia.
      }
      rewrite n_seq_subst.
      apply i_pair_in_n_seq_r.
      rewrite n_seq_subst.
      apply i_pair_in_n_seq_l.
      rewrite i_subst_subst_eq_1.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      assert (hx:
        NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
        from_pure (NBin NMinus (NNum (S n)) (NNum 1))
      ) by reflexivity.
      rewrite hx.
      apply c_pair_in_subst with (e1:=e) (n:=n); auto.
      auto using n_step_succ_minus_one.
    - (* i_pair_in_for_3 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct p as (a1, a2).
      simpl in *.
      invc Hc.
      assert (Hc: WLang.CanRun (w_subst x (NNum n) P)) by auto.
      apply r_pick_inv_last in H.
      destruct H as [H|H]. {
        right.
        apply r_last_to_eq in H.
        apply c_pair_in_def;
          intuition;
          rename_hyp (ILast _ _) as hl
        .
        + apply ULang.c_in_c_seq_l.
          assert (hx:
            NExp.NBin NMinus (NExp.from_pure e2) (NExp.NNum 1) =
            from_pure (NBin NMinus e2 (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eauto using i_last_to_c_in_1.
        + apply ULang.c_in_c_seq_r.
          assert (hx:
            NExp.NBin NMinus (NExp.from_pure e2) (NExp.NNum 1) =
            from_pure (NBin NMinus e2 (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply ULang.c_in_subst; eauto.
        + apply ULang.c_in_c_seq_r.
          assert (hx:
            NExp.NBin NMinus (NExp.from_pure e2) (NExp.NNum 1) =
            from_pure (NBin NMinus e2 (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply ULang.c_in_subst; eauto.
        + apply ULang.c_in_c_seq_l.
          assert (hx:
            NExp.NBin NMinus (NExp.from_pure e2) (NExp.NNum 1) =
            from_pure (NBin NMinus e2 (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eauto using i_last_to_c_in_1.
      }
      left.
      apply i_pair_in_for_2 with (n:=S n). {
        eauto using Pure.RExp.r_pick_advance.
      }
      rewrite subst_n_seq.
      rewrite subst_n_seq.
      rewrite <- n_seq_c_seq.
      apply i_pair_in_n_seq_l.
      rewrite i_subst_subst_eq_1.
      rewrite i_subst_subst_eq_1.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      apply c_pair_in_def; intuition.
      + assert (hx:
           NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
          from_pure (NBin NMinus (NNum (S n)) (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eauto using ULang.c_in_c_seq_l, i_last_to_c_in_1, n_step_succ_minus_one.
      + apply ULang.c_in_c_seq_r.
        assert (hx:
           NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
          from_pure (NBin NMinus (NNum (S n)) (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eapply ULang.c_in_subst; eauto using n_step_succ_minus_one.
      + apply ULang.c_in_c_seq_r.
        assert (hx:
           NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
          from_pure (NBin NMinus (NNum (S n)) (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eapply ULang.c_in_subst; eauto using n_step_succ_minus_one.
      + assert (hx:
           NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
          from_pure (NBin NMinus (NNum (S n)) (NNum 1))
        ) by reflexivity.
        rewrite hx.
        eauto using ULang.c_in_c_seq_l, i_last_to_c_in_1, n_step_succ_minus_one.
    - (* i_pair_in_for_first_1 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct p as (a1, a2).
      simpl in *.
      intuition; left.
      auto using i_pair_in_for_1, i_pair_in_n_seq_l.
    - (* i_pair_in_for_first_2 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct p as (a1, a2).
      simpl in *.
      left.
      apply i_pair_in_for_1.
      invc Hc.
      assert (WLang.CanRun (w_subst x e P)). {
        assert (WLang.CanRun (w_subst x (NNum n) P)) by auto using r_first_to_pick.
        eauto using can_run_subst, n_step_num.
      }
      intuition.
      + apply i_pair_in_n_seq_1; auto.
        assert (NStep e1 n) by eauto using r_first_to_eq.
        eauto using i_first_to_c_in_1.
      + apply i_pair_in_n_seq_2; auto.
        assert (NStep e1 n) by eauto using r_first_to_eq.
        eauto using i_first_to_c_in_1.
    - (* i_pair_in_for_mid_1 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct p as (a1, a2).
      simpl in *.
      invc Hc.
      left.
      apply i_pair_in_for_2 with (n:=S n). {
        auto using r_pick2_advance.
      }
      rewrite subst_n_seq.
      rewrite subst_n_seq.
      rewrite i_subst_subst_eq_1.
      rewrite i_subst_subst_eq_1.
      apply i_pair_in_n_seq_r.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      assert (WLang.CanRun (w_subst x e' P)). {
        assert (WLang.CanRun (w_subst x (NNum (S n)) P)) by eauto using r_pick2_to_pick_r.
        eapply can_run_subst; eauto using n_step_num.
      }
      intuition.
      + apply i_pair_in_n_seq_1.
        * assert (hx:
            NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
            from_pure (NBin NMinus (NNum (S n)) (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply c_in_subst with (v:=e); eauto using n_step_succ_minus_one. 
        * eapply i_first_to_c_in_1; eauto using n_step_num.
      + apply i_pair_in_n_seq_2.
        * eapply i_first_to_c_in_1; eauto using n_step_num.
        * assert (hx:
            NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
            from_pure (NBin NMinus (NNum (S n)) (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply c_in_subst with (v:=e); eauto using n_step_succ_minus_one. 
    - (* i_pair_in_for_mid_2 *)
      destruct r as (e1, e2).
      destruct (align P) as (P_x, c_x) eqn:r1.
      destruct Hd as (Hd1, (Hd2, (Hd3, (Hd4, Hd5)))).
      destruct p as (a1, a2).
      simpl in *.
      invc Hc.
      left.
      apply i_pair_in_for_2 with (n:=S n). {
        auto using r_pick2_advance.
      }
      rewrite subst_n_seq.
      rewrite subst_n_seq.
      rewrite i_subst_subst_eq_1.
      rewrite i_subst_subst_eq_1.
      simpl.
      destruct (Set_VAR.MF.eq_dec x x) as [_|?]; try contradiction.
      assert (WLang.CanRun (w_subst x (NNum n) P)) by eauto using r_pick2_to_pick.
      assert (WLang.CanRun (w_subst x e' P)). {
        assert (WLang.CanRun (w_subst x (NNum (S n)) P)) by eauto using r_pick2_to_pick_r.
        eapply can_run_subst; eauto using n_step_num.
      }
      intuition.
      + apply i_pair_in_n_seq_1.
        * assert (hx:
            NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
            from_pure (NBin NMinus (NNum (S n)) (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply i_last_to_c_in_1 with (e:=e); eauto using n_step_succ_minus_one.
        * apply i_first_n_seq_r.
          eapply i_first_to_c_in_1; eauto using n_step_num.
      + apply i_pair_in_n_seq_2.
        * apply i_first_n_seq_r.
          eapply i_first_to_c_in_1; eauto using n_step_num.
        * assert (hx:
            NExp.NBin NMinus (NExp.NNum (S n)) (NExp.NNum 1) =
            from_pure (NBin NMinus (NNum (S n)) (NNum 1))
          ) by reflexivity.
          rewrite hx.
          eapply i_last_to_c_in_1 with (e:=e); eauto using n_step_succ_minus_one.
  Qed.

  Corollary drf_2:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    DRF (align P) ->
    WLang.DRF P.
  Proof.
    unfold DRF, WLang.DRF.
    intros.
    auto using in_2.
  Qed.

  Corollary drf:
    forall P,
    WLang.CanRun P ->
    WLang.Distinct P ->
    DRF (align P) <-> WLang.DRF P.
  Proof.
    intros.
    split; auto using drf_1, drf_2.
  Qed.

  Lemma var_inv_seq:
    forall x c P,
    Var x (n_seq c P) ->
    ULang.Var x c \/ Var x P.
  Proof.
    induction P; simpl in *; intros.
    - auto using ULang.var_inv_c_seq.
    - intuition.
    - intuition.
  Qed.

  Lemma occurs_inv_seq:
    forall x c P,
    Occurs x (n_seq c P) ->
    ULang.Occurs x c \/ Occurs x P.
  Proof.
    induction P; simpl in *; intros.
    - auto using occurs_inv_c_seq.
    - intuition.
    - intuition.
  Qed.

  Lemma distinct_seq:
    forall c P,
    Distinct P ->
    ULang.Distinct c ->
    Distinct (n_seq c P).
  Proof.
    induction P; simpl; intros; auto.
    - intuition.
    - intuition.
  Qed.

  Lemma distinct_w_to_a:
    forall P,
    WLang.Distinct P ->
    PDistinct (align P).
  Proof.
    intros.
    induction P; simpl in *; auto.
    - destruct (align P1) as (P1', c1).
      destruct (align P2) as (P2', c2).
      simpl in *.
      intuition.
      auto using distinct_seq.
    - destruct (align P) as (Px,cx) eqn:hr.
      destruct r as (e1, e2).
      simpl in *.
      destruct H as (ha, (hb, (hc, (hd, he)))).
      apply IHP in hd.
      destruct hd as (hd1, hd2); clear IHP.
      repeat split.
      + apply distinct_seq; auto using distinct_subst.
      + intros N.
        apply var_inv_seq in N.
        destruct N as [N|N]. {
          contradict hb.
          apply var_inv_align.
          rewrite hr.
          simpl.
          apply ULang.var_inv_subst in N.
          auto.
        }
        apply var_inv_seq in N.
        destruct N as [N|N]. {
          contradict hc.
          eauto using ULang.var_inv_subst.
        }
        contradict hb.
        apply var_inv_align.
        rewrite hr.
        simpl.
        auto.
      + apply distinct_seq. {
          apply distinct_seq; auto.
          auto using ULang.distinct_subst.
        }
        auto using ULang.distinct_subst.
      + apply distinct_c_seq; auto using ULang.distinct_subst.
  Qed.

End Props.