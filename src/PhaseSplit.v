Require Import AccExp.
Require Import Tasks.
Require Import AlignLang.
Require Import RExp.
Require Import NExp.
Require Import Var.
Require Import Tictac.
Require Conc.

Require Import Coq.Lists.List.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Inductive phase :=
  | Phase: Conc.inst -> phase
  | Decl: var -> range -> phase -> phase.

  Fixpoint a_split (n:n_inst) : list phase :=
  match n with
  | NSync c => [Phase c]
  | NSeq n1 n2 => a_split n1 ++ a_split n2
  | NFor n1 x r n2 => a_split n1 ++ (List.map (Decl x r) (a_split n2))
  end.

  Definition split (P:p_inst) :=
    let (P, c) := P in
    Phase c :: a_split P. 

  Fixpoint ph_subst x (v:nexp) (P:phase) : phase :=
    match P with
    | Phase c => Phase (Conc.i_subst x v c)
    | Decl y r P =>
      let P' := if VAR.eq_dec x y
        then P
        else ph_subst x v P
      in
      Decl y (r_subst x v r) P'
    end.

  Inductive PPairIn (p:access_val * access_val) : phase -> Prop :=
  | p_pair_in_phase:
    forall c,
    Conc.CPairIn p c ->
    PPairIn p (Phase c)
  | p_pair_in_decl:
    forall x r P n,
    RPick r n ->
    PPairIn p (ph_subst x (NNum n) P) ->
    PPairIn p (Decl x r P).

  Definition DRF (l:list phase) :=
    forall P,
    List.In P l ->
    forall p,
    PPairIn p P ->
    access_safe (fst p) (snd p).


  Definition InPhases p (l:list phase) :=
    exists ph, List.In ph l /\ PPairIn p ph. 

  Inductive ASplit: n_inst -> phase -> Prop :=
  | a_split_phase:
    forall c,
    ASplit (NSync c) (Phase c)
  | a_split_seq_l:
    forall ph P Q,
    ASplit P ph ->
    ASplit (NSeq P Q) ph
  | a_split_seq_r:
    forall ph P Q,
    ASplit Q ph ->
    ASplit (NSeq P Q) ph
  | a_split_for_1:
    forall P Q x r ph,
    ASplit P ph ->
    ASplit (NFor P x r Q) ph
  | a_split_for_2:
    forall P Q x r ph,
    ASplit Q ph -> 
    ASplit (NFor P x r Q) (Decl x r ph).

  Lemma map_subst_reorder:
    forall x v y r l,
    x <> y ->
    map (ph_subst x v) (map (Decl y r) l) = 
    map (Decl y (r_subst x v r)) (map (ph_subst x v) l).
  Proof.
    induction l; intros.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHl; auto.
      destruct (Set_VAR.MF.eq_dec x y) as [?|_]; try contradiction.
      reflexivity.
  Qed.

  Lemma a_split_subst_rw:
    forall x v P,
    ~ Var x P -> 
    a_split (subst x v P) = List.map (ph_subst x v) (a_split P).
  Proof.
    induction P; intros; simpl; auto.
    - rewrite map_app.
      simpl in *.
      rewrite IHP2; auto.
      rewrite IHP1; auto.
    - rename v0 into y.
      rewrite map_app.
      simpl in *.
      rewrite IHP1; auto.
      destruct (Set_VAR.MF.eq_dec x y). {
        subst.
        intuition.
      }
      rewrite IHP2; auto.
      rewrite map_subst_reorder; auto.
  Qed.

  Lemma in_phases_1:
    forall P p,
    IPairIn p P ->
    Distinct P ->
    InPhases p (a_split P).
  Proof.
    intros P p H.
    induction H; intros; unfold InPhases; simpl in *; intuition;
      try rename_hyp (InPhases _ _) as Hi.
    - exists (Phase c).
      intuition.
      auto using p_pair_in_phase.
    - destruct Hi as (ph, (Ha, Hb)).
      eexists.
      rewrite in_app_iff.
      eauto.
    - destruct Hi as (ph, (Ha, Hb)).
      eexists.
      rewrite in_app_iff.
      eauto.
    - destruct Hi as (ph, (Ha, Hb)).
      eexists.
      rewrite in_app_iff.
      eauto.
    - assert (Hd: Distinct (subst x (NNum n) j) ). {
        auto using distinct_subst.
      }
      apply IHIPairIn in Hd.
      destruct Hd as (ph, (Ha, Hb)).
      rewrite a_split_subst_rw in Ha; auto.
      rewrite in_map_iff in Ha.
      destruct Ha as (ph', (?, Ha)).
      subst.
      exists (Decl x r ph').
      split. {
        rewrite in_app_iff.
        right.
        rewrite in_map_iff.
        exists ph'.
        auto.
      }
      apply p_pair_in_decl with (n:=n); auto.
  Qed.

  Lemma in_ph_split:
    forall P p ph,
    PPairIn p ph ->
    ASplit P ph ->
    IPairIn p P.
  Proof.
    induction P; intros.
    - admit.
    - admit.
    - invc H0. {
        admit.
      }
      invc H.
      assert (IHP2 
    intros p ph H.
    induction H; intros P' Hi. {
      admit.
    }
    destruct P'.
    - invc Hi.
    - invc Hi.
      rewr

    intros P ph H.
    induction H; intros.
    - invc H.
      constructor.
      assumption.
    - auto using i_pair_in_seq_l.
    - auto using i_pair_in_seq_r.
    - auto using i_pair_in_for_1.
    - invc H0.
      eapply i_pair_in_for_2; eauto.
      invc 	H3.
  Qed.

(*
  Lemma in_ph_split:
    forall P ph,
    In ph (a_split P) ->
    forall p,
    PPairIn p ph ->
    IPairIn p P.
*)
(*
  Lemma in_ph_split:
    forall p P,
    InPhases p (a_split P) ->
    IPairIn p P.
  Proof.
    intros.
    remember (a_split _) as l.
    generalize dependent P.
    destruct H as (ph, (Hl, Hi)).
    generalize dependent p.
    generalize dependent ph.
    induction l; intros. {
      contradiction.
    }
    simpl in *.
    destruct P.
    - simpl in *.
      invc Heql; subst.
      destruct Hl; try contradiction.
      subst.
      clear IHl.
      admit.
    - destruct Hl. {
        simpl in *.
        subst.
    destruc
    induction P; simpl; intros H p Hi.
    - destruct H as [H|?]; try contradiction.
      subst.
      invc Hi.
      constructor.
      assumption.
    - apply in_app_iff in H.
      destruct H as [H|H]. {
        auto using i_pair_in_seq_l.
      }
      auto using i_pair_in_seq_r.
    - apply in_app_iff in H.
      destruct H as [H|H]. {
        auto using i_pair_in_for_1.
      }
      clear IHP1.
      apply in_map_iff in H.
      destruct H as (ph', (Hd, Hi2)).
      subst.
      invc Hi.
      eapply i_pair_in_for_2; eauto.
  Qed.
*)
  Theorem drf_1:
    forall P,
    AlignLang.DRF P ->
    DRF (split P).
  Proof.
    intros.
    unfold DRF.
    intros.
    destruct P as (P, c).
    simpl in *.
    destruct H0. {
      subst.
      invc H1.
      unfold AlignLang.DRF in *.
      simpl in *.
      apply H.
      auto.
    }
    apply H.
    simpl.
    left.
    clear H.
    rename P0 into ph.
    unfold AlignLang.DRF in H.
  Qed.

End Defs.