Require Import AExp.
Require Import Tasks.
Require Import ALang.
Require Import RExp.
Require Import NExp.
Require Import Var.
Require Import Tictac.
Require ULang.
Require Sequentialize.
Require Import Coq.Lists.List.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Inductive phase :=
  | Phase: ULang.inst -> phase
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
    | Phase c => Phase (ULang.i_subst x v c)
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
    ULang.CPairIn p c ->
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

  Inductive PhasePairIn (p:access_val * access_val) : phase -> n_inst -> Prop :=
  | ph_pair_in_sync:
    forall c,
    ULang.CPairIn p c ->
    PhasePairIn p (Phase c) (NSync c)
  | ph_pair_in_seq_l:
    forall ph P Q,
    PhasePairIn p ph P ->
    PhasePairIn p ph (NSeq P Q)
  | ph_pair_in_seq_r:
    forall ph P Q,
    PhasePairIn p ph Q ->
    PhasePairIn p ph (NSeq P Q)
  | p_pair_in_for_1:
    forall x r P Q ph,
    PhasePairIn p ph P ->
    PhasePairIn p ph (NFor P x r Q)
  | p_pair_in_for_2:
    forall x r P Q ph n,
    RPick r n ->
    PhasePairIn p (ph_subst x (NNum n) ph) (subst x (NNum n) Q) ->
    PhasePairIn p (Decl x r ph) (NFor P x r Q).

  Lemma in_phases_2:
    forall p P ph,
    PhasePairIn p ph P ->
    IPairIn p P.
  Proof.
    intros.
    induction H;
      eauto using
        i_pair_in_seq_l,
        i_pair_in_seq_r,
        i_pair_in_for_1,
        i_pair_in_sync,
        i_pair_in_for_2.
  Qed.

  Lemma in_1:
    forall p P,
    ALang.PPairIn p P ->
    Distinct (fst P) ->
    InPhases p (split P).
  Proof.
    intros.
    destruct P as (a, u).
    simpl in *.
    unfold InPhases.
    destruct H as [H|H]. {
      apply in_phases_1 in H; auto.
      destruct H as (ph, (Ha, Hb)).
      eauto using in_cons.
    }
    exists (Phase u).
    simpl.
    split; auto.
    auto using p_pair_in_phase.
  Qed.

  Theorem drf_1:
    forall P,
    DRF (split P) ->
    Distinct (fst P) ->
    ALang.DRF P.
  Proof.
    unfold DRF, ALang.DRF.
    intros.
    rename_hyp (ALang.PPairIn _ _) as Hi.
    apply in_1 in Hi; auto.
    destruct Hi as (ph, (Hi, Hp)).
    eauto.
  Qed.

  Inductive CanRun: n_inst -> Prop :=
  | can_run_sync:
    forall c,
    CanRun (NSync c)
  | can_run_seq:
    forall P Q,
    CanRun P ->
    CanRun Q ->
    CanRun (NSeq P Q)
  | can_run_for:
    forall P Q x r,
    CanRun P ->
    (forall n, RPick r n -> CanRun (subst x (NNum n) Q)) ->
    CanRun (NFor P x r Q).

  Lemma in_ph_subst:
    forall P ph,
    In ph (a_split P) ->
    forall x n,
    ~ Var x P ->
    In (ph_subst x (NNum n) ph) (a_split (subst x (NNum n) P)).
  Proof.
    induction P; intros.
    - simpl in *.
      intuition.
      subst.
      auto.
    - simpl in *.
      rewrite in_app_iff in *.
      destruct H as [H|H]. {
        left.
        apply IHP1; auto.
      }
      right.
      apply IHP2; auto.
    - simpl in *.
      rename v into y.
      intuition.
      destruct (Set_VAR.MF.eq_dec x y). {
        contradiction.
      }
      rewrite in_app_iff in *.
      destruct H as [H|H]. {
        eauto.
      }
      right.
      rewrite in_map_iff in *.
      destruct H as (ph', (?, Hi)).
      subst.
      simpl.
      destruct (Set_VAR.MF.eq_dec x y). {
        contradiction.
      }
      exists  (ph_subst x (NNum n) ph').
      split; auto.
  Qed.

  Lemma i_pair_in_ph:
    forall P,
    CanRun P ->
    Distinct P ->
    forall ph,
    In ph (a_split P) ->
    forall p,
    PPairIn p ph ->
    IPairIn p P.
  Proof.
    intros P H.
    induction H; intros Hd ph Hi p Hp; simpl in *.
    - destruct Hi; try (intuition; fail).
      subst.
      invc Hp.
      auto using i_pair_in_sync.
    - apply in_app_iff in Hi.
      destruct Hd as (Hd1, Hd2).
      destruct Hi as [Hi|Hi]. {
        eauto using i_pair_in_seq_l.
      }
      eauto using i_pair_in_seq_r.
    - simpl in *.
      destruct Hd as (Hd1, (Hd2, Hd3)).
      rewrite in_app_iff in Hi.
      destruct Hi as [Hi|Hi]. {
        eapply IHCanRun in Hi; eauto using i_pair_in_for_1.
      }
      apply in_map_iff in Hi.
      destruct Hi as (ph', (?, Hi)).
      subst.
      invc Hp.
      apply H1 with (n:=n) in H6; auto.
      + eapply i_pair_in_for_2; eauto.
      + auto using distinct_subst.
      + apply in_ph_subst; auto.
  Qed.

  Lemma in_2:
    forall p P,
    InPhases p (split P) ->
    Distinct (fst P) ->
    CanRun (fst P) ->
    ALang.PPairIn p P.
  Proof.
    intros.
    destruct P as (a, u).
    simpl in *.
    destruct H as (ph, (Hi, Hp)).
    destruct Hi as [Hi|Hi]. {
      subst.
      invc Hp.
      auto.
    }
    left.
    eapply i_pair_in_ph; eauto.
  Qed.

  Theorem drf_2:
    forall P,
    CanRun (fst P) ->
    Distinct (fst P) ->
    ALang.DRF P ->
    DRF (split P).
  Proof.
    unfold DRF, ALang.DRF.
    intros.
    apply H1.
    eapply in_2; auto.
    eexists.
    eauto.
  Qed.

  Theorem drf:
    forall P,
    CanRun (fst P) ->
    Distinct (fst P) ->
    ALang.DRF P <-> DRF (split P).
  Proof.
    split; intros.
    + apply drf_2; auto.
    + apply drf_1; auto.
  Qed.

End Defs.