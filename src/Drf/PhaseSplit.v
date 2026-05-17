From Faial.Core Require Import Tasks.
Require Import ALang.

From Faial.Expr Require Import Pure.R.Exp.

From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Expr Require Import SIMT.N.Exp.

From Faial.Core Require Import Var.
From Faial.Core Require Import Tictac.
From Faial.Drf.U Require Import Lang Subst Free Run IIn CIn CSeq Distinct Notations.
Require Sequentialize.
From Stdlib Require Import Lists.List.
From Faial.Core Require Import AVal.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.

  Inductive phase :=
  | Phase: Lang.t -> phase
  | Decl: var -> Pure.R.Exp.range -> phase -> phase.

  Fixpoint Var x p :=
    match p with
    | Phase u => Var.t x u
    | Decl y _ p => x = y \/ Var x p
    end.

  Fixpoint Occurs x p :=
    match p with
    | Phase u => Occurs.t x u
    | Decl y _ p => x = y \/ Occurs x p
    end.

  Fixpoint Distinct p :=
  match p with
  | Phase u => True
  | Decl x r p => ~ Var x p /\ Distinct p
  end.

  Fixpoint a_split (n:n_inst) : list phase :=
  match n with
  | NSync c => [Phase c]
  | NSeq n1 n2 => a_split n1 ++ a_split n2
  | NFor n1 x r n2 => a_split n1 ++ (List.map (Decl x r) (a_split n2))
  end.

  Definition split (P:p_inst) :=
    let (P, c) := P in
    a_split P ++ [Phase c].

  Fixpoint ph_subst x (v:Pure.N.Exp.nexp) (P:phase) : phase :=
    match P with
    | Phase c => Phase (Subst.f x (from_pure v) c)
    | Decl y r P =>
      let P' := if VAR.eq_dec x y
        then P
        else ph_subst x v P
      in
      Decl y (Pure.R.Exp.r_subst x v r) P'
    end.

  Lemma var_inv_subst:
    forall x y v ph,
    Var x (ph_subst y v ph) ->
    Var x ph.
  Proof.
    induction ph; simpl in *; intros.
    - eauto using Var.inv_subst.
    - intuition.
      destruct (Set_VAR.MF.eq_dec y v0). {
        subst.
        intuition.
      }
      intuition.
  Qed.

  Lemma not_var_subst:
    forall x y v ph,
    ~ Var x ph ->
    ~ Var x (ph_subst y v ph).
  Proof.
    intros.
    intros N.
    apply var_inv_subst in N.
    contradiction.
  Qed.

  Lemma occurs_inv_subst:
    forall x y v ph,
    Occurs x (ph_subst y v ph) ->
    Pure.N.Exp.NFree x v \/ Occurs x ph.
  Proof.
    induction ph; simpl in *; intros.
    - rename_hyp (Occurs.t _ _) as ho.
      apply Occurs.inv_subst in ho.
      intuition.
      rewrite n_free_from_pure in *.
      intuition.
    - intuition.
      destruct (Set_VAR.MF.eq_dec y v0). {
        subst.
        intuition.
      }
      intuition.
  Qed.

  Lemma not_occurs_subst:
    forall y ph x v,
    ~ Pure.N.Exp.NFree x v ->
    ~ Occurs x ph ->
    ~ Occurs x (ph_subst y v ph).
  Proof.
    intros.
    intros N.
    apply occurs_inv_subst in N; auto.
    intuition.
  Qed.

  Lemma distinct_subst:
    forall ph,
    Distinct ph ->
    forall x v,
    Distinct (ph_subst x v ph).
  Proof.
    induction ph; simpl; intros; auto.
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
      intuition.
    }
    destruct H as (Ha, Hb).
    split. {
      auto using not_var_subst.
    }
    eauto.
  Qed.

  Inductive PPairIn (p:access_val * access_val) : phase -> Prop :=
  | p_pair_in_phase:
    forall c,
    CIn.CPairIn p c ->
    PPairIn p (Phase c)
  | p_pair_in_decl:
    forall x r P n,
    Pure.R.Exp.RPick r n ->
    PPairIn p (ph_subst x (Pure.N.Exp.NNum n) P) ->
    PPairIn p (Decl x r P).

  Definition DRF (l:list phase) :=
    forall P,
    List.In P l ->
    forall p,
    PPairIn p P ->
    Safe (fst p) (snd p).


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
    ~ ALang.Var x P -> 
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
    ALang.Distinct P ->
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
    - assert (Hd: ALang.Distinct (subst x (Pure.N.Exp.NNum n) j) ). {
        auto using ALang.distinct_subst.
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

  Lemma in_1:
    forall p P,
    ALang.PPairIn p P ->
    ALang.Distinct (fst P) ->
    InPhases p (split P).
  Proof.
    intros.
    destruct P as (a, u).
    simpl in *.
    unfold InPhases.
    destruct H as [H|H]. {
      apply in_phases_1 in H; auto.
      destruct H as (ph, (Ha, Hb)).
      exists ph.
      rewrite in_app_iff.
      intuition.
    }
    exists (Phase u).
    rewrite in_app_iff.
    simpl.
    split; auto.
    auto using p_pair_in_phase.
  Qed.

  Theorem drf_1:
    forall P,
    DRF (split P) ->
    ALang.Distinct (fst P) ->
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
    (forall n, RPick r n -> CanRun (subst x (Pure.N.Exp.NNum n) Q)) ->
    CanRun (NFor P x r Q).
(*
  Definition ACanRun (p:p_inst) : Prop :=
    let (a, u) := p in
    CanRun a.
*)
  Lemma can_run_n_seq_1:
    forall u a,
    CanRun (n_seq u a) ->
    CanRun a.
  Proof.
    induction a; intros; simpl in *.
    - constructor.
    - inversion_clear H.
      constructor; auto.
    - inversion_clear H.
      constructor; auto.
  Qed.

  Lemma can_run_n_seq_2:
    forall u a,
    CanRun a ->
    CanRun (n_seq u a).
  Proof.
    induction a; intros; simpl in *.
    - constructor.
    - inversion_clear H.
      constructor; auto.
    - inversion_clear H.
      constructor; auto.
  Qed.

  Lemma can_run_n_seq_iff:
    forall u a,
    CanRun (n_seq u a) <-> CanRun a.
  Proof.
    split; intros; eauto using can_run_n_seq_1, can_run_n_seq_2.
  Qed.


  Lemma can_run_subst:
    forall a e1 e2 n x,
    Pure.N.Exp.NStep e1 n ->
    Pure.N.Exp.NStep e2 n ->
    CanRun (ALang.subst x e1 a) ->
    CanRun (ALang.subst x e2 a).
  Proof.
    intros.
    remember (subst _ _ _) as p.
    generalize dependent e1.
    generalize dependent x.
    generalize dependent e2.
    generalize dependent n.
    generalize dependent a.
    induction H1;
      intros a n e2 e2_n y e1 e1_n r_eq;
      destruct a;
      simpl in r_eq;
      inversion r_eq;
      subst;
      simpl;
      constructor;
      eauto;
      clear r_eq.
    intros m r_m.
    simpl.
    destruct (Set_VAR.MF.eq_dec y v) as [y_v|y_v]. {
      subst.
      eapply r_pick_subst in r_m; eauto.
    }
    clear IHCanRun.
    eapply r_pick_subst in r_m; eauto.
    clear H.
    assert (hc: CanRun (subst y e2 (subst v (Pure.N.Exp.NNum m) a2))). {
      eapply H0; eauto.
      rewrite ALang.subst_subst_neq; eauto using Pure.N.Exp.n_step_to_not_free.
    }
    rewrite ALang.subst_subst_neq; eauto using Pure.N.Exp.n_step_to_not_free.
  Qed.

  Lemma in_ph_subst:
    forall P ph,
    In ph (a_split P) ->
    forall x n,
    ~ ALang.Var x P ->
    In (ph_subst x (Pure.N.Exp.NNum n) ph) (a_split (subst x (Pure.N.Exp.NNum n) P)).
  Proof.
    Import Pure.N.Exp.
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
    ALang.Distinct P ->
    forall ph,
    In ph (a_split P) ->
    forall p,
    PPairIn p ph ->
    IPairIn p P.
  Proof.
    intros P H.
    induction H; intros Hd ph Hi p Hp; simpl in *.
    - intuition.
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
      + auto using ALang.distinct_subst.
      + apply in_ph_subst; auto.
  Qed.

  Lemma in_phases_app_or:
    forall p l r,
    InPhases p (l ++ r) ->
    InPhases p l \/ InPhases p r.
  Proof.
    intros.
    remember (l ++ r) as i.
    generalize dependent l.
    generalize dependent r.
    induction H.
    destruct H as (Ha, Hb).
    generalize dependent i.
    induction Hb; intros i hi r1 l1 i_eq; subst. {
      rewrite in_app_iff in *.
      intuition.
      - left.
        exists (Phase c).
        intuition.
        constructor.
        assumption.
      - right.
        exists (Phase c).
        intuition.
        constructor.
        assumption.
    }
    rewrite in_app_iff in *.
    destruct hi as [hi|hi]. {
      left.
      eexists; split; eauto.
      apply p_pair_in_decl with (n:=n); auto.
    }
    right.
    eexists; split; eauto.
    apply p_pair_in_decl with (n:=n); auto.
  Qed.

  Lemma in_2:
    forall p P,
    InPhases p (split P) ->
    ALang.Distinct (fst P) ->
    CanRun (fst P) ->
    ALang.PPairIn p P.
  Proof.
    intros.
    destruct P as (a, u).
    simpl in *.
    destruct H as (ph, (Hi, Hp)).
    apply in_app_iff in Hi.
    destruct Hi as [Hi|Hi]. {
      left.
      eapply i_pair_in_ph; eauto.
    }
    subst.
    simpl in Hi.
    intuition.
    subst.
    invc Hp; auto.
  Qed.

  Theorem drf_2:
    forall P,
    CanRun (fst P) ->
    ALang.Distinct (fst P) ->
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
    ALang.Distinct (fst P) ->
    ALang.DRF P <-> DRF (split P).
  Proof.
    split; intros.
    + apply drf_2; auto.
    + apply drf_1; auto.
  Qed.

End Defs.