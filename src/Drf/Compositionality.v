From Faial.Expr Require Import SIMT.A.Exp.
From Faial.Core Require Import Tasks.
From Faial.Core Require Import Var.
Require Import WLang.
From Faial.Drf.U Require Import Lang Subst Free Run IIn CIn CSeq Distinct Notations.
From Faial.Expr Require Import SIMT.N.Exp.
From Faial.Core Require Import Tictac.
Require Import ALang.
From Faial.Core Require Import Util.
From Faial.Expr Require Import SIMT.R.Exp.
From Stdlib Require Import Lia.

Section Props.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Inductive ctxt :=
  | Hole: ctxt
  | Sync: Lang.t -> ctxt
  | SeqL: ctxt -> n_inst -> ctxt
  | SeqR: n_inst -> ctxt -> ctxt
  | ForL: ctxt -> var -> range -> n_inst -> ctxt
  | ForR: n_inst -> var -> range -> ctxt -> ctxt.

  Fixpoint subst x v i :=
    match i with
    | Hole => Hole
    | Sync u => Sync (Subst.f x v u)
    | SeqL c q => SeqL (subst x v c) (ALang.subst x v q)
    | SeqR q c => SeqR (ALang.subst x v q) (subst x v c)
    | ForL c y r q =>
      let q' := if VAR.eq_dec x y
        then q
        else ALang.subst x v q
      in
      ForL (subst x v c) y (r_subst x v r) q'
    | ForR q y r c =>
      let c' := if VAR.eq_dec x y
        then c
        else subst x v c
      in
      ForR (ALang.subst x v q) y (r_subst x v r) c'
    end.
  
  Fixpoint plug (c:ctxt) (p:n_inst) : n_inst :=
    match c with
    | Hole => p
    | Sync u => NSync u
    | SeqL c q => NSeq (plug c p) q
    | SeqR q c => NSeq q (plug c p)
    | ForL c v r q => NFor (plug c p) v r q
    | ForR q v r c => NFor q v r (plug c p)
    end.

  Definition DRF (P:n_inst) :=
    forall p,
    IPairIn p P ->
    access_safe (fst p) (snd p).

  Definition UDRF (P:Lang.t) :=
    forall p,
    CIn.CPairIn p P ->
    access_safe (fst p) (snd p).

  Inductive IDRF : n_inst -> Prop :=
  | idrf_sync: forall u,
      UDRF u -> IDRF (NSync u)
  | idrf_seq: forall p q,
      IDRF p -> IDRF q -> IDRF (NSeq p q)
  | idrf_for: forall p q r x,
      IDRF p ->
      (forall n, RPick r n -> IDRF (ALang.subst x (NNum n) q)) ->
      IDRF (NFor p x r q).

  Inductive CDRF : ctxt -> Prop :=
  | cdrf_hole: CDRF Hole 
  | cdrf_sync: forall u,
    UDRF u -> CDRF (Sync u)
  | cdrf_seq_l: forall c p,
    CDRF c ->
    IDRF p ->
    CDRF (SeqL c p)
  | cdrf_seq_r: forall c p,
    CDRF c ->
    IDRF p ->
    CDRF (SeqR p c)
  | cdrf_for_l: forall c p r x,
    CDRF c ->
    (forall n, RPick r n -> IDRF (ALang.subst x (NNum n) p)) ->
    CDRF (ForL c x r p)
  | cdrf_for_r: forall p c r x,
    IDRF p ->
    (forall n, RPick r n -> CDRF (subst x (NNum n) c)) ->
    CDRF (ForR p x r c).


  Fixpoint Var x c :=
    match c with
    | Hole => False
    | Sync u => Free.Var x u
    | SeqL c p => Var x c \/ ALang.Var x p 
    | SeqR p c => ALang.Var x p \/ Var x c
    | ForL c y r n => Var x c \/ x = y \/ ALang.Var x n
    | ForR p y r c => ALang.Var x p \/ x = y \/ Var x c
    end.

  Fixpoint Free x (p:n_inst) :=
    match p with
    | NSync u => Free.Free x u
    | NSeq p q => Free x p \/ Free x q
    | NFor p y r q => Free x p \/ RFree x r \/ (x <> y /\ Free x q)
    end.

  Definition Closed p := forall x, x <> TID -> ~ Free x p.

  Lemma subst_not_free:
    forall x p v,
    ~ Free x p ->
    ALang.subst x v p = p.
  Proof.
    induction p; intros; simpl in *.
    - rewrite i_subst_not_free; auto.
    - rewrite IHp1; auto.
      rewrite IHp2; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite IHp1; auto.
        rewrite r_subst_not_free; auto.
      }
      rewrite IHp1; auto.
      rewrite IHp2; auto. 2: {
        intuition.
      }
      rewrite r_subst_not_free; auto.
  Qed.

  Lemma subst_not_occurs:
    forall x p v,
    ~ Occurs x p ->
    ALang.subst x v p = p.
  Proof.
    induction p; intros; simpl in *.
    - rewrite i_subst_not_occurs; auto.
    - rewrite IHp1; auto.
      rewrite IHp2; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        intuition.
      }
      rewrite IHp1; auto.
      rewrite IHp2; auto. 2: {
        intuition.
      }
      rewrite r_subst_not_free; auto.
      intuition.
  Qed.

  Lemma closed_subst_eq:
    forall p,
    Closed p ->
    forall x v,
    x <> TID ->
    ALang.subst x v p = p.
  Proof.
    intros.
    unfold Closed in *.
    rewrite subst_not_free; auto.
  Qed.

  Lemma closed_plug_subst:
    forall p,
    Closed p ->
    forall c x v,
    x <> TID ->
    ALang.subst x v (plug c p) = plug (subst x v c) p.
  Proof.
    induction c; intros; simpl.
    - auto using closed_subst_eq.
    - reflexivity.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
      destruct (Set_VAR.MF.eq_dec x v).
      + reflexivity.
      + reflexivity.
  Qed.

  Lemma var_inv_subst:
    forall c x y v,
    Var x (subst y v c) ->
    Var x c.
  Proof.
    induction c; simpl; intros.
    - assumption.
    - apply Free.var_inv_subst in H.
      assumption.
    - destruct H as [H|H]. {
        eauto.
      }
      apply ALang.var_inv_subst in H.
      auto.
    - destruct H as [H|H]; eauto using ALang.var_inv_subst.
    - destruct H as [H|[H|H]]; eauto.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        auto.
      }
      eauto using ALang.var_inv_subst.
    - destruct H as [H|[H|H]]; eauto using ALang.var_inv_subst.
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        auto.
      }
      eauto.
  Qed.

  Lemma compositionality_1:
    forall c,
    CDRF c ->
    ~ Var TID c ->
    forall p,
    Closed p ->
    IDRF p ->
    IDRF (plug c p).
  Proof.
    intros c H.    
    induction H; intros; simpl in *.
    - assumption.
    - apply idrf_sync.
      assumption.
    - apply idrf_seq; eauto.
    - apply idrf_seq; eauto.
    - apply idrf_for; eauto.
    - apply idrf_for.
      + assumption.
      + intros.
        assert (IDRF (plug (subst x (NNum n) c) p0)).
        { apply H1; auto.
          intros N.
          apply var_inv_subst in N.
          auto.
        }
        rewrite closed_plug_subst; auto.
  Qed.

  Lemma i_drf_1:
    forall p,
    IDRF p ->
    DRF p.
  Proof.
    intros.
    induction H; intros.
    - unfold UDRF, DRF in *.
      intros.
      apply H.
      invc H0.
      auto.
    - unfold DRF.
      intros.
      rename_hyp (IPairIn _ _) as h.
      invc h. {
        apply IHIDRF1; auto.
      }
      apply IHIDRF2; auto.
    - unfold DRF; intros.
      rename_hyp (IPairIn _ _) as h.
      invc h. {
        rename_hyp (IPairIn _ _) as h.
        apply IHIDRF in h.
        assumption.
      }
      rename_hyp (IPairIn _ _) as h.
      apply H1 in h; auto.
  Qed.

  Lemma i_drf_2:
    forall p,
    CanRun p ->
    DRF p ->
    IDRF p.
  Proof.
    intros p H.
    induction H; unfold DRF; intros drf.
    - constructor.
      unfold UDRF.
      intros.
      apply drf.
      constructor.
      assumption.
    - constructor.
      + apply IHCanRun1.
        unfold DRF; intros.
        apply drf.
        auto using i_pair_in_seq_l.
      + apply IHCanRun2.
        unfold DRF; intros.
        apply drf.
        auto using i_pair_in_seq_r.
    - constructor.
      + apply IHCanRun.
        unfold DRF; intros.
        apply drf.
        auto using i_pair_in_for_1.
      + intros.
        apply H1; auto.
        unfold DRF.
        intros.
        apply drf.
        eapply i_pair_in_for_2; eauto.
  Qed.

  Inductive CCanRun: ctxt -> Prop :=
  | c_can_run_hole:
    CCanRun Hole
  | c_can_run_sync:
    forall u,
    CCanRun (Sync u)
  | c_can_run_seq_l:
    forall c q,
    CCanRun c ->
    CanRun q ->
    CCanRun (SeqL c q)
  | c_can_run_seq_r:
    forall c p,
    CCanRun c ->
    CanRun p ->
    CCanRun (SeqR p c)
  | c_can_run_for_l:
    forall c x r q,
    CCanRun c ->
    (forall n, RPick r n -> CanRun (ALang.subst x (NNum n) q)) ->
    CCanRun (ForL c x r q)
  | c_can_run_for_r:
    forall p x r c,
    CanRun p ->
    (forall n, RPick r n -> CCanRun (subst x (NNum n) c)) ->
    CCanRun (ForR p x r c).

  Lemma plug_subst:
    forall x v c p,
    ~ Var x c ->
    ALang.subst x v (plug c p) = plug (subst x v c) (ALang.subst x v p).
  Proof.
    induction c; simpl; intros; auto.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
    - rewrite IHc; auto.
      destruct (Set_VAR.MF.eq_dec x v0). {
        subst.
        intuition.
      }
      auto.
  Qed.

  Fixpoint Distinct c :=
    match c with
    | Hole => True
    | Sync u => Distinct.Distinct u
    | SeqL c q => Distinct c /\ ALang.Distinct q
    | SeqR p c => ALang.Distinct p /\ Distinct c
    | ForL c x r q => Distinct c /\ ~ ALang.Var x q /\ ALang.Distinct q
    | ForR p x r c => ALang.Distinct p /\ ~ Var x c /\ Distinct c
    end.

  Lemma distinct_subst:
    forall c,
    Distinct c ->
    forall x v,
    Distinct (subst x v c).
  Proof.
    induction c; intros; simpl in *.
    - auto.
    - auto using Distinct.distinct_subst.
    - intuition.
      auto using ALang.distinct_subst.
    - intuition.
      auto using ALang.distinct_subst.
    - intuition; destruct (Set_VAR.MF.eq_dec x v); subst; auto.
      + rename_hyp (ALang.Var _ _) as hx.
        apply ALang.var_inv_subst in hx.
        intuition.
      + auto using ALang.distinct_subst.
    - intuition;
        destruct (Set_VAR.MF.eq_dec x v);
        subst;
        auto using ALang.distinct_subst.
      rename_hyp (Var _ _) as hx.
      apply var_inv_subst in hx.
      auto.
  Qed.

  Lemma drf_to_c_drf:
    forall c,
    CCanRun c ->
    Distinct c ->
    IDRF (plug c (NSync Skip)) ->
    CDRF c.
  Proof.
    intros c H.
    induction H; intros hd h; simpl in h; simpl in *.
    - constructor.
    - simpl in *.
      invc h; constructor; auto.
    - invc h.
      simpl in hd.
      destruct hd.
      constructor; auto.
    - invc h.
      constructor; auto.
      simpl in hd.
      destruct hd.
      auto.
    - invc h.
      simpl in hd.
      destruct hd as (?, (?, ?)).
      constructor; auto.
    - simpl in *.
      invc h.
      constructor; auto.
      intros.
      apply H1; auto. {
        apply distinct_subst.
        intuition.
      }
      assert (ha: IDRF (ALang.subst x (NNum n) (plug c (NSync Skip)))) by auto.
      rewrite plug_subst in ha.
      2: { intuition. }
      simpl in ha.
      assumption.
  Qed.

  Lemma can_run_1:
    forall c,
    CanRun (plug c (NSync Skip)) ->
    Distinct c ->
    CCanRun c.
  Proof.
    intros c H.
    remember (plug _ _) as q.
    generalize dependent c.
    induction H;
      intros c heq hd;
      destruct c;
      simpl in hd;
      simpl in heq;
      invc heq;
      intuition;
      try (constructor; auto).
    intros m hp.
    eapply H1; eauto.
    rewrite plug_subst; simpl; auto.
    apply distinct_subst; auto.
  Qed.

  Corollary compositionality:
    forall c,
    Distinct c ->                   (* All loop variables in c must be distinct *)
    CanRun (plug c (NSync Skip)) -> (* C[skip;sync] must be runnable *)
    DRF (plug c (NSync Skip)) ->    (* C[skip;sync] must be DRF *)
    ~ Var TID c ->                  (* TID is not declared in any loop that appears in c *)
    forall p,
    Closed p ->                     (* if the only free variable of p is TID *)
    CanRun p ->                     (* if p can run *)
    DRF p ->                        (* if p is DRF *)
    DRF (plug c p).                 (* Then, C[p] is also DRF *)
  Proof.
    intros c hd cr1 drf1 hv p hc cr2 drf2.
    apply i_drf_2 in drf1; auto.
    apply i_drf_2 in drf2; auto.
    apply drf_to_c_drf in drf1; auto using can_run_1.
    apply i_drf_1.
    auto using compositionality_1.
  Qed.

End Props.