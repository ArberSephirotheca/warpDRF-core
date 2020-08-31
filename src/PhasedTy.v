Require Import Coq.Lists.List.
Require Import VHist.
Require Import Tasks.
Require Import ALang.
Require Import NExp.
Require Import Var.
Require Import AccExp.
Require Import Phased.
Require Import ALangTy.
Require Import Lia.

Require Conc.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.

  Notation history := (list access_val).
  Notation mhistory := (list history).

  (* -------------------- PHASE OF ----------------------------- *)

  Inductive PhaseOf : inst -> phase -> Prop :=
  | phase_of_block:
    forall c,
    PhaseOf (Block c) PhOne
  | phase_of_sync:
    PhaseOf Sync PhOne
  | phase_of_seq: forall i j ph1 ph2,
    PhaseOf i ph1 ->
    PhaseOf j ph2 ->
    PhaseOf (Seq i j) (PhPlus ph1 ph2)
  | phase_of_for:
    forall x r i ph,
    PhaseOf i ph ->
    PhaseOf (For x r i) (PhSum x r ph)
  .

  Fixpoint phase_of (i:inst) :=
    match i with
    | Block _
    | Sync => PhOne
    | Seq i j => PhPlus (phase_of i) (phase_of j)
    | For x r i => PhSum x r (phase_of i)
    end.

  Lemma phase_of_to_prop:
    forall i,
    PhaseOf i (phase_of i).
  Proof.
    induction i; intros; simpl; constructor; auto.
  Qed.

  Lemma phase_of_from_prop:
    forall i ph,
    PhaseOf i ph ->
    phase_of i = ph.
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H; auto.
    - erewrite IHi1; eauto.
      erewrite IHi2; eauto.
    - erewrite IHi; eauto.
  Qed.

  Lemma phase_of_fun:
    forall i ph1 ph2,
    PhaseOf i ph1 ->
    PhaseOf i ph2 ->
    ph1 = ph2.
  Proof.
    intros.
    apply phase_of_from_prop in H.
    apply phase_of_from_prop in H0.
    rewrite H in H0.
    assumption.
  Qed.

  Lemma phase_of_subst:
    forall i ph,
    PhaseOf i ph ->
    forall x v,
    PhaseOf (i_subst x v i) (ph_subst x v ph).
  Proof.
    intros i ph H.
    induction H; intros y v; simpl.
    - apply phase_of_block.
    - apply phase_of_sync.
    - apply phase_of_seq; auto.
    - destruct (Set_VAR.MF.eq_dec y x); auto using phase_of_for.
  Qed.

  Lemma phase_of_inv_subst:
    forall ph x v i,
    PhaseOf (i_subst x v i) ph ->
    ph = ph_subst x v (phase_of i).
  Proof.
    intros.
    assert (Hp: PhaseOf i (phase_of i)) by auto using phase_of_to_prop.
    apply phase_of_subst with (x:=x) (v:=v) in Hp; auto.
    eauto using phase_of_fun.
  Qed.

  Lemma phase_of_subst_rw:
    forall x v i,
    phase_of (i_subst x v i) = ph_subst x v (phase_of i).
  Proof.
    intros.
    assert (Hp: PhaseOf (i_subst x v i) (phase_of (i_subst x v i))) by auto using phase_of_to_prop.
    apply phase_of_inv_subst in Hp.
    assumption.
  Qed.

  Lemma phase_to_run_ph:
    forall n ph,
    RunPh ph n ->
    forall i,
    PhaseOf i ph ->
    Phase i n.
  Proof.
    intros ph n H.
    induction H; intros i Hp; inversion Hp; subst; clear Hp.
    - apply phase_block.
    - apply phase_sync.
    - eauto using phase_seq.
    - eapply phase_for_cons; eauto using phase_of_subst, phase_of_for.
    - eapply phase_for_nil; eauto.
  Qed.

  Lemma run_ph_to_phase:
    forall i n,
    Phase i n ->
    forall ph,
    PhaseOf i ph ->
    RunPh ph n.
  Proof.
    intros i n H.
    induction H; intros ph Hp; inversion Hp; subst; clear Hp; try (constructor; fail).
    - econstructor; eauto.
    - eapply run_ph_sum_cons; eauto.
      + auto using phase_of_subst.
      + auto using phase_of_for.
    - eauto using run_ph_sum_nil.
  Qed.


  (* ------------------------- PHASEOF 2 -------------------- *)

  Definition PhaseOf2 (p:phased) (ph: phase) : Prop :=
    match p with
    | Phased1 c => ph = PhZero
    | Phased2 i c => PhaseOf i ph
    end.

  Definition phase_of2 (p:phased) :=
    match p with
    | Phased1 c => PhZero
    | Phased2 i c => phase_of i
    end.

  Lemma phase_of2_to_prop:
    forall i,
    PhaseOf2 i (phase_of2 i).
  Proof.
    intros [c|i c]; simpl; auto using phase_of_to_prop.
  Qed.

  Lemma phase_of2_from_prop:
    forall i ph,
    PhaseOf2 i ph ->
    phase_of2 i = ph.
  Proof.
    intros [c|i c]; simpl; auto using phase_of_from_prop.
  Qed.

  (* ---------------------------- SEQ1 -------------------------- *)

  Inductive Seq1 (c:Conc.inst) : inst -> inst -> Prop :=
  | seq1_sync:
    Seq1 c Sync (Block c)
  | seq1_block:
    forall c',
    Seq1 c (Block c') (Block (Conc.Seq c c'))
  | seq1_seq:
    forall i i' j,
    Seq1 c i i' ->
    Seq1 c (Seq i j) (Seq i' j)
  .

  Lemma seq1_norm:
    forall i,
    Norm i ->
    forall c,
    exists j,
    Seq1 c i j.
  Proof.
    induction i; intros; simpl in *.
    - eauto using seq1_sync.
    - eauto using seq1_block.
    - destruct i2; simpl in H; destruct H;
      destruct IHi1 with (c:=c) as (j', Hs); auto;
      eauto using seq1_seq.
    - apply norm_for in H. contradiction.
  Qed.

  Lemma seq1_to_norm:
    forall c i i',
    Seq1 c i i' ->
    Norm i ->
    Norm i'.
  Proof.
    intros c i i' H.
    induction H; intros; simpl; auto.
    simpl in H0.
    assert (Hni': Norm i') by eauto using norm_inv_seq_l; clear IHSeq1.
    eapply norm_seq_2; eauto.
  Qed.

  Lemma in_phase_seq1_l:
    forall a c i j,
    Conc.IIn a c ->
    Seq1 c i j ->
    InPhase a 0 j.
  Proof.
    induction i; intros; simpl in *; inversion H0; subst; clear H0.
    - constructor; auto.
    - auto using in_phase_block, Conc.i_in_seq_l.
    - auto using in_phase_seq_l.
  Qed.

  Lemma in_phase_seq1_r:
    forall i n a c j j',
    Phase i n ->
    Conc.IIn a c ->
    Seq1 c j j' ->
    InPhase a n (Seq i j').
  Proof.
    induction j; intros; simpl in *; inversion H1; subst; clear H1.
    - eauto using in_phase_seq_r, in_phase_block.
    - eauto using in_phase_seq_r, in_phase_block, Conc.i_in_seq_l.
    - eauto using in_phase_seq_r, in_phase_seq_l, in_phase_seq1_l.
  Qed.

  (* ------------------------------ SEQ2 ----------------------------- *)

  Inductive Seq2 (c:Conc.inst) : phased -> phased -> Prop :=
  | seq2_1:
    forall c',
    Seq2 c (Phased1 c') (Phased1 (Conc.Seq c c'))
  | seq2_2:
    forall i c' i',
    Seq1 c i i' ->
    Seq2 c (Phased2 i c') (Phased2 i' c')
  .

  Lemma seq2_norm:
    forall p,
    PNorm p ->
    forall c,
    exists p', Seq2 c p p'.
  Proof.
    intros.
    destruct p as [c' | i c']; simpl in *.
    - eauto using seq2_1.
    - destruct seq1_norm with (i:=i) (c:=c) as (i', Hi); auto.
      eauto using seq2_2.
  Qed.

  Lemma seq2_to_norm:
    forall c p p',
    PNorm p ->
    Seq2 c p p' ->
    PNorm p'.
  Proof.
    intros.
    inversion H0; subst; clear H0; simpl; auto.
    simpl in *.
    eauto using seq1_to_norm.
  Qed.



  Lemma in_phase2_seq2_l:
    forall a c i j,
    Conc.IIn a c ->
    Seq2 c i j ->
    InPhase2 a 0 j.
  Proof.
    intros a c [c'|i c'] j Hi Hp; inversion Hp; subst; clear Hp.
    - auto using in_phase2_1, Conc.i_in_seq_l.
    - eauto using in_phase2_2_l, in_phase_seq1_l.
  Qed.

  Lemma phase_seq1:
    forall i n,
    Phase i n ->
    forall c j,
    Seq1 c i j ->
    Phase j n.
  Proof.
    intros i n H.
    induction H; intros; simpl in *.
    - inversion H; subst; clear H.
      apply phase_block.
    - inversion H; subst; clear H.
      apply phase_block.
    - inversion H2; subst; clear H2.
      eauto using phase_seq.
    - inversion H5.
    - inversion H2.
  Qed.

  Lemma phase2_1:
    forall c,
    Phase2 (Phased1 c) 0.
  Proof.
    intros.
    simpl; auto.
  Qed.

  Lemma phase2_seq2:
    forall c p n p',
    Phase2 p n ->
    Seq2 c p p' ->
    Phase2 p' n.
  Proof.
    intros.
    destruct p; simpl in *; inversion H0; subst; clear H0.
    - apply phase2_1.
    - inversion H4; subst; clear H4; inversion H; subst; clear H; simpl.
      + apply phase_block.
      + apply phase_block.
      + eapply phase_seq1 in H0; eauto.
        eauto using phase_seq.
  Qed.

  (* -------------------------------- SEQ3 --------------------- *)

  Definition seq3 (n:inst) (a:phased) : phased :=
    match a with
    | Phased1 c2 => Phased2 n c2
    | Phased2 n2 c2 => Phased2 (Seq n n2) c2
    end.

  Lemma seq3_norm:
    forall i p,
    Norm i ->
    PNorm p ->
    PNorm (seq3 i p).
  Proof.
    intros.
    destruct p; simpl in *; auto.
    auto using norm_seq_1.
  Qed.

  Lemma seq3_inv_1:
    forall i p c,
    seq3 i p = Phased1 c ->
    False.
  Proof.
    intros.
    destruct p as [c'|i' c']; simpl in *.
    - inversion H.
    - inversion H; subst; clear H.
  Qed.


  Lemma in_phase2_seq3_l:
    forall a n i p,
    InPhase a n i ->
    InPhase2 a n (seq3 i p).
  Proof.
    intros.
    destruct p as [c | j c]; simpl.
    - auto.
    - left.
      auto using in_phase_seq_l.
  Qed.

  Lemma in_phase2_seq3_r:
    forall i p a m n,
    Phase i n ->
    InPhase2 a m p ->
    InPhase2 a (n + m) (seq3 i p).
  Proof.
    intros.
    destruct p as [c |j c]; simpl in *.
    - destruct H0 as (?, Hi).
      subst.
      rewrite PeanoNat.Nat.add_0_r.
      auto.
    - destruct H0 as [Hi | (Hp, Hi)].
      + left.
        eapply in_phase_seq_r; eauto.
      + subst.
        right.
        eexists.
        repeat split.
        * eapply phase_seq; eauto.
        * auto.
  Qed.

  Lemma phase2_seq3:
    forall i n1 n2 o p,
    Phase i n1 ->
    Phase2 p n2 ->
    o = n1 + n2 ->
    Phase2 (seq3 i p) o.
  Proof.
    intros.
    destruct p as [c|j c]; simpl in *; subst.
    - rewrite PeanoNat.Nat.add_0_r.
      assumption.
    - eauto using phase_seq.
  Qed.


  (* ----------------------- PSEQ -------------------------------- *)

  Inductive PSeq: phased -> phased -> phased -> Prop :=
  | pseq_phased1:
    forall c1 p2 p2',
    Seq2 c1 p2 p2' ->
    PSeq (Phased1 c1) p2 p2'
  | pseq_phased2:
    forall c1 i1 p2 p2',
    Seq2 c1 p2 p2' ->
    PSeq (Phased2 i1 c1) p2 (seq3 i1 p2').

  Lemma pseq_norm:
    forall p1 p2,
    PNorm p1 ->
    PNorm p2 ->
    exists p, PSeq p1 p2 p.
  Proof.
    intros [c1 | i1 c1]; simpl; intros. {
      apply seq2_norm with (c:=c1) in H0.
      destruct H0 as (p', Hs).
      eauto using pseq_phased1.
    }
    apply seq2_norm with (c:=c1) in H0.
    destruct H0 as (p', Hs).
    eauto using pseq_phased2.
  Qed.


  Lemma pseq_to_norm:
    forall p1 p2 p,
    PNorm p1 ->
    PNorm p2 ->
    PSeq p1 p2 p ->
    PNorm p.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    - simpl in *.
      eauto using seq2_to_norm.
    - simpl in *.
      assert (PNorm p2') by eauto using seq2_to_norm.
      apply seq3_norm; auto.
  Qed.

  Lemma pseq_inv_1:
    forall i j c,
    PSeq i j (Phased1 c) ->
    exists ci cj,
    i = Phased1 ci /\ j = Phased1 cj.
  Proof.
    intros.
    inversion H; subst; clear H.
    - inversion H0; subst; clear H0.
      eauto.
    - apply seq3_inv_1 in H0.
      contradiction.
  Qed.

  Lemma phase2_pseq:
    forall p1 p2 n1 n2 o p,
    Phase2 p1 n1 ->
    Phase2 p2 n2 ->
    o = n1 + n2 ->
    PSeq p1 p2 p ->
    Phase2 p o.
  Proof.
    intros.
    destruct p1 as [c|i c]; simpl in *; inversion H2; subst; clear H2.
    - eauto using phase2_seq2.
    - eapply phase2_seq3; eauto.
      eapply phase2_seq2; eauto.
  Qed.

  (* ------------------------------ TRANSLATE --------------------- *)

  Inductive Translate: ALang.inst -> phased -> Prop :=
  | translate_block:
    forall c,
    Translate (ALang.Block c) (Phased1 c)
  | translate_sync:
    Translate ALang.Sync (Phased2 Sync Conc.Skip)
  | translate_seq:
    forall i j pi pj p,
    Translate i pi ->
    Translate j pj ->
    PSeq pi pj p ->
    Translate (ALang.Seq i j) p
  | translate_for_1:
    forall i c x r,
    Translate i (Phased1 c) ->
    Translate (ALang.For x r i) (Phased1 (Conc.For x r c))
  | translate_for_2:
    forall e1 e2 x i c b j,
    let e2' := NBin NMinus e2 (NNum 1) in
    let x' := NBin NPlus (NNum 1) (NVar x) in
    Translate i (Phased2 b c) ->
    Seq1 c (i_subst x x' b) j ->
    Translate (ALang.For x (e1, e2) i) (
      Phased2
        (Seq (i_subst x e1 b) (For x (e1, e2') j))
        (Conc.i_subst x e2' c)
    ).

  Lemma translate_to_norm:
    forall i p,
    Translate i p ->
    PNorm p.
  Proof.
    intros i p H.
    induction H; simpl; auto.
    - apply norm_sync.
    - eauto using pseq_to_norm.
    - simpl in *.
      apply norm_seq_for.
      + auto using norm_subst.
      + eapply seq1_to_norm; eauto using norm_subst.
  Qed.

  Lemma translate_exists:
    forall i,
    exists p, Translate i p.
  Proof.
    induction i; intros.
    - eexists.
      apply translate_sync.
    - eexists.
      apply translate_block.
    - destruct IHi1 as (pi, Hi).
      destruct IHi2 as (pj, Hj).
      assert (Hni: PNorm pi) by eauto using translate_to_norm.
      assert (Hnj: PNorm pj) by eauto using translate_to_norm.
      destruct pseq_norm with (p1:=pi) (p2:=pj) as (p, Hs); auto.
      exists p.
      eapply translate_seq; eauto.
    - destruct IHi as (p, Ht).
      destruct p as [c | i' c].
      + eauto using translate_for_1.
      + destruct r as (e1, e2).
        assert (Hn: PNorm (Phased2 i' c)) by eauto using translate_to_norm.
        simpl in Hn.
        assert (Hn': exists p, Seq1 c (i_subst v (NBin NPlus (NNum 1) (NVar v)) i') p). {
          auto using seq1_norm, norm_subst.
        }
        destruct Hn' as (p, Hn').
        eexists.
        apply translate_for_2; eauto.
  Qed.

  Lemma phase_of_seq1:
    forall c i j,
    Seq1 c i j ->
    phase_of i = phase_of j.
  Proof.
    intros c i j H.
    induction H; auto.
    simpl.
    rewrite IHSeq1.
    reflexivity.
  Qed.

  Lemma translate_phase_of:
    forall i n,
    Translate i n ->
    forall ph1,
    ALangTy.PhaseOf i ph1 ->
    forall ph2,
    PhaseOf2 n ph2 ->
    PhEq ph1 ph2.
  Proof.
    intros i n H.
    induction H; intros ph1 Hp1 ph2 Hp2.
    - admit.
    - admit.
    - admit.
    - admit.
    - simpl in *.
      inversion Hp2; subst; clear Hp2.
      inversion Hp1; subst; clear Hp1.
      eapply IHTranslate with (ph2:=phase_of2 (Phased2 b c)) in H7; eauto using phase_of2_to_prop.
      + apply phase_of_inv_subst in H3.
        subst.
        apply phase_of_from_prop in H5.
        subst.
        simpl in *.
        apply phase_of_seq1 in H0.
        rewrite phase_of_subst_rw in H0.
        rewrite <- H0.
        admit.
      + simpl.
        eapply phase_of_to_prop.
  Admitted.
(*
  Inductive PhTranslate: ALang.inst -> phased -> nat -> Prop :=
  | ph_translate_block:
    forall c,
    PhTranslate (ALang.Block c) (Phased1 c) 0
  | ph_translate_sync:
    PhTranslate ALang.Sync (Phased2 Sync Conc.Skip) 1
  | ph_translate_seq:
    forall i j pi pj p,
    Translate i pi ni ->
    Translate j pj nj ->
    PSeq pi pj p ->
    PhTranslate (ALang.Seq i j) p (ni+nj)
  | ph_translate_for_1:
    forall i c x r,
    PhTranslate i (Phased1 c) 0 ->
    PhTranslate (ALang.For x r i) (Phased1 (Conc.For x r c)) 0
  | ph_translate_for_2:
    forall e1 e2 x i c b j,
    let e2' := NBin NMinus e2 (NNum 1) in
    let x' := NBin NPlus (NNum 1) (NVar x) in
    PhTranslate i (Phased2 b c) n ->
    Seq1 c (i_subst x x' b) j ->
    PhTranslate (ALang.For x (e1, e2) i) (
      Phased2
        (Seq (i_subst x e1 b) (For x (e1, e2') j))
        (Conc.i_subst x e2' c)
    ).

*)

  Lemma phase_to_phase2:
    forall i n,
    ALang.Phase i n ->
    forall p,
    Translate i p ->
    Phase2 p n.
  Proof.
    intros i n H.
    induction H; intros p Ht.
    - inversion Ht; subst; clear Ht.
      apply phase2_1.
    - inversion Ht; subst; clear Ht.
      simpl.
      apply phase_sync.
    - inversion Ht; subst; clear Ht.
      eapply phase2_pseq with (p1:=pi) (p2:=pj); eauto.
    - assert (Ht1: exists p, Translate (ALang.i_subst x (NNum n1) i) p) by auto using translate_exists.
      destruct Ht1 as (p1, Ht1).
      assert (IHPhase1 := IHPhase1 _ Ht1).
      assert (Ht2: exists p, Translate (For x (NNum (S n1), e2) i) p) by auto using translate_exists.
      destruct Ht2 as (p2, Ht2).
      assert (IHPhase2 := IHPhase2 _ Ht2).
      subst.
      inversion Ht; subst; clear Ht. {
        admit.
      }
      simpl.
      eapply phase_seq; eauto.
      + admit.
      + admit.
    - admit.
  Admitted.

  Lemma in_phase_spec:
    forall i,
    forall a n,
    ALang.InPhase a n i ->
    forall p,
    Translate i p ->
    InPhase2 a n p.
  Proof.
    intros i a n H.
    induction H; intros p Heq; simpl in *; inversion Heq; subst; clear Heq; simpl.
    - auto.
    - apply IHInPhase in H2.
      (* Sequence 1 *)
      admit.
    - (* Sequence 2 *)
      assert (InPhase2 a m pj) by auto.
      admit.
    - (* conc-loop *)
      admit.
    - 
      admit.
    - admit.
    - admit.
  Admitted.

End Defs.