Require Import Coq.Lists.List.
Require Import NExp.
Require Import Var.
Require Import AccExp.
Require Import Tasks.
Require Import VHist.
Require Conc.
Require Import ALang.

Require Import Lia.

Import ListNotations.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.

  Notation history := (list access_val).
  Notation mhistory := (list history).

  Inductive phased :=
  | Phased1: Conc.inst -> phased
  | Phased2: inst -> Conc.inst -> phased
  .

  Definition skip_for (i:inst) :=
    match i with
    | For _ _ j => j
    | _ => i
    end.
(*
  Inductive Norm: inst -> Prop :=
  | norm_sync:
    Norm Sync
  | norm_block:
    forall c,
    Norm (Block c)
  | norm_seq:
    forall i j,
    Norm i ->
    Norm (skip_for j) ->
    Norm (Seq i j).
*)

  Fixpoint NormEx (i: inst) (for_ok:bool) : Prop :=
    match i with
    | Sync => True
    | Block _ => True
    | Seq i j => NormEx i false /\ NormEx j true
    | For _ _ _ => for_ok = true
    end.

  Definition Norm i := NormEx i false.
(*
  Lemma norm_ex_false:
    forall i,
    Norm
*)
(*
  Lemma
    forall i,
    (exists x r j, i = For x r j) \/  
*)
(*
  Lemma skip_for_i_subst_rw:
    forall i x v,
    skip_for (i_subst x v i) = i_subst x v (skip_for i).
  Proof.
    induction i; intros; simpl; auto.
    destruct (Set_VAR.MF.eq_dec x v). {
      subst.
  Qed.
*)
  Lemma norm_ex_subst:
    forall i b,
    NormEx i b ->
    forall x v,
    NormEx (i_subst x v i) b.
  Proof.
    induction i; intros; simpl in *; auto.
    destruct H as (Ha, Hb).
    apply IHi1 with (x:=x) (v:=v) in Ha.
    apply IHi2 with (x:=x) (v:=v) in Hb.
    auto.
  Qed.

  Lemma norm_ex_incl:
    forall i,
    NormEx i false ->
    NormEx i true.
  Proof.
    intros.
    destruct i; simpl in *; auto.
  Qed.

  Lemma norm_subst:
    forall i,
    Norm i ->
    forall x v,
    Norm (i_subst x v i).
  Proof.
    unfold Norm.
    intros.
    auto using norm_ex_subst.
  Qed.

  Lemma norm_for:
    forall x r i,
    ~ Norm (For x r i).
  Proof.
    unfold Norm.
    intros.
    intros N.
    simpl in *.
    inversion N.
  Qed.

  Lemma norm_seq_1:
    forall i j,
    Norm i ->
    Norm j ->
    Norm (Seq i j).
  Proof.
    unfold Norm; intros i j Hni Hnj.
    simpl.
    split; auto using norm_ex_incl.
  Qed.

  Lemma norm_seq_for:
    forall i x r j,
    Norm i ->
    Norm j ->
    Norm (Seq i (For x r j)).
  Proof.
    unfold Norm; simpl; intros.
    split; auto.
  Qed.

  Lemma norm_seq_2:
    forall i i' j,
    Norm (Seq i' j) ->
    Norm i ->
    Norm (Seq i j).
  Proof.
    unfold Norm.
    intros.
    inversion H; subst; clear H.
    simpl.
    split; auto.
  Qed.

  Lemma norm_sync:
    Norm Sync.
  Proof.
    unfold Norm; simpl; auto.
  Qed.

  Lemma norm_inv_seq_l:
    forall i j,
    Norm (Seq i j) ->
    Norm i.
  Proof.
    unfold Norm.
    intros.
    simpl in *.
    destruct H; auto.
  Qed.

  Definition PNorm (p:phased) : Prop :=
    match p with
    | Phased1 _ => True
    | Phased2 i _ => Norm i
    end.

  Inductive Run: inst -> list history -> Prop :=
  | run_sync:
    Run Sync []
  | run_block:
    forall c h,
    Conc.RunAll TID_COUNT c h ->
    Run (Block c) [h]
  | run_seq: forall i j mh_i mh_j mh,
    Run i mh_i ->
    Run j mh_j ->
    mh_i ++ mh_j = mh ->
    Run (Seq i j) mh
  | run_for_cons:
    forall e1 e2 n1 n2 i x m1 m2 m3,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run (i_subst x (NNum n1) i) m1 ->
    Run (For x (NNum (S n1), NNum n2) i) m2 ->
    m1 ++ m2 = m3 ->
    Run (For x (e1, e2) i) m3
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run (For x (e1, e2) i) []
  .

  (* ----------------------- Acces membership ---------------------- *)

  Inductive Phase : inst -> nat -> Prop :=
  | phase_block:
    forall c,
    Phase (Block c) 1
  | phase_sync:
    Phase Sync 1
  | phase_seq:
    forall i j n m o,
    Phase i n ->
    Phase j m ->
    o = n + m ->
    Phase (Seq i j) o
  | phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    Phase (For x (NNum (S n1), e2) i) m ->
    n + m = o ->
    Phase (For x (e1, e2) i) o
  | phase_for_nil:
    forall i x e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Phase (For x (e1, e2) i) 0
  .

  Inductive InPhase (a:access_val) : nat -> inst -> Prop :=
  | in_phase_block:
    forall c,
    Conc.IIn a c ->
    InPhase a 0 (Block c)
  | in_phase_seq_l:
    forall i j n,
    InPhase a n i ->
    InPhase a n (Seq i j)
  | in_phase_seq_r:
    forall i j n m o,
    Phase i n ->
    InPhase a m j ->
    o = n + m ->
    InPhase a o (Seq i j)
  | in_phase_for_eq:
    forall i x e1 e2 n1 n2 n,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    InPhase a n (i_subst x (NNum n1) i) ->
    InPhase a n (For x (NNum (S n1), e2) i)
  | in_phase_for_cons:
    forall i x e1 e2 n1 n2 n m o,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Phase (i_subst x (NNum n1) i) n ->
    InPhase a m (For x (NNum (S n1), e2) i) ->
    o = n + m ->
    InPhase a o (For x (e1, e2) i)
  .

  (* --------------------- IN PHASE 2 -------------------- *)


  Definition InPhase2 a n (p:phased) :=
    match p with
    | Phased1 c => n = 0 /\ Conc.IIn a c
    | Phased2 i c =>
      InPhase a n i \/
      Phase i n /\ Conc.IIn a c
    end.

  Definition Phase2 (p:phased) (n:nat) : Prop :=
    match p with
    | Phased1 c => n = 0
    | Phased2 i _ => Phase i n
    end.



  Lemma in_phase2_1:
    forall a c,
    Conc.IIn a c ->
    InPhase2 a 0 (Phased1 c).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma in_phase2_2_l:
    forall a n i c,
    InPhase a n i ->
    InPhase2 a n (Phased2 i c).
  Proof.
    intros.
    simpl.
    left.
    assumption.
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

  (* ------------------------ SUBST ------------------------- *)

  Fixpoint i_subst x v (i:inst) :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | For y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      For y (r_subst x v r) i'
    end.

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


  Lemma phase_to_phase2:
    forall i n,
    ALang.Phase i n ->
    forall p,
    Translate i p ->
    Phase2 p n.
  Proof.
    intros i n H.
    induction H; intros p Ht; inversion Ht; subst; clear Ht.
    - apply phase2_1.
    - simpl.
      apply phase_sync.
    - eapply phase2_pseq with (p1:=pi) (p2:=pj); eauto.
    - admit.
    - assert (Ht1: exists p, Translate (ALang.i_subst x (NNum n1) i) p) by auto using translate_exists.
      destruct Ht1 as (p1, Ht1).
      assert (IHPhase1 := IHPhase1 _ Ht1).
      assert (Ht2: exists p, Translate (For x (NNum (S n1), e2) i) p) by auto using translate_exists.
      destruct Ht2 as (p2, Ht2).
      assert (IHPhase2 := IHPhase2 _ Ht2).
      simpl.
      eapply phase_seq; eauto.
      + 
      apply phase2_1.
    intros p Heq; simpl in *.
    - inversion Heq; subst; clear Heq.
      reflexivity.
    - inversion Heq; subst; clear Heq.
      constructor.
    - destruct (translate i) as [pi|] eqn:R1.
      2: { inversion Heq. }
      destruct (translate j) as [pj|] eqn:R2.
      2: { inversion Heq. }
      assert (IHPhase1 := IHPhase1 _ eq_refl). 
      assert (IHPhase2 := IHPhase2 _ eq_refl). 
      subst.
      eapply phase2_seq with (p1:=pi) (p2:=pj); eauto.
    - destruct (translate i) as [pi|] eqn:R1.
      2: { inversion Heq. }
      destruct pi as [j c|c]. {
        destruct (seq1 c (i_subst x (NBin NPlus (NNum 1) (NVar x)) j)) as [o'|].
        2: { inversion Heq. }
        inversion Heq; subst; clear Heq.
      }
      destruct (translate j) as [pj|] eqn:R2.
      2: { inversion Heq. }
      
  Qed.

  Lemma in_phase_spec:
    forall i,
    forall a n,
    ALang.InPhase a n i ->
    forall p,
    translate i = Some p ->
    InPhase2 a n p.
  Proof.
    intros i a n H.
    induction H; intros p Heq; simpl in *; inversion Heq; subst; clear Heq; simpl.
    - auto.
    - destruct (translate i) as [[i' c1 | c1]|];
        destruct (translate j) as [[j' c2 | c2]|];
        try (inversion H1; fail); simpl in *;
        assert (IHInPhase := IHInPhase _ eq_refl).
      + destruct (seq1 c1 _) as [j''|] eqn:R; inversion H1; subst; clear H1.
        simpl in *.
        destruct IHInPhase as [Hi|(Hp,Hi)].
        * left.
          apply in_phase_seq_l.
          assumption.
        * left.
          eapply in_phase_seq1_r; eauto.
      + inversion H1; subst; clear H1.
        simpl in *.
        intuition.
        right; split; auto.
        apply Conc.i_in_seq_l.
        assumption.
      + destruct (seq1 c1 _) as [j''|] eqn:R; inversion H1; subst; clear H1.
        simpl in *.
        destruct IHInPhase as (?, Hi).
        subst.
        left.
        eapply in_phase_seq1_l; eauto.
      + inversion H1; subst; clear H1.
        simpl in *.
        destruct IHInPhase as (?, Hi).
        subst.
        split; auto using Conc.i_in_seq_l.
    - destruct (translate i) as [p1|] eqn:R1.
      2: { inversion H3. }
      destruct (translate j) as [p2|] eqn:R2.
      2: { inversion H3. }
      assert (IHInPhase := IHInPhase _ eq_refl).
      destruct p1 as [j1 c1 | c1], p2 as [j2 c2 | c2]; simpl in *.
      + admit.
      + inversion H3; subst; clear H3.
        destruct IHInPhase as (?, Hi).
        subst.
        simpl.
        right.
        simpl in *.
      }
        destruct (translate j) as [[j' c2 | c2]|].
        ;
        try (inversion H3; fail); simpl in *.
      * admit.
      * admit.
      * inversion H3.
      * admit. 
      * admit.
      * inversion H3.
      * 
      destruct (translate i) as [j' c | c]; simpl in *.
      
      try (inversion H1; fail). {
        .
        simpl in *.
        destruct (translate j) as [[j' c2 | c2]|]; try (inversion H1; fail); simpl in H1. {
          
        }
      }
      destruct (translate j) as [[j' c2 | c2]|]; try (inversion H1; fail); simpl in H1.
      destruct (translate i) as [j' c | c]; simpl in *.
      + destruct IHInPhase as [Hi|(Hp, Hi)].
        * auto using in_phase2_seq3_l.
        * assert (R: n = n + 0) by auto using PeanoNat.Nat.add_0_r.
          rewrite R; clear R.
          apply in_phase2_seq3_r; auto.
          
  Qed.
End Defs.