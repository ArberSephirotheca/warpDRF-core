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

  (* ---------------------------- TRANSLATION ---------------------- *)
(*
  Fixpoint seq1 (c:Conc.inst) (n:inst) : option inst :=
    match n with
    | Sync => Some (Block c)
    | Block c2 => Some (Block (Conc.Seq c c2))
    | Seq i j => match seq1 c i with
      | Some i => Some (Seq i j)
      | None => None
      end
    | For _ _ _ => None 
    end.
*)
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

  (*
  Definition seq2 (c:Conc.inst) (a:phased) : option phased :=
    match a with
    | OnlyUnsync c2 => Some (OnlyUnsync (Conc.Seq c c2))
    | SyncUnsync i c2 =>
      match seq1 c i with
      | Some i => Some (SyncUnsync i c2)
      | None => None
      end
    end.
  *)
  Inductive Seq2 (c:Conc.inst) : phased -> phased -> Prop :=
  | seq2_1:
    forall c',
    Seq2 c (Phased1 c') (Phased1 (Conc.Seq c c'))
  | seq2_2:
    forall i c' i',
    Seq1 c i i' ->
    Seq2 c (Phased2 i c') (Phased2 i' c')
  .

  Definition seq3 (n:inst) (a:phased) : phased :=
    match a with
    | Phased1 c2 => Phased2 n c2
    | Phased2 n2 c2 => Phased2 (Seq n n2) c2
    end.

  (*
  Definition seq (a1 a2: phased) : option phased :=
    match a1 with
    | OnlyUnsync c1 => seq2 c1 a2
    | SyncUnsync n c1 =>
      match seq2 c1 a2 with
      | Some p => Some (seq3 n p)
      | None => None
      end 
    end.
  *)
  Inductive PSeq: phased -> phased -> phased -> Prop :=
  | pseq_phased1:
    forall c1 p2 p2',
    Seq2 c1 p2 p2' ->
    PSeq (Phased1 c1) p2 p2'
  | pseq_phased2:
    forall c1 i1 p2 p2',
    Seq2 c1 p2 p2' ->
    PSeq (Phased2 i1 c1) p2 (seq3 i1 p2').

  Fixpoint i_subst x v (i:inst) :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | For y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      For y (r_subst x v r) i'
    end.
(*
  Fixpoint translate (i:ALang.inst) : option phased :=
    match i with
    | ALang.Block c => Some (OnlyUnsync c)
    | ALang.Sync => Some (SyncUnsync Sync Conc.Skip)
    | ALang.Seq i j =>
      match translate i, translate j with
      | Some i, Some j => seq i j
      | _, _ => None
      end
    | ALang.For x (e1, e2) i =>
      match translate i with
      | Some (OnlyUnsync c) => Some (OnlyUnsync (Conc.For x (e1, e2) c))
      | Some (SyncUnsync b c) =>
        let e2' := NBin NMinus e2 (NNum 1) in
        let x' := NBin NPlus (NNum 1) (NVar x) in
        match seq1 c (i_subst x x' b) with
        | Some i => 
          Some (SyncUnsync
            (Seq (i_subst x e1 b) (For x (e1, e2') i))
            (Conc.i_subst x e2' c))
        | None => None
        end
      | None => None
      end
    end.
*)

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
    forall i c x e1 e2,
    Translate i (Phased1 c) ->
    Translate (ALang.For x (e1, e2) i) (Phased1 (Conc.For x (e1, e2) c))
  | translate_for_2:
    forall e1 e2 x i c b,
    let e2' := NBin NMinus e2 (NNum 1) in
    let x' := NBin NPlus (NNum 1) (NVar x) in
    Translate i (Phased2 b c) ->
    Seq1 c (i_subst x x' b) i ->
    Translate (ALang.For x (e1, e2) i) (
      Phased2
        (Seq (i_subst x e1 b) (For x (e1, e2') i))
        (Conc.i_subst x e2' c)
    ).

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

  Lemma seq1_to_seq1:
    forall c i j,
    Seq1 c i j ->
    forall c',
    exists k, Seq1 c' j k.
  Proof.
    intros c i j H.
    induction H; intros.
    - eauto using seq1_block.
    - eauto using seq1_block.
    - destruct (IHSeq1 c') as (k, Hi).
      eauto using seq1_seq.
  Qed.

  Lemma seq2_to_seq2:
    forall c pi pj,
    Seq2 c pi pj ->
    forall c',
    exists p', Seq2 c' pj p'.
  Proof.
    intros.
    inversion H; subst; clear H.
    - eexists.
      apply seq2_1.
    - apply seq1_to_seq1 with (c':=c') in H0.
      destruct H0 as (k, Hi).
      eexists.
      apply seq2_2.
      eauto.
  Qed.
  (* XXX: I actually just need a notion of well-formedness.
          Prove: WF terms can be sequenced. *)

  Lemma seq2_to_seq2_1_2:
    forall c1 i p1,
    Seq1 c1 i p1 ->
    forall c2 p2, 
    Seq2 c1 (Phased1 c2) p2 ->
    exists p', Seq2 c1 (Phased2 i c2) p'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eexists.
    apply seq2_2.
    eauto.
  Qed.
(*
  Lemma p_seq_to_seq2:
    forall pi pj p,
    PSeq pi pj p ->
    forall c,
    exists p', Seq2 c p p'.
  Proof.
    intros.
    inversion H; subst; clear H.
    - eauto using seq2_to_seq2.
    - apply seq2_to_seq2 with (c':=c) in H0.
      destruct H0 as (p', Hs).
      destruct p2' as [ci | ci p2'].
      + simpl.
        eexists.
        assumption.
  Qed.
*)
  Lemma translate_to_pseq_1:
    forall i p,
    Translate i p ->
    forall c,
    exists p', PSeq (Phased1 c) p p'.
  Proof.
    intros i p H.
    induction H; intros c'.
    - eexists.
      apply pseq_phased1.
      apply seq2_1.
    - eexists.
      apply pseq_phased1.
      apply seq2_2.
      apply seq1_sync.
    - eexists.
      apply pseq_phased1.
      destruct p as [c | c p].
      + apply seq2_2.
  Qed.

  Lemma translate_to_pseq:
    forall i pi,
    Translate i pi ->
    forall j pj,
    Translate j pj ->
    exists p, PSeq pi pj p.
  Proof.
    intros i pi H.
    induction H; intros.
    -  
  Qed.

  Lemma translate_subst:
    forall i p,
    Translate i p ->
    forall x v,
    exists p',
    Translate
      (ALang.i_subst x v i) p'.
  Proof.
    intros i p H.
    induction H; intros.
    - eauto using translate_block.
    - simpl.
      eauto using translate_sync.
    - simpl.
      destruct IHTranslate1 with (x:=x) (v:=v) as (pi', Hti); auto.
      destruct IHTranslate2 with (x:=x) (v:=v) as (pj', Htj); auto.
      
      eexists.
      eexists.
      destruct pi as [ci|ii ci]. {
        clear IHTranslate1.
        inversion H1; subst; clear H1.
        inversion H3; subst; clear H3.
        assert (IHTranslate2 := IHTranslate2 _ _ eq_refl y v).
        destruct IHTranslate2 as (j'', (c'', Ht2)).
        eapply translate_seq; eauto.
        - 
        inversion H4; subst; clear H4.
        - apply IH
      }
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
(*
  Lemma translate_inv_1_phase:
    forall i c,
    Translate i (Phased1 c) ->
    forall m,
    ALang.Run i m ->
    exists h, m = v_one h.
  Proof.
    intros i c H.
    remember (Phased1 _) as p.
    generalize dependent c.
    induction H; intros.
    - inversion Heqp; subst; clear Heqp.
      inversion H; subst; clear H.
      eauto.
    - inversion Heqp.
    - subst.
      apply pseq_inv_1 in H1.
      destruct H1 as (ci, (cj, (?, ?))).
      subst.
      inversion H2; subst; clear H2.
      eapply IHTranslate1 in H4; eauto.
      eapply IHTranslate2 in H5; eauto.
      destruct H4 as (h1, ?).
      destruct H5 as (h2, ?).
      subst.
      simpl.
      eauto.
    - inversion Heqp; subst; clear Heqp.
      
      apply ALang.phase_for.
      inversion H1; subst; clear H1.
  Qed.
*)
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
    - simpl.
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