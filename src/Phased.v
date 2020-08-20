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
  | SyncUnsync: inst -> Conc.inst -> phased
  | OnlyUnsync: Conc.inst -> phased.

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
    Run (For x (e1, e2) i) [].

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
    Phase (For x (e1, e2) i) 0.

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
    InPhase a o (For x (e1, e2) i).

  Definition InPhase2 a n (p:phased) :=
    match p with
    | OnlyUnsync c => n = 0 /\ Conc.IIn a c
    | SyncUnsync i c =>
      InPhase a n i \/
      Phase i n /\ Conc.IIn a c
    end.

  Definition Phase2 (p:phased) (n:nat) : Prop :=
    match p with
    | OnlyUnsync c => n = 0
    | SyncUnsync i _ => Phase i n
    end.

  (* ---------------------------- TRANSLATION ---------------------- *)

  Fixpoint seq1 (c:Conc.inst) (n:inst) :=
    match n with
    | Sync => Some (Block c)
    | Block c2 => Some (Block (Conc.Seq c c2))
    | Seq i j => match seq1 c i with
      | Some i => Some (Seq i j)
      | None => None
      end
    | For _ _ _ => None 
    end.

  Definition seq2 (c:Conc.inst) (a:phased) :=
    match a with
    | OnlyUnsync c2 => Some (OnlyUnsync (Conc.Seq c c2))
    | SyncUnsync i c2 =>
      match seq1 c i with
      | Some i => Some (SyncUnsync i c2)
      | None => None
      end
    end.

  Definition seq3 (n:inst) (a:phased) :=
    match a with
    | OnlyUnsync c2 => SyncUnsync n c2
    | SyncUnsync n2 c2 => SyncUnsync (Seq n n2) c2
    end.

  Definition seq (a1 a2: phased) : option phased :=
    match a1 with
    | OnlyUnsync c1 => seq2 c1 a2
    | SyncUnsync n c1 =>
      match seq2 c1 a2 with
      | Some p => Some (seq3 n p)
      | None => None
      end 
    end.

  Fixpoint i_subst x v (i:inst) :=
    match i with
    | Sync => Sync
    | Block c => Block (Conc.i_subst x v c)
    | Seq i j => Seq (i_subst x v i) (i_subst x v j)
    | For y r i =>
      let i' := if VAR.eq_dec x y then i else i_subst x v i in
      For y (r_subst x v r) i'
    end.

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

  Lemma in_phase2_seq3_l:
    forall a n i p,
    InPhase a n i ->
    InPhase2 a n (seq3 i p).
  Proof.
    intros.
    destruct p as [j c | c]; simpl.
    - left.
      auto using in_phase_seq_l.
    - auto.
  Qed.

  Lemma in_phase2_seq3_r:
    forall i p a m n,
    Phase i n ->
    InPhase2 a m p ->
    InPhase2 a (n + m) (seq3 i p).
  Proof.
    intros.
    destruct p as [j c| c]; simpl in *.
    - destruct H0 as [Hi | (Hp, Hi)].
      + left.
        eapply in_phase_seq_r; eauto.
      + subst.
        right.
        eexists.
        repeat split.
        * eapply phase_seq; eauto.
        * auto.
    - destruct H0 as (?, Hi).
      subst.
      rewrite PeanoNat.Nat.add_0_r.
      auto.
  Qed.

  Lemma in_phase_seq1_l:
    forall a c i j,
    Conc.IIn a c ->
    seq1 c i = Some j ->
    InPhase a 0 j.
  Proof.
    induction i; intros; simpl in *; inversion H0; subst; clear H0.
    - constructor; auto.
    - apply in_phase_block.
      apply Conc.i_in_seq_l.
      assumption.
    - destruct (seq1 c i1) eqn:R1; inversion H2; subst; clear H2.
      apply in_phase_seq_l.
      auto.
  Qed.

  Lemma in_phase_seq1_r:
    forall i n a c j j',
    Phase i n ->
    Conc.IIn a c ->
    seq1 c j = Some j' ->
    InPhase a n (Seq i j').
  Proof.
    induction j; intros; simpl in *; inversion H1; subst; clear H1.
    - eapply in_phase_seq_r; eauto using in_phase_block.
    - eapply in_phase_seq_r; eauto.
      apply in_phase_block.
      apply Conc.i_in_seq_l.
      assumption.
    - destruct (seq1 c j1) as [j1'|] eqn:R; inversion H3; subst; clear H3.
      eapply in_phase_seq_r; eauto.
      apply in_phase_seq_l.
      eauto using in_phase_seq1_l.
  Qed.


  Lemma in_phase2_seq2_l:
    forall a c i j,
    Conc.IIn a c ->
    seq2 c i = Some j ->
    InPhase2 a 0 j.
  Proof.
    intros a c [i c'| c'] j Hi Heq; simpl in *.
    - destruct (seq1 c i) as [i' |] eqn:Hr; inversion Heq; subst; clear Heq.
      simpl.
      left.
      eapply in_phase_seq1_l; eauto.
    - inversion Heq; subst; clear Heq.
      simpl.
      split; auto.
      apply Conc.i_in_seq_l.
      assumption.
  Qed.

  Lemma phase2_seq3:
    forall i n1 n2 o p,
    Phase i n1 ->
    Phase2 p n2 ->
    o = n1 + n2 ->
    Phase2 (seq3 i p) o.
  Proof.
    intros.
    destruct p as [j c|c]; simpl in *; subst.
    - eauto using phase_seq.
    - rewrite PeanoNat.Nat.add_0_r.
      assumption.
  Qed.

  Lemma phase_seq1:
    forall i n,
    Phase i n ->
    forall c j,
    seq1 c i = Some j ->
    Phase j n.
  Proof.
    intros i n H.
    induction H; intros; simpl in *.
    - inversion H; subst; clear H.
      apply phase_block.
    - inversion H; subst; clear H.
      apply phase_block.
    - destruct (seq1 c i) as [o'|] eqn:R.
      inversion H2; subst; clear H2.
      + eauto using phase_seq.
      + inversion H2.
    - inversion H5.
    - inversion H2.
  Qed.

  Lemma phase2_seq2:
    forall c p n p',
    Phase2 p n ->
    seq2 c p = Some p' ->
    Phase2 p' n.
  Proof.
    intros.
    destruct p; simpl in *.
    - destruct (seq1 c i) eqn:R1.
      + inversion H0; subst; clear H0.
        simpl.
        eapply phase_seq1;eauto.
      + inversion H0.
    - subst.
      inversion H0; subst; clear H0.
      simpl.
      reflexivity.
  Qed.

  Lemma phase2_seq:
    forall p1 p2 n1 n2 o p,
    Phase2 p1 n1 ->
    Phase2 p2 n2 ->
    o = n1 + n2 ->
    seq p1 p2 = Some p ->
    Phase2 p o.
  Proof.
    intros.
    destruct p1 as [i c|c]; simpl in *.
    - destruct (seq2 c p2) as [o' |] eqn:R; inversion H2; subst; clear H2.
      eapply phase2_seq3; eauto.
      eapply phase2_seq2; eauto.
    - subst.
      simpl.
      eapply phase2_seq2; eauto.
  Qed.

  Lemma translate_subst:
    forall i j c,
    translate i = Some (SyncUnsync j c) ->
    forall x v,
    translate (ALang.i_subst x v i) =
    Some (SyncUnsync (i_subst x v j) (Conc.i_subst x v c)).
  Proof.
    intros.
    induction i; intros; simpl; inversion H; subst; simpl; clear H.
    - reflexivity.
    - simpl in 
  Qed.
  Lemma phase_to_phase2:
    forall i n,
    ALang.Phase i n ->
    forall p,
    translate i = Some p ->
    Phase2 p n.
  Proof.
    intros i n H.
    induction H;
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