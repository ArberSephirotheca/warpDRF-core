Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Coq.omega.Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Util.
Require Import Tasks.
Require Hist.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip: inst
  | If: bexp -> inst -> inst -> inst
  | Seq: inst -> inst -> inst
  | MemAcc: access_exp -> inst
  | For : var -> range -> inst -> inst
  .

  Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | If b i j => If (b_subst x v b) (i_subst x v i) (i_subst x v j)
  | Seq i j => Seq (i_subst x v i) (i_subst x v j)
  | MemAcc a => MemAcc (access_subst x v a)  
  | For y r i =>
    let i' := if VAR.eq_dec x y then i else i_subst x v i in
    For y (r_subst x v r) i'
  end.

  Import Hist.

  Notation history := (list access_val).

  Fixpoint In (x:var) i :=
  match i with
  | Skip => False
  | MemAcc e => access_in x e
  | If b i j => BIn x b \/ In x i \/ In x j
  | Seq i j => In x i \/ In x j
  | For y r i => x = y \/ RIn x r \/ In x i
  end.

  Fixpoint Var x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => Var x i \/ Var x j
  | For y _ i (*| Loop y _ i*) => x = y \/ Var x i
  end.

  Fixpoint InRange x i :=
  match i with
  | Skip | MemAcc _ => False
  | If _ i j | Seq i j => InRange x i \/ InRange x j
  | For _ r i => RIn x r \/ InRange x i
  end.

  Infix ";;" := Seq (at level 50).

  Lemma i_subst_seq:
    forall x n i1 i2,
    i_subst x n (i1 ;; i2) = i_subst x n i1 ;; i_subst x n i2.
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma i_subst_inv_seq:
    forall x v k i j,
    i_subst x v k = Seq i j ->
    exists i' j',
    k = Seq i' j' /\
    i = i_subst x v i' /\
    j = i_subst x v j'.
  Proof.
    destruct k; simpl; intros i j H; inversion H; subst; clear H.
    eauto.
  Qed.

  Lemma i_subst_subst_eq:
    forall x i n1 n2,
    i_subst x (NNum n1) (i_subst x (NNum n2) i) = i_subst x (NNum n2) i.
  Proof.
    induction i; simpl; intros.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_eq.
      reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_eq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        rewrite r_subst_subst_eq.
        reflexivity.
      }
      rewrite IHi.
      rewrite r_subst_subst_eq.
      reflexivity.
  Qed.

  Lemma i_subst_subst_eq_2
     : forall (x : var) i (v e : nexp),
       ~ NIn x v -> i_subst x e (i_subst x v i) = i_subst x v i.
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite b_subst_subst_eq_2; auto.
      rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite IHi1; auto; rewrite IHi2; auto.
    - rewrite access_subst_subst_eq_2; auto.
    - rewrite r_subst_subst_eq_2; auto.
      destruct (Set_VAR.MF.eq_dec x v). { reflexivity. }
      rewrite IHi; auto.
  Qed.

  Lemma i_subst_subst_neq:
    forall x y i n1 n2,
    x <> y ->
    i_subst x (NNum n1) (i_subst y (NNum n2) i) =
    i_subst y (NNum n2) (i_subst x (NNum n1) i).
  Proof.
    induction i; intros; simpl.
    - reflexivity.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
      rewrite b_subst_subst_neq; auto.
    - rewrite IHi1; auto.
      rewrite IHi2; auto.
    - rewrite access_subst_subst_neq; auto.
    - destruct (Set_VAR.MF.eq_dec x v). {
        destruct (Set_VAR.MF.eq_dec y v). {
          subst.
          contradiction.
        }
        rewrite r_subst_subst_neq; auto.
      }
      destruct (Set_VAR.MF.eq_dec y v). {
        subst.
        rewrite r_subst_subst_neq; auto.
      }
      rewrite IHi; auto.
      rewrite r_subst_subst_neq; auto.
  Qed.

  Lemma var_subst_inv_1:
    forall y x n i,
    Var y (i_subst x (NNum n) i) ->
    Var y i.
  Proof.
    induction i; simpl; intros; auto; destruct H; auto.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_range_subst_inv_1:
    forall y x n i,
    InRange y (i_subst x (NNum n) i) ->
    InRange y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_r_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  Lemma in_subst_inv_1:
    forall y x n i,
    In y (i_subst x (NNum n) i) ->
    In y i.
  Proof.
    induction i; simpl; intros; auto; try (destruct H; auto).
    - apply in_b_subst_neq in H; auto.
      intros N.
      inversion N.
    - destruct H; auto.
    - eapply access_in_subst_neq; eauto.
      intros N.
      inversion N.
    - destruct H; auto.
      + apply in_r_subst_neq in H; eauto.
        intros N.
        inversion N.
      + destruct (Set_VAR.MF.eq_dec x v); auto.
  Qed.

  (** Parallelize an access for [n] tasks. *)

  Context `{T:Tasks}.
  Inductive Run (n:nat) : inst -> history -> Prop :=
  | run_skip:
    Run n Skip []
  | run_access:
    forall e v,
    access_step (e, NNum n) v ->
    Run n (MemAcc e) v
  | run_seq:
    forall i j h1 h2,
    Run n i h1 ->
    Run n j h2 ->
    Run n (Seq i j) (h1 ++ h2)
  | run_if:
    forall i j e b hi hj,
    BStep e b ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) (if b then hi else hj)
  
  | run_for_cons:
    forall e1 e2 n1 n2 i x h1 h2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run n (i_subst x (NNum n1) i) h1 ->
    Run n (For x (NNum (S n1), NNum n2) i) h2 ->
    Run n (For x (e1, e2) i) (h1 ++ h2)
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run n (For x (e1, e2) i) []
  .

  Lemma run_if_true:
    forall e n i j hi hj,
    BStep e true ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) hi.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Lemma run_if_false:
    forall e n i j hi hj,
    BStep e false ->
    Run n i hi ->
    Run n j hj ->
    Run n (If e i j) hj.
  Proof.
    intros.
    eapply run_if with (i:=i) (j:=j) in H1; eauto.
    assumption.
  Qed.

  Definition REq i1 i2 :=
   forall n h,
   Run n i1 h <-> Run n i2 h.

  Import Morphisms.
(*
  Lemma r_eq_proper_1:
    forall n b b' i j h,
    BEq b b' ->
    Run n (If b i j) h ->
    Run n (If b' i j) h.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    rewrite H in H4.
    eauto using run_if.
  Qed.

  Global Instance r_eq_proper_2: Proper (BEq ==> eq ==> eq ==> REq) If.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    + eapply r_eq_proper_1; eauto.
    + symmetry in H.
      eapply r_eq_proper_1; eauto.
  Qed.
(*
  Lemma r_eq_proper_3:
    forall x e1 e2 i h e1' e2' n,
    NEq e1 e1' ->
    NEq e2 e2' ->
    Run n (For x (e1, e2) i) h ->
    Run n (For x (e1', e2') i) h.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply run_for.
    inversion H7; subst; clear H7.
    apply run_if; auto.
    + eapply b_eq_proper_4; eauto.
    + inversion H6; subst; clear H6.
      apply run_seq.
      * eapply run_seq.
    eapply r_eq_proper_1; eauto.
    - 
    rewrite H in H7.
  Qed.

  Global Instance r_eq_proper_1: Proper (eq ==> NEq * NEq ==> eq ==> REq) For.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    + destruct x0 as (e1, e2).
      destruct y0 as (e1', e2').
      destruct H0 as (Ha, Hb).
      unfold RelCompFun in *.
      simpl in *.
  Qed.
*)
(*
  Lemma r_eq_proper_3:
    forall n i v v' x h,
    Run n (i_subst x v i) h ->
    NEq v v' ->
    Run n (i_subst x v' i) h.
  Proof.
    induction i; simpl; intros; inversion H; subst; clear H.
    - constructor.
    - apply run_if; eauto.
      rewrite <- H0.
      assumption.
    - apply run_seq; eauto.
    - apply run_access.
      eapply access_step_proper; eauto.
      + apply access_subst_proper; auto.
      + reflexivity.
    - destruct r as (e1', e2').
      simpl in *.
      inversion H3; subst; clear H3.
      apply run_for.
      inversion H5; subst; clear H5.
      inversion H6; subst; clear H6.
      apply run_if; auto. {
        rewrite <- H0.
        assumption.
      }
      apply run_seq. {
        destruct (Set_VAR.MF.eq_dec x v). {
          eapply IHi; eauto.
          rewrite H0.
          reflexivity.
        }
        admit.
      }
      destruct (Set_VAR.MF.eq_dec x v). {
        subst.
        
  Qed.
*)
  Lemma r_eq_proper_3:
    forall n i h,
    Run n i h ->
    forall e v v' x,
    NEq v v' ->
    i = i_subst x v e ->
    Run n (i_subst x v' e) h.
  Proof.
    intros n i h H.
    induction H; intros.
    - destruct e; inversion H0.
      simpl in *.
      apply run_skip.
    - destruct e0; simpl in *; inversion H1; subst; clear H1.
      apply run_access.
      eapply access_step_proper; eauto.
      + apply access_subst_proper; auto.
      + reflexivity.
    - destruct e; simpl in *; inversion H2; subst; clear H2.
      eauto using run_seq.
    - destruct e0; simpl in *; inversion H3; subst; clear H3.
      apply run_if; eauto.
      eapply b_eq_proper_6; eauto.
    - assert (IHRun := IHRun (If (NRel NLt e1 e2)
          (i_subst x e1 i;; For x (NBin NPlus (NNum 1) e1, e2) i) Skip) v v' x H0).
      simpl in IHRun.
      destruct (Set_VAR.MF.eq_dec x x) as [_|N]; try contradiction.
      assert (Hn: exists n1 n2, NStep e1 n1 /\ NStep e2 n2). {
        inversion H; subst; clear H.
        inversion H5; subst; clear H5.
        eauto.
      }
      destruct Hn as (n1, (n2, (Hn1, Hn2))).
      rewrite n_subst_not_in in IHRun; eauto using n_step_to_not_in.
      rewrite n_subst_not_in in IHRun; eauto using n_step_to_not_in.
      rewrite i_subst_subst_eq_2 in IHRun; eauto using n_step_to_not_in.
      assert (IHRun := IHRun eq_refl).
      destruct e; simpl in *; inversion H1; subst; clear H1.
      destruct r as (e1', e2').
      simpl in *.
      inversion H4; subst; clear H4.
      apply run_for.
      destruct (Set_VAR.MF.eq_dec x0 v0). {
        subst.
        apply r_eq_proper_1 with (b:=(NRel NLt (n_subst v0 v' (n_subst v0 v e1'))
                (n_subst v0 v' (n_subst v0 v e2')))); auto. {
          rewrite n_eq_subst_subst; eauto.
          rewrite n_eq_subst_subst; eauto.
          reflexivity.
        }
        inversion IHRun; subst; clear IHRun.
        apply run_if; auto.
        inversion H6; subst; clear H6.
        inversion H; subst; clear H.
        inversion H10; subst; clear H10.
        inversion H11; subst; clear H11.
        
        assert (hj0 = hj) by eauto using run_fun.
        apply run_seq.
        - 
          
        rewrite i_subst_subst_eq_2 in IHRun; eauto using n_step_to_not_in.
        apply n_step_inv_subst in Hn1.
        apply n_step_inv_subst in Hn2.
        destruct Hn2 as [Hn2|Hn2], Hn1 as [Hn1|Hn1].
        - rewrite n_subst_not_in with (x:=v0) (n:=e1') in *; auto.
          rewrite n_subst_not_in with (x:=v0) (n:=e2') in *; auto.
        - rewrite n_subst_not_in with (x:=v0) (n:=e2') in *; auto.
          destruct Hn1 as (vn, Hn1).
          assert (NStep v' vn) by (apply H0; auto).
          rewrite n_subst_not_in in IHRun; eauto using n_step_to_not_in, n_in_subst_eq.
          2: { admit. }
          rewrite n_subst_not_in in IHRun; eauto using n_step_to_not_in, n_in_subst_eq.
          rewrite n_subst_not_in in IHRun; eauto using n_step_to_not_in.
          rewrite i_subst_subst_eq_2 in IHRun; eauto using n_step_to_not_in.
      }
  Qed.
*)
(*
  Lemma r_eq_proper_3:
    forall e n v v' x h,
    NEq v v' ->
    Run n (i_subst x v e) h ->
    Run n (i_subst x v' e) h.
  Proof.
    intros.
    induction e; simpl; intros.
    - assumption.
    - inversion H0; subst; clear H0.
      rewrite H in H4.
      eauto using run_if.
    - inversion H0; subst; clear H0; eauto using run_seq.
    - inversion H0; subst; clear H0.
      apply run_access.
      eapply access_step_proper; eauto.
      + apply access_subst_proper; auto.
      + reflexivity.
    - inversion H0; subst; clear H0.
      destruct r as (e1', e2').
      simpl in *.
      inversion H3; subst; clear H3.
  Qed.

  Import Morphisms.
  Global Instance r_eq_proper_1: Proper (eq ==> NEq ==> eq ==> REq) i_subst.
  Proof.
    unfold Proper, respectful.
    split; intros; subst.
    + rename x0 into v.
      rename y0 into v'.
  Qed.
*)
(*
  Lemma run_for_cons:
    forall n e1 e2 n1 n2 i x h1 h2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    Run n (i_subst x (NNum n1) i) h1 ->
    Run n (For x (NNum (S n1), NNum n2) i) h2 ->
    Run n (For x (e1, e2) i) (h1 ++ h2).
  Proof.
    intros.
    apply run_for.
    eapply run_if_true; eauto using run_skip.
    - eapply b_step_lt; eauto.
    - apply run_seq.
      + clear H1 H3. clear H0. 
  Qed.
*)
(*
  | run_for_nil:
    forall x i e1 e2 n1 n2,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 >= n2 ->
    Run n (For x (e1, e2) i) []
*)
  Inductive RunAll : nat -> inst -> history -> Prop :=
  | run_all_zero:
    forall i,
    RunAll 0 i []
  | run_all_succ:
    forall i n h1 h2,
    Run n (i_subst TID (NNum n) i) h1 ->
    RunAll n i h2 ->
    RunAll (S n) i (h1 ++ h2).

  Inductive IIn (a:access_val) : inst -> Prop :=
  | i_in_access:
    forall e,
    AIn a e ->
    IIn a (MemAcc e)
  | i_in_if_true:
    forall b i j,
    BData (access_tid a) b true ->
    IIn a i ->
    IIn a (If b i j)
  | i_in_if_false:
    forall b i j,
    BData (access_tid a) b false ->
    IIn a j ->
    IIn a (If b i j)
  | i_in_seq_l:
    forall i j,
    IIn a i ->
    IIn a (Seq i j)
  | i_in_seq_r:
    forall i j,
    IIn a j ->
    IIn a (Seq i j)
  | i_in_for:
    forall i r x n1 n n2,
    RData (access_tid a) r (n1, n2) ->
    n1 <= n < n2 ->
    IIn a (i_subst x (NNum n) i) ->
    IIn a (For x r i)
  .

  Inductive Run2 (n1 n2:nat): inst -> history -> history -> Prop :=
  | run2_skip:
    Run2 n1 n2 Skip [] []

  | run2_access:
    forall e v1 v2,
    access_step (access_subst TID (NNum n1) e, NNum n1) v1 ->
    access_step (access_subst TID (NNum n2) e, NNum n2) v2 ->
    Run2 n1 n2 (MemAcc e) v1 v2

  | run2_seq:
    forall i j hi1 hj1 hi2 hj2,
    Run2 n1 n2 i hi1 hi2 ->
    Run2 n1 n2 j hj1 hj2 ->
    Run2 n1 n2 (Seq i j) (hi1 ++ hj1) (hi2 ++ hj2)

  | run2_if:
    forall i j b b1 b2 hi1 hi2 hj1 hj2,
    BData n1 b b1 ->
    BData n2 b b2 ->
    Run2 n1 n2 i hi1 hi2 ->
    Run2 n1 n2 j hj1 hj2 ->
    Run2 n1 n2 (If b i j) (if b1 then hi1 else hj1) (if b2 then hi2 else hj2)

  | run2_for:
    forall e1 e2 i x n1_1 n1_2 n2_1 n2_2 h1_1 h1_2 h2_1 h2_2,
    RData n1 (e1,e2) (n1_1,n2_1) ->
    RData n2 (e1,e2) (n1_2,n2_2) ->
    Run2 n1 n2 (i_subst x e1 i) h1_1 h1_2 ->
    Run2 n1 n2 (For x (NBin NPlus (NNum 1) e1, e2) i) h2_1 h2_2 ->
    Run2 n1 n2 (For x (e1, e2) i)
      (if leb n1_1 n2_1 then (h1_1 ++ h1_2) else [])
      (if leb n1_2 n2_2 then (h1_2 ++ h2_2) else []).

  Definition HasIter t1 t2 r : Prop :=
    exists n1 n2 n3 n4,
    RData t1 r (n1, n2) /\
    RData t2 r (n3, n4) /\
    (n1 < n2 \/ n3 < n3).

  Definition IsDone t1 t2 r : Prop :=
    exists n1 n2 n3 n4,
    RData t1 r (n1, n2) /\
    RData t2 r (n3, n4) /\
    n1 >= n2 /\
    n3 >= n4.

  Inductive PRun2 (n1 n2:nat): bexp -> inst -> history -> history -> Prop :=
  | p_run2_skip p:
    PRun2 n1 n2 p Skip [] []

  | p_run2_access p:
    forall e v1 v2 b1 b2,
    BData n1 p b1 ->
    BData n2 p b2 ->
    access_step (access_subst TID (NNum n1) e, NNum n1) v1 ->
    access_step (access_subst TID (NNum n2) e, NNum n2) v2 ->
    PRun2 n1 n2 p (MemAcc e) (if b1 then v1 else []) (if b2 then v2 else [])

  | p_run2_seq p:
    forall i j hi1 hj1 hi2 hj2,
    PRun2 n1 n2 p i hi1 hi2 ->
    PRun2 n1 n2 p j hj1 hj2 ->
    PRun2 n1 n2 p (Seq i j) (hi1 ++ hj1) (hi2 ++ hj2)

  | p_run2_if p:
    forall i j b hi1 hi2 hj1 hj2,
    PRun2 n1 n2 (BRel BAnd b p) i hi1 hi2 ->
    PRun2 n1 n2 (BRel BAnd (BNot b) p) j hj1 hj2 ->
    PRun2 n1 n2 p (If b i j) (hi1 ++ hj1) (hi2 ++ hj2)

  | p_run2_for_cons p:
    forall e1 e2 i x h1_1 h1_2 h2_1 h2_2,
    HasIter n1 n2 (e1, e2) ->
    PRun2 n1 n2 (BRel BAnd (NRel NLt e1 e2) p) (i_subst x e1 i) h1_1 h1_2 ->
    PRun2 n1 n2 (BRel BAnd (NRel NLe e2 e1) p) (For x (NBin NPlus (NNum 1) e1, e2) i) h2_1 h2_2 ->
    PRun2 n1 n2 p (For x (e1, e2) i)
      (h1_1 ++ h1_2)
      (h1_2 ++ h2_2)

  | p_run2_for_nil p:
    forall r i x,
    IsDone n1 n2 r ->
    PRun2 n1 n2 p (For x r i) [] [].

  Lemma run_all_inv_in:
    forall n i h,
    RunAll n i h ->
    forall x,
    List.In x h ->
    exists m h',
    m < n /\ Run m (i_subst TID (NNum m )i) h' /\ incl h' h /\ List.In x h'.
  Proof.
    intros n i h H.
    induction H; intros. { contradiction. }
    apply in_app_or in H1.
    destruct H1.
    - exists n.
      exists h1.
      eauto using InUtil.incl_app_refl_l with *.
    - edestruct IHRunAll as (m, (h, (Hl, (Hr, (Hi,Hj))))); eauto.
      exists m.
      exists h.
      auto using incl_appr with *.
  Qed.

  Inductive SRun n: inst -> history -> Prop :=
  | s_run_skip:
    SRun n Skip []
  | s_run_access:
    forall e v,
    access_step (access_subst TID (NNum n) e, NNum n) v ->
    SRun n (MemAcc e) v
  | s_run_seq:
    forall i j h1 h2,
    SRun n i h1 ->
    SRun n j h2 ->
    SRun n (Seq i j) (h1 ++ h2)
  | s_run_if:
    forall e i j b hi hj,
    BData n e b ->
    SRun n i hi ->
    SRun n j hj ->
    SRun n (If e i j) (if b then hi else hj)
  | s_run_for_cons:
    forall e1 e2 n1 n2 x i h1 h2,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 < n2 ->
    SRun n (i_subst x (NNum n1) i) h1 ->
    SRun n (For x (NNum (S n1), NNum n2) i) h2 ->
    SRun n (For x (e1, e2) i) (h1 ++ h2) 
  | s_run_for_nil:
    forall e1 e2 n1 n2 x i,
    NData n e1 n1 ->
    NData n e2 n2 ->
    n1 >= n2 ->
    SRun n (For x (e1, e2) i) []
  .

  Lemma run_to_s_run:
    forall n i h,
    Run n (i_subst TID (NNum n) i) h ->
    ~ Var TID i ->
    SRun n i h.
  Proof.
    intros n i h Hr.
    remember (i_subst _ _ _) as j.
    generalize dependent i.
    induction Hr; simpl; intros; symmetry in Heqj.
    - destruct i; inversion Heqj.
      apply s_run_skip.
    - destruct i; inversion Heqj; subst; clear Heqj.
      auto using s_run_access.
    - apply i_subst_inv_seq in Heqj.
      destruct Heqj as (i', (j', (?, (?,?)))).
      subst.
      simpl in H.
      eapply s_run_seq; eauto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      simpl in *.
      apply s_run_if; auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (r1, r2).
      simpl in *.
      inversion H5; subst; clear H5.
      eapply s_run_for_cons.
      + eauto.
      + eauto.
      + assumption.
      + apply IHHr1; auto.
        * destruct (Set_VAR.MF.eq_dec TID x). {
            assert (TID <> x) by auto.
            contradiction.
          }
          rewrite i_subst_subst_neq; auto.
        * intros N.
          apply var_subst_inv_1 in N.
          auto.
      + auto.
    - destruct i0; inversion Heqj; subst; clear Heqj.
      destruct r as (r1, r2).
      simpl in *.
      inversion H5; subst; clear H5.
      eapply s_run_for_nil; eauto.
  Qed.

  Lemma s_run_to_run:
    forall n i h,
    SRun n i h ->
    ~ Var TID i ->
    Run n (i_subst TID (NNum n) i) h.
  Proof.
    intros n i h H.
    induction H; simpl; intros.
    - apply run_skip.
    - auto using run_access.
    - apply run_seq; eauto.
    - apply run_if; auto.
    - assert (TID <> x) by auto.
      remove_eq TID x.
      eapply run_for_cons; eauto.
      + rewrite i_subst_subst_neq; auto.
        apply IHSRun1.
        intros N.
        apply var_subst_inv_1 in N.
        auto.
      + remove_eq TID x.
        apply IHSRun2.
        auto.
    - assert (TID <> x) by auto.
      remove_eq TID x.
      eapply run_for_nil; eauto.
  Qed.

  Lemma s_run_iff:
    forall i,
    ~ Var TID i ->
    forall n h,
    Run n (i_subst TID (NNum n) i) h <-> SRun n i h.
  Proof.
    split; intros; auto using s_run_to_run, run_to_s_run.
  Qed.

  Lemma s_run_access_tid:
    forall m i h,
    SRun m i h ->
    forall a,
    List.In a h ->
    access_tid a = m.
  Proof.
    intros m i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - eapply access_step_inv_in_eq in H; eauto.
    - apply in_app_iff in Hi.
      destruct Hi as [Hi|Hi]; auto.
    - destruct b; auto.
    - apply in_app_iff in Hi.
      destruct Hi; auto.
    - contradiction.
  Qed.

  Lemma run_access_tid:
    forall i,
    ~ Var TID i ->
    forall m h,
    Run m (i_subst TID (NNum m) i) h ->
    forall a,
    List.In a h ->
    access_tid a = m.
  Proof.
    intros i Hv m h Hr.
    apply s_run_iff in Hr; eauto using s_run_access_tid.
  Qed.

  Lemma s_run_i_in:
    forall m i h,
    SRun m i h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros m i h Hr.
    induction Hr; intros a Hi.
    - contradiction.
    - apply i_in_access.
      unfold AIn.
      exists v.
      erewrite access_step_inv_in_eq; eauto.
    - apply in_app_iff in Hi.
      destruct Hi; eauto using i_in_seq_l, i_in_seq_r.
    - destruct b.
      + apply i_in_if_true; auto.
        unfold BData in *.
        erewrite s_run_access_tid with (i:=i); eauto.
      + apply i_in_if_false; auto.
        unfold BData in *.
        erewrite s_run_access_tid with (i:=j); eauto.
    - apply in_app_iff in Hi.
      destruct Hi.
      + apply i_in_for with (n1:=n1) (n2:=n2) (n:=n1); auto.
        assert (R: access_tid a = m). { eauto using s_run_access_tid. }
        rewrite R.
        split; auto.
      + assert (Hi := H2).
        apply IHHr2 in H2.
        inversion H2; subst; clear H2.
        destruct H6 as (Ha, Hb).
        assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
        assert (n3 = n2) by eauto using n_step_fun, n_step_num.
        subst.
        apply i_in_for with (n1:=n1) (n:=n) (n2:=n2); auto with *.
        assert (R: access_tid a = m). { eauto using s_run_access_tid. }
        rewrite R.
        split; auto.
    - contradiction.
  Qed.

  Lemma in_to_i_in:
    forall i,
    ~ Var TID i ->
    forall m h,
    Run m (i_subst TID (NNum m) i) h ->
    forall a,
    List.In a h ->
    IIn a i.
  Proof.
    intros i Hv m h Hr.
    apply s_run_iff in Hr; eauto using s_run_i_in.
  Qed.

  Lemma s_run_i_in_to_in:
    forall m i h,
    SRun m i h ->
    forall a,
    access_tid a = m ->
    IIn a i ->
    List.In a h.
  Proof.
    intros m i h Hr.
    induction Hr; intros a He Hi; inversion Hi; subst; clear Hi.
    - unfold AIn in *.
      destruct H1 as (l', (Hs, Hi)).
      assert (l' = v) by eauto using access_step_fun.
      subst.
      assumption.
    - apply in_app_iff.
      auto.
    - apply in_app_iff.
      auto.
    - assert (b = true) by eauto using b_step_fun.
      subst.
      eauto.
    - assert (b = false) by eauto using b_step_fun.
      subst.
      eauto.
    - apply in_app_iff.
      destruct H5 as (Hn1, Hn2).
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      assert (Hn: n1 = n \/ n1 < n). {
        assert (Hn: n1 <= n) by auto with *.
        inversion Hn; subst; clear Hn; auto with *.
      }
      destruct Hn. { subst. eauto. }
      apply i_in_for with (r:=(NNum (S n1), NNum n2)) (n1:=S n1) (n2:=n2) in H7; auto with *.
      split; apply n_step_num.
    - destruct H5 as (Hn1, Hn2).
      assert (n0 = n1) by eauto using n_step_fun.
      assert (n3 = n2) by eauto using n_step_fun.
      subst.
      Import Omega.
      omega.
  Qed.

  Lemma s_run_i_in_iff:
    forall m i h,
    SRun m i h ->
    forall a,
    access_tid a = m ->
    IIn a i <-> List.In a h.
  Proof.
    intros.
    split; eauto using s_run_i_in_to_in, s_run_i_in.
  Qed.

End C1.
