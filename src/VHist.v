Require Import Coq.Lists.List.

Require Import AccExp.
Require Import PairInUtil.
Import ListNotations.

(*
  A non-empty vector of histories.
  *)

Section Defs.
  Context {A:Access}.

  Notation history := (list access_val).

  Inductive vhist :=
  | v_one: history -> vhist
  | v_cons: history -> vhist -> vhist
  .

  Definition first (v:vhist) :=
    match v with
    | v_one h
    | v_cons h _ => h
    end.

  Fixpoint last (v:vhist) :=
   match v with
   | v_one h => h
   | v_cons _ v => last v
   end.

  Fixpoint In h p :=
    match p with
    | v_one h' => h' = h
    | v_cons h' p => h' = h \/ In h p
    end.

  Definition v_prefix h p :=
    match p with
    | v_one h' => v_one (h ++ h')
    | v_cons h' p => v_cons (h ++ h') p
    end.

  Fixpoint v_seq p1 p2 :=
    match p1 with
    | v_one h1 => v_prefix h1 p2 
    | v_cons h1 p1 => v_cons h1 (v_seq p1 p2)
    end.

  Fixpoint v_app p1 p2 :=
    match p1 with
    | v_one h1 => v_cons h1 p2
    | v_cons h1 p1 => v_cons h1 (v_app p1 p2)
    end. 

  Fixpoint MIn (a:access_val) (p:vhist) : Prop :=
    match p with
    | v_one h => List.In a h
    | v_cons h p => List.In a h \/ MIn a p
    end.

  Fixpoint MPairIn (p:access_val*access_val) (m:vhist) : Prop :=
    match m with
    | v_one h => PairIn p h
    | v_cons h v => PairIn p h \/ MPairIn p v
    end.

  Fixpoint vhist_to_list (p:vhist) : list history :=
    match p with
    | v_one h => [h]
    | v_cons h m => h :: vhist_to_list m
    end.

  Definition MOneOf (p:access_val*access_val) h1 h2 :=
    let (v1, v2) := p in
    (List.In v1 h1 /\ List.In v2 h2)
    \/
    (List.In v2 h1 /\ List.In v1 h2).


  Lemma m_pair_in_inv_v_app:
    forall p m1 m2,
    MPairIn p (v_app m1 m2) ->
    MPairIn p m1 \/ MPairIn p m2.
  Proof.
    induction m1; intros; simpl in *.
    - intuition.
    - destruct H; try intuition.
      apply IHm1 in H.
      intuition.
  Qed.

  Lemma m_one_of_def_1:
    forall p h1 h2,
    List.In (fst p) h1 ->
    List.In (snd p) h2 ->
    MOneOf p h1 h2.
  Proof.
    intros.
    destruct p; simpl in *; auto.
  Qed.

  Lemma m_one_of_def_2:
    forall p h1 h2,
    List.In (fst p) h2 ->
    List.In (snd p) h1 ->
    MOneOf p h1 h2.
  Proof.
    intros.
    destruct p; simpl in *; auto.
  Qed.

  Lemma m_pair_in_inv_prefix:
    forall p v h,
    MPairIn p (v_prefix h v) ->
    PairIn p h \/ MPairIn p v \/ MOneOf p h (first v).
  Proof.
    induction v; intros; simpl in *. {
      apply pair_in_inv_app in H.
      destruct H as [H|[H|H]];
        intuition;
        auto using m_one_of_def_1, m_one_of_def_2.
    }
    destruct H as [H|H]; auto.
    apply pair_in_inv_app in H.
    destruct H as [H|[H|H]];
      intuition;
      auto using m_one_of_def_1, m_one_of_def_2.
  Qed.

  Lemma m_pair_in_inv_seq:
    forall p m1 m2,
    MPairIn p (v_seq m1 m2) ->
    MPairIn p m1 \/ MPairIn p m2 \/ MOneOf p (last m1) (first m2).
  Proof.
    induction m1; intros; simpl in *.
    - apply m_pair_in_inv_prefix in H.
      intuition.
    - intuition.
      apply IHm1 in H0.
      intuition.
  Qed.

  Lemma first_inv_in_prefix:
    forall a v h,
    List.In a (first (v_prefix h v)) ->
    List.In a h
    \/ List.In a (first v).
  Proof.
    induction v; simpl; intros; apply in_app_iff in H; auto.
  Qed.
 
  Lemma first_inv_in_seq:
    forall a v1 v2,
    List.In a (first (v_seq v1 v2)) ->
    List.In a (first v1)
    \/ exists h, v_one h = v1 /\ List.In a (first v2).
  Proof.
    induction v1; intros; simpl in *. {
      apply first_inv_in_prefix in H.
      intuition.
      eauto.
    }
    auto.
  Qed.

  Lemma v_seq_inv_one:
    forall v1 v2 h,
    v_seq v1 v2 = v_one h ->
    exists h1 h2,
    v1 = v_one h1 /\ v2 = v_one h2.
  Proof.
    induction v1; intros; simpl in *. {
      destruct v2. {
        eauto.
      }
      inversion H.
    }
    inversion H.
  Qed.
  
  Inductive InPhase (a:access_val) : nat -> vhist -> Prop :=
  | in_phase_eq_one:
    forall h,
    List.In a h ->
    InPhase a 0 (v_one h)
  | in_phase_eq_cons:
    forall h m,
    List.In a h ->
    InPhase a 0 (v_cons h m)
  | in_phase_cons:
    forall h m n,
    InPhase a n m ->
    InPhase a (S n) (v_cons h m).

  (* [h1;h2; h3] seq [h4; h5; h6] = [h1; h2; h3++h4; h5; h6] *)

  Goal
    (* Block c1 ; Block c2 where c1 produces h1 and c2 produces h2 *)
    forall h1 h2,
    v_seq (v_one h1) (v_one h2) = v_one (h1 ++ h2).
  Proof.
    reflexivity.
  Qed.

  Goal 
    (* Block c1 ; SYNC; Block c2 where c1 produces h1 and c2 produces h2 *)
    forall h1 h2,
    let v_sync := (v_cons [] (v_one [])) in
    v_seq (v_seq (v_one h1) v_sync) (v_one h2) =
    v_cons h1 (v_one h2).
  Proof.
    intros.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

End Defs.

Declare Scope vhist_scope.
Delimit Scope vhist_scope with vhist.

Infix "**" := v_cons (at level 60, right associativity) : vhist_scope.

Notation "{{ x }}" := (v_one x) : vhist_scope.

Infix "||" := v_app (left associativity, at level 50) : vhist_scope.

Infix "@" := v_seq (right associativity, at level 60) : vhist_scope.

Notation "{{ x | .. | y | z }}" := (v_cons x .. (v_cons y (v_one z)) ..) : vhist_scope.

