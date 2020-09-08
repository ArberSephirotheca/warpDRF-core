Require Import AccExp.
Require Import Tasks.
Require Import Conc.
Require Import NExp.
Require Import Var.
Require Import WLang.

Section Defs.
  Context `{T:Tasks}.
  Context {A:Access}.
  Inductive n_inst :=
  | NSync: Conc.inst -> n_inst
  | NSeq: n_inst -> n_inst -> n_inst
  | NFor : n_inst -> range -> (nexp -> n_inst) -> n_inst.

  Definition p_inst := (n_inst * Conc.inst) % type.


  Fixpoint c_seq (c1:Conc.inst) (c2:Conc.inst) :=
    match c1 with
    | Conc.Skip
    | Conc.If _ _ _
    | MemAcc _
    | For _ _ _
      => Conc.Seq c1 c2
    | Seq c1 c3 => c_seq c1 (c_seq c3 c2)
    end.

  Fixpoint w_seq (c:Conc.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (c_seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 r i => WFor (c_seq c c1) r i
   end.

  Fixpoint n_seq (c:Conc.inst) (n:n_inst) : n_inst :=
    match n with
    | NSync c' => NSync (c_seq c c')
    | NSeq i j => NSeq (n_seq c i) j
    | NFor i r j => NFor (n_seq c i) r j
    end.

  Lemma n_seq_seq:
    forall i c c',
    n_seq (Conc.Seq c c') i = n_seq c (n_seq c' i).
  Proof.
    induction i; intros.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHi1.
      auto.
    - simpl.
      rewrite IHi.
      reflexivity.
  Qed.

  Lemma c_seq_seq:
    forall c1 c2 c3,
    c_seq (c_seq c1 c2) c3 = c_seq c1 (c_seq c2 c3).
  Proof.
    induction c1; intros; simpl; auto.
    rewrite IHc1_1.
    rewrite IHc1_2.
    auto.
  Qed.

  Lemma n_seq_c_seq:
    forall i c1 c2,
    n_seq (c_seq c1 c2) i = n_seq c1 (n_seq c2 i).
  Proof.
    induction i; intros; simpl.
    - rewrite c_seq_seq.
      auto.
    - rewrite IHi1.
      auto.
    - rewrite IHi.
      auto.
  Qed.

  Definition p_seq (i:p_inst) (j:p_inst) :=
   match i, j with
    | (i,ci), (j, cj) => (NSeq i (n_seq ci j), cj)
    end.
(*
  Fixpoint i_subst x v i :=
    match i with
    | NSync c => NSync (Conc.i_subst x v c)
    | NSeq i2 i3 => NSeq (i_subst x v i2) (i_subst x v i3)
    | NFor i y r j =>
      let j' := if VAR.eq_dec x y then j else i_subst x v j in
      NFor (i_subst x v i) y (r_subst x v r) j'
    end.

  Definition p_subst x v (p:p_inst) :=
   match p with
    | (i, c) => (i_subst x v i, Conc.i_subst x v c)
    end.
*)
  Fixpoint tr (i:w_inst) : p_inst :=
    match i with
      (*
        [[ c ; sync ]] =  [ c, skip ]
        *) 
    | WSync c => (NSync c, Conc.Skip)
      (*
        [[ P; Q ]] = [[P]] ;; [[Q]]
        *) 
    | WSeq i j => p_seq (tr i) (tr j)
    | WFor c1 (e1, e2) f =>
      (*
      
      [[  c1; for x \in (e1, e2] { f = \x. (P, c2) } ]] =
        
        c1; P'(e1);
        for x \in (e1 + 1, e2) {
          c'(x - 1); c2 (x - 1); P'(x)
        }
        ,
        c'(e2 - 1); c2 (e2 - 1)
        
        
        where F = \x. [[ fst(f(x)) ]] = P', c'
            P' x = fst (F x)
       *)
      let i x := fst (tr (fst (f x))) in
      let c e := Conc.Seq (snd (tr (fst (f e)))) (snd (f e)) in
      (
        NFor
          (n_seq c1 (i e1))
          (NBin NPlus e1 (NNum 1), e2)
          (fun x =>
            n_seq (c (NBin NMinus x (NNum 1))) (i x)
          )
        ,
        c (NBin NMinus e2 (NNum 1))
      )
    end.


  (*  (a1, a2) \in P *)

  Inductive IPairIn (p:access_val*access_val) : n_inst -> Prop :=
  | i_pair_in_sync:
    (* 
       p \in c
       ------------
       p \in c;sync
      *)
    forall c,
    CPairIn p c ->
    IPairIn p (NSync c)
  | i_pair_in_seq_l:
    forall i j,
    IPairIn p i ->
    IPairIn p (NSeq i j)
  | i_pair_in_seq_r:
    forall i j,
    IPairIn p j ->
    IPairIn p (NSeq i j)
  | i_pair_in_for_1:
    forall r i j,
    IPairIn p i ->
    IPairIn p (NFor i r j)
  | i_pair_in_for_2:
    forall r n i j,
    RPick r n ->
    IPairIn p (j (NNum n)) ->
    IPairIn p (NFor i r j)
  .


  (*
    p \in P \/ p \in c 
    ------------------
    p \in [P, c]
    *)

  Definition PPairIn a (p:p_inst) : Prop :=
    match p with
    | (i, c) => IPairIn a i \/ CPairIn a c
    end.
(*
  Lemma i_pair_in_n_seq_l:
    forall p c i,
    CPairIn p c ->
    IPairIn p (n_seq c i).
  Proof.
    intros.
    induction i; simpl.
    - auto using i_pair_in_sync, c_pair_in_seq_l.
    - auto using i_pair_in_seq_l.
    - auto using i_pair_in_for_1.
  Qed.

  Lemma i_pair_in_i_seq_r:
    forall p c i,
    IPairIn p i ->
    IPairIn p (i_seq c i).
  Proof.
    intros.
    induction i; simpl; inversion H; subst; clear H.
    - auto using i_pair_in_sync, c_pair_in_seq_r.
    - auto using i_pair_in_seq_r, i_pair_in_seq_l.
    - auto using i_pair_in_seq_r.
    - auto using i_pair_in_for_1.
    - eauto using i_pair_in_for_2.
  Qed.

  Lemma p_pair_in_seq_l:
    forall p i j,
    PPairIn p i ->
    PPairIn p (seq i j).
  Proof.
    intros p (i, ci) (j, cj) Hi.
    simpl in *.
    destruct Hi as [Hi|Hi]. {
      auto using i_pair_in_seq_l.
    }
    eauto using i_pair_in_i_seq_l, i_pair_in_seq_r.
  Qed.

  Lemma p_pair_in_seq_r:
    forall p i j,
    PPairIn p j ->
    PPairIn p (seq i j).
  Proof.
    intros p (i, ci) (j, cj) Hi.
    simpl in *.
    destruct Hi as [Hi|Hi]; auto.
    left.
    auto using i_pair_in_seq_r, i_pair_in_i_seq_r.
  Qed.
  *)

  (*
  
   ---------------
    p \in [[ P ]]
  
    *)

  Inductive TPairIn a : w_inst -> Prop :=
  | t_pair_in_sync:
    forall c,
    CPairIn a c ->
    TPairIn a (WSync c)
  | t_pair_in_seq_l:
    forall i j,
    TPairIn a i ->
    TPairIn a (WSeq i j).

  Lemma tr_seq:
    forall i j c,
    tr i = (j, c) ->
    forall c',
    tr (w_seq c' i) = (n_seq c' j, c).
  Proof.
    induction i; intros; simpl in *.
    - inversion H; subst; clear H.
      simpl.
      reflexivity.
    - destruct (tr i1) as (j1, c1) eqn:R1.
      assert (IHi1 := IHi1 _ _ eq_refl c').
      destruct (tr i2) as (j2, c2) eqn:R2.
      assert (IHi2 := IHi2 _ _ eq_refl c').
      rewrite IHi1.
      simpl in *.
      inversion H; subst; clear H.
      simpl.
      reflexivity.
    - destruct r as (e1, e2).
      inversion H; subst; clear H.
      simpl.
      rewrite n_seq_c_seq.
      auto.
  Qed.

  Lemma snd_p_seq:
    forall i j,
    snd (p_seq i j) = snd j.
  Proof.
    intros (i, ci) (j, cj).
    destruct i; intros; simpl; auto.
  Qed.

  Inductive WF : w_inst -> Prop :=
  | wf_sync:
    forall c,
    WF (WSync c)
  | wf_seq:
    forall i j,
    WF i ->
    WF j ->
    WF (WSeq i j)
  | wf_for:
    forall i r j,
    (forall n, RPick r n -> forall x, NEq (NNum n) x -> j (NNum n) = j x) ->
    (forall n, RPick r n -> WF (fst (j (NNum n)))) ->
    WF (WFor i r j).

  Lemma translate_to_i_last:
    forall a i,
    ILast a i ->
    WF i ->
    Conc.CIn a (snd (tr i)).
  Proof.
    intros a i H.
    induction H; intros Hw; inversion Hw; subst; clear Hw.
    - simpl.
      rewrite snd_p_seq.
      auto.
    - simpl.
      destruct r as (e1, e2).
      simpl.
      apply c_in_seq_l.
      assert (Hi: CIn a (snd (tr (fst (b (NNum n)))))). {
        apply IHILast.
        apply H5.
        auto using r_last_to_pick.
      }
    - destruct r as (e1, e2).
      simpl.
      apply c_in_seq_r.
      admit.
  Qed.

  Lemma translate_1:
    forall a i,
    PPairIn a (tr i) ->
    TPairIn a i.
  Proof.
    intros.
    remember (tr i) as j.
    generalize dependent i.
    destruct j as (j, c).
    destruct H as [H|H]. {
      generalize dependent c.
      induction H; intros c' i' Hr; symmetry in Hr.
      - destruct i'; inversion Hr; subst; clear Hr.
        + constructor.
          auto.
        + destruct (tr i'1); simpl in *.
          destruct (tr i'2); simpl in *.
          inversion H1; subst; clear H1.
        + destruct r as (e1, e2).
          inversion H1.
      - destruct i'; simpl in *; inversion Hr.
        + destruct (tr i'1) as (i1, c1) eqn:R1.
          destruct (tr i'2) as (i2, c2) eqn:R2.
          simpl in *.
          inversion Hr; subst; clear Hr.
          symmetry in R1.
          apply IHIPairIn in R1.
          auto using t_pair_in_seq_l.
        + destruct r as (e1, e2).
          inversion H1.
      - destruct i'; simpl in *; inversion Hr.
        + destruct (tr i'1) as (i1, c1) eqn:R1.
          destruct (tr i'2) as (i2, c2) eqn:R2.
          simpl in *.
          inversion Hr; subst; clear Hr.
          symmetry in R2.
          assert (Hx: (n_seq c1 i2, c') = tr (w_seq c1 i'2)). {
            erewrite tr_seq; eauto.
          }
          apply IHIPairIn in Hx.
          assert (IHIPairIn := IHIPairIn c' (w_seq c1 i'2)).
          apply IHIPairIn in R2.
          auto using t_pair_in_seq_l.
          
    }
  Admitted.

  Lemma translate_1:
    forall a i,
    WLang.IPairIn a i ->
    PPairIn a (tr i).
  Proof.
    intros i a H.
    induction H; simpl;
      try rename b into i;
      try destruct r as (e1, e2);
      try remember (fst (i (NNum n))) as i_n.
    - left.
      constructor.
      assumption.
    - auto using p_pair_in_seq_l.
    - auto using p_pair_in_seq_r.
    - admit.
    - (*
      destruct (tr i) as (b, c) eqn:Ht.
      rewrite tr_subst in IHIPairIn.
      simpl.
      left.
      apply i_pair_in_for_1.
      rewrite Ht in *.
      simpl in *. *)
      admit.
    - 
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
End Defs.
