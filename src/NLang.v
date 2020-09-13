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
  | NFor : n_inst -> var -> range -> n_inst -> n_inst.

  Fixpoint subst x v i :=
    match i with
    | NSync c => NSync (Conc.i_subst x v c)
    | NSeq i1 i2 => NSeq (subst x v i1) (subst x v i2)
    | NFor P y r Q =>
      let Q' := if VAR.eq_dec x y
        then Q
        else subst x v Q
      in
      NFor (subst x v P) y (r_subst x v r) Q'
    end.

  Definition p_inst := (n_inst * Conc.inst) % type.
(*
  Inductive IEq : n_inst -> n_inst -> Prop :=
  | i_eq_sync:
    forall c c',
    CEq c c' ->
    IEq (NSync c) (NSync c')
  | i_eq_seq:
    forall P P' Q Q',
    IEq P P' ->
    IEq Q Q' ->
    IEq (NSeq P Q) (NSeq P' Q')
  | i_eq_for:
    forall P P' e1 e2 Q Q',
    IEq P P' ->
    (forall n n', NEq n n' -> IEq (Q n) (Q' n')) ->
    IEq (NFor P (e1, e2) Q) (NFor P' (e1', e2') Q).
*)

  Fixpoint w_seq (c:Conc.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (c_seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 x r P c2 => WFor (c_seq c c1) x r P c2
   end.

  Fixpoint n_seq (c:Conc.inst) (n:n_inst) : n_inst :=
    match n with
    | NSync c' => NSync (c_seq c c')
    | NSeq i j => NSeq (n_seq c i) j
    | NFor i x r j => NFor (n_seq c i) x r j
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
      rewrite IHi1.
      reflexivity.
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
    - rewrite IHi1.
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
  Reserved Notation "P |> Q" (at level 80).

  Inductive Translate : w_inst -> p_inst -> Prop :=
  (*
        [[ c ; sync ]] |> ( c, skip )
  *) 
  | translate_sync:
    forall c,
    WSync c |> (NSync c, Conc.Skip)

  | translate_seq:
    forall P P' Q Q' R,
    P |> P' ->
    Q |> Q' ->
    R = p_seq P' Q' ->
    (* --------- *)
    WSeq P Q |> R  
  
  | translate_for:
    forall x e1 e2 P c2 c1 P_e1 c_e1 P_dec_e2 P_dec_x c_dec_x c_dec_e2 P_x c_x P' c', 
    w_subst x e1 P |> (P_e1, c_e1) ->
    w_subst x (NBin NMinus (NVar x) (NNum 1)) P |> (P_dec_x , c_dec_x) ->
    P |> (P_x, c_x) ->
    w_subst x (NBin NMinus e2 (NNum 1)) P |> (P_dec_e2, c_dec_e2) ->
    let c2_dec_x := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c2 in
    let c2_dec_e2 := Conc.i_subst x (NBin NMinus e2 (NNum 1)) c2 in
    P' =
      NFor
        (n_seq c1 P_e1) x (e1, e2)
        (n_seq c_dec_x (n_seq c2_dec_x P_x)) ->
    c' = c_seq c_dec_e2 c2_dec_e2 ->
    WFor c1 x (e1, e2) P c2 |> (P', c')
    
  where " P |> Q" := (Translate P Q).

  (*
  Fixpoint tr i :=
    match i with
    | WSync c => (NSync c, Conc.Skip)
      (*
        [[ P; Q ]] = [[P]] ;; [[Q]]
        *) 
    | WSeq P Q => p_seq [[ P ]] [[ Q ]]
    | WFor c1 x (e1, e2) P c2 =>
      (*
      
      [[  c1; for x \in (e1, e2] { \x. P, \x. c2 } ]] =
        
        c1; P'(e1);
        for x \in (e1 + 1, e2) {
          c'(x - 1); c2 (x - 1); P'(x)
        }
        ,
        c'(e2 - 1); c2 (e2 - 1)

        
       *)
      let P' e := fst ([[w_subst x e P ]]) in
      let c' e := Conc.Seq (snd ([[w_subst x e P]])) (Conc.i_subst x e c2) in
      (
        NFor
          (n_seq c1 (P' e1))
          x
          (NBin NPlus e1 (NNum 1), e2)
          (n_seq (c' (NBin NMinus (NVar x) (NNum 1))) (P' (NVar x)))
        ,
        c' (NBin NMinus e2 (NNum 1))
      )
    end
    where "[[ P ]]" := (tr P).
  *)

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
    forall x r i j,
    IPairIn p i ->
    IPairIn p (NFor i x r j)
  | i_pair_in_for_2:
    forall r n i j x,
    RPick r n ->
    IPairIn p (subst x (NNum n) j) ->
    IPairIn p (NFor i x r j)
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
(*
  Lemma tr_seq:
    forall P Q c,
    P |> (Q, c) ->
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
      inversion H0; subst; clear H0.
      simpl.
      rewrite n_seq_c_seq.
      auto.
  Qed.
*)
  Lemma snd_p_seq:
    forall i j,
    snd (p_seq i j) = snd j.
  Proof.
    intros (i, ci) (j, cj).
    destruct i; intros; simpl; auto.
  Qed.

  Lemma p_seq_inv_snd:
    forall P Q c Q' c',
    p_seq P (Q, c) = (Q', c') ->
    c' = c.
  Proof.
    intros.
    destruct P as (P, c1).
    simpl in *.
    inversion H; subst; clear H.
    reflexivity.
  Qed.

(*
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
    forall c1 r P c2,
    (forall n, RPick r n -> forall x, NEq (NNum n) x -> WLang.IEq (P (NNum n)) (P x)) ->
    (forall n, RPick r n -> WF (P (NNum n))) ->
    WF (WFor c1 r P c2).

  Definition IEq P Q :=
    forall p, IPairIn p P <-> IPairIn p Q. 

  Definition PEq P Q :=
    forall p, PPairIn p P <-> PPairIn p Q.
(*
  Lemma tr_eq (*i_eq: forall p Q, WLang.IPairIn p Q <-> PPairIn p [[Q]]*):
    forall P Q,
    WLang.IEq P Q ->
    Conc.CEq (snd (tr P)) (snd (tr Q)).
  Proof.
    intros.
    split; intros Hi.
    -  
    induction P; intros.
    - simpl in *.
      split; intros Hi.
      + simpl in *.
        apply c_in_skip in Hi.
        contradiction.
      + 
        Search (CIn _ Skip).
        destruct Hi as [Hi|Hi].
        2: { apply c_pair_in_skip in Hi. contradiction. }
        unfold WLang.IEq in H.
        inversion Hi; subst; clear Hi.
        assert (Hi: WLang.IPairIn p Q). {
          assert (X: WLang.IPairIn p (WSync i)). {
            auto using WLang.i_pair_in_sync.
          }
          apply H in X.
          assumption.
        }
        apply i_eq; auto.
      + apply i_eq in Hi.
        apply H in Hi.
        simpl.
        inversion Hi; subst; clear Hi.
  Admitted.
  *)
*)
  Lemma translate_to_i_last:
    forall a P,
    ILast a P ->
    forall Q c,
    P |> (Q, c) ->
    Conc.CIn a c.
  Proof.
    intros a P H.
    induction H; intros Q c Ht; inversion Ht; subst; clear Ht.
    - destruct Q' as (Q', c').
      assert (c' = c). {
        symmetry.
        eapply p_seq_inv_snd; eauto.
      }
      subst.
      eauto.
    - 
      assert (Hn: NStep (NBin NMinus e2 (NNum 1)) n) by eauto using r_last_to_eq.
      eapply H1 in H12; eauto.
      auto using c_in_c_seq_l.
    - assert (Hn: NStep (NBin NMinus e2 (NNum 1)) n) by eauto using r_last_to_eq.
      apply c_in_c_seq_r.
      unfold c2_dec_e2.
      eauto.
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
