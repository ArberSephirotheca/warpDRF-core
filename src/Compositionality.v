Require Import AExp.
Require Import Tasks.
Require Import Var.
Require Import WLang.
Require Import ULang.
Require Import NExp.
Require Import Tictac.
Require Import ALang.
Require Import Util.
Require Import RExp.
Require Import Lia.

Section Props.
  Context `{T:Tasks}.
  Context `{A:Access}.

  Inductive ctxt :=
  | Hole: ctxt
  | Sync: ULang.inst -> ctxt
  | SeqL: ctxt -> n_inst -> ctxt
  | SeqR: n_inst -> ctxt -> ctxt
  | ForL: ctxt -> var -> range -> n_inst -> ctxt
  | ForR: n_inst -> var -> range -> ctxt -> ctxt.  

  Fixpoint c_subst x v i :=
    match i with
    | Hole => Hole
    | Sync u => Sync (ULang.i_subst x v u)
    | SeqL c q => SeqL (c_subst x v c) (subst x v q)
    | SeqR q c => SeqR (subst x v q) (c_subst x v c)
    | ForL c y r q =>
      let q' := if VAR.eq_dec x y
        then q
        else subst x v q
      in
      ForL (c_subst x v c) y (r_subst x v r) q'
    | ForR q y r c =>
      let c' := if VAR.eq_dec x y
        then c
        else c_subst x v c
      in
      ForR (subst x v q) y (r_subst x v r) c'
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
(*
  Inductive Plug p : ctxt -> n_inst -> Prop :=
  | Plug_Hole: Plug p Hole p
  | Plug_Sync: forall u,
      Plug p (Sync u) (NSync u)
  | Plug_SeqL: forall c p' q,
      Plug p c p' ->
      Plug p (SeqL c q) (NSeq p' q)
  | Plug_SeqR: forall c p' q,
      Plug p c p' ->
      Plug p (SeqR q c) (NSeq q p')  
  | Plug_ForL:
      forall c v r q p',
        Plug p c p' ->
        Plug p (ForL c v r q) (NFor p' v r q)
  | Plug_ForR:
      forall c v r q p',
        Plug p c p' ->
        Plug p (ForR q v r c) (NFor q v r p').
*)
  Definition DRF (P:n_inst) :=
    forall p,
      IPairIn p P ->
      access_safe (fst p) (snd p).

    Definition UDRF (P:ULang.inst) :=
    forall p,
      ULang.CPairIn p P ->
      access_safe (fst p) (snd p).

  Inductive IDRF : n_inst -> Prop :=
  | idrf_sync: forall u,
      UDRF u -> IDRF (NSync u)
  | idrf_seq: forall p q,
      IDRF p -> IDRF q -> IDRF (NSeq p q)
  | idrf_for: forall p q r x,
      IDRF p ->
      (forall n, RPick r n -> IDRF (subst x (NNum n) q)) ->
      IDRF (NFor p x r q).


  
  Inductive CDRF : ctxt -> Prop :=
  | cdrf_hole: CDRF Hole 
  | cdrf_sync: forall u,
      UDRF u -> CDRF (Sync u)
  | cdrf_seql: forall c p,
      CDRF c ->
      IDRF p ->
      CDRF (SeqL c p)
  | cdrf_seqr: forall c p,
      CDRF c ->
      IDRF p ->
      CDRF (SeqR p c)
  | cdrf_forl: forall c p r x,
      CDRF c ->
      (forall n, RPick r n -> IDRF (subst x (NNum n) p)) ->
      CDRF (ForL c x r p)
  | cdrf_forr: forall p c r x,
      IDRF p ->
      (forall n, RPick r n -> CDRF (c_subst x (NNum n) c)) ->
      CDRF (ForR p x r c).


  (* 
     fv(p) is empty
      subst x v (plug c p) == plug (subs c) p 
   *)

  Definition Closed p := forall x, ~ Occurs x p.


  Lemma subst_eq:
    forall p,
    Closed p ->
    subst x v p = p

  
  Lemma closed_plug_subst:
    forall p,
      Closed p ->
      forall c x v,
        subst x v (plug c p) = plug (c_subst x v c) p.
  Proof.
    induction c; intros; simpl.
    - 
    - reflexivity.
    - rewrite IHc.
      reflexivity.
    - rewrite IHc.
      reflexivity.
    - rewrite IHc.
      reflexivity.
    - rewrite IHc.
      destruct (Set_VAR.MF.eq_dec x v).
      + reflexivity.
      + reflexivity.
  Admitted.
      
(*
  Lemma subst_plug_ind:
    forall p',
      IDRF p' ->
      forall x v c p,
        Plug p (c_subst x v c) p' -> 
        IDRF (subst x v (plug c p)).
  Proof.
    intros p' H.
    induction H; intros.
    - invc H0.
      + destruct c.
        * 
      + destruct c; invc H2.
        * simpl.
          apply idrf_sync.


  
  Lemma subst_plug:
    forall x v c p,
      IDRF (plug (c_subst x v c) p) ->      
      IDRF (subst x v (plug c p)).
  Proof.
    admit.
  Admitted.

  *)
  Lemma compo:
    forall c,
      CDRF c ->
      forall p,
        Closed p ->
        IDRF p ->
        IDRF (plug c p).
  Proof.
    intros c H.    
    induction H; intros; simpl.
    - assumption.
    - admit.
    - admit.
    - admit.
    - admit.
    - apply idrf_for.
      + assumption.
      + intros.
        assert (IDRF (plug (c_subst x (NNum n) c) p0)).
        { auto. }
        rewrite closed_plug_subst.
        * assumption.
        * assumption.
     
    
