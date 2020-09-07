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

  Definition p_inst := (n_inst * Conc.inst) % type.

  Fixpoint i_seq (c:Conc.inst) (n:n_inst) : n_inst :=
    match n with
    | NSync c' => NSync (Conc.Seq c c')
    | NSeq i j => NSeq (i_seq c i) j
    | NFor i x r j => NFor (i_seq c i) x r j
    end.

  Definition seq (i:p_inst) (j:p_inst) :=
   match i, j with
    | (i,ci), (j, cj) => (NSeq i (i_seq ci j), cj)
    end.

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

  Fixpoint tr (i:w_inst) : p_inst :=
    match i with
    | WSync c => (NSync c, Conc.Skip)
    | WSeq i j => seq (tr i) (tr j)
    | WFor c1 x (e1, e2) i c2 =>
      let (b, c) := tr i in
      let e1' := NBin NPlus e1 (NNum 1) in
      let c' := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c in
      let e2' := NBin NMinus e2 (NNum 1) in
      (
        NFor (i_seq c1 (i_subst x e1 b)) x (e1', e2) (i_seq c' b),
        Conc.i_subst x e2' c
      )
    end.

  Inductive IPairIn (p:access_val*access_val) : n_inst -> Prop :=
  | i_pair_in_sync:
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
    forall r i x j,
    IPairIn p i ->
    IPairIn p (NFor i x r j)
  | i_pair_in_for_2:
    forall r n i x j,
    RPick r n ->
    IPairIn p (i_subst x (NNum n) j) ->
    IPairIn p (NFor i x r j)
  .

  Fixpoint w_seq (c:Conc.inst) (i:w_inst) :=
   match i with
   | WSync c' => WSync (Conc.Seq c c') 
   | WSeq i j => WSeq (w_seq c i) j
   | WFor c1 x (e1, e2) i c2 => WFor (Conc.Seq c c1) x (e1, e2) i c2
   end.

  Definition PPairIn a (p:p_inst) : Prop :=
    match p with
    | (i, c) => IPairIn a i \/ CPairIn a c
    end.

  Lemma i_pair_in_i_seq_l:
    forall p c i,
    CPairIn p c ->
    IPairIn p (i_seq c i).
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
(*
  Inductive TPairIn (p:access_val * access_val) : w_inst -> n_inst * Conc.inst -> Prop :=

  | t_pair_in_sync:
    forall c,
    CPairIn p c ->
    TPairIn p (WSync c) (NSync c, Conc.Skip)

  | t_pair_seq_l:
   forall i j,
    TPairIn p i (i', c) ->
    TPairIn p (WSeq i j) (
    

  | t_pair_in_seq_r:
    forall i j c,
    ALang.GetLast i c ->
    TPairIn p (w_seq c j) ->
    TPairIn p (WSeq i j)
  (*
  | t_pair_seq_last:
    forall i j c,
    ALang.GetLast j c ->
    CPairIn p c ->
    TPairIn p (WSeq i j)
  | t_pair_for_1:
    forall e1 e2 n1 n2 c1 c2 x i,
    NStep e1 n1 ->
    NStep e2 n2 ->
    n1 < n2 ->
    TPairIn p (w_seq c1 (i_subst x (NNum n1) i)) ->
    TPairIn p (WFor c1 x (e1, e2) i c2).
  | t_pair_for_2:
  *)
    .
(*
  Lemma t_pair_seq_r_eq:
    forall p i j,
    TPairIn p j ->
    TPairIn p (WSeq i j).
  Proof.
    intros.
    apply t_pair_in_seq_r with (c:=Conc.Skip).
  Qed.
*)
(*
      let e1' := NBin NPlus e1 (NNum 1) in
      let c' := Conc.i_subst x (NBin NMinus (NVar x) (NNum 1)) c in
      let e2' := NBin NMinus e2 (NNum 1) in
      (
        NFor (i_seq c1 (i_subst x e1 b)) x (e1', e2) (i_seq c' b),
        Conc.i_subst x e2' c
      )
*)
*)
(*
  Lemma t_pair_in_1:
    forall a i,
    PPairIn a (tr i) ->
    TPairIn a i.
  Proof.
    intros.
    remember (tr i) as j.
    generalize dependent i.
    destruct j as (j, c).
    simpl in *.
    destruct H as [H|H].
    2: {
      intros i.
      generalize dependent a.
      generalize dependent c.
      generalize dependent j.
      induction i; intros; inversion Heqj; subst.
      - apply c_pair_in_skip in H.
        contradiction.
      - simpl in *.
        clear H1.
        symmetry in Heqj.
        destruct (tr i1) as (j1, c1) eqn:R1.
        destruct (tr i2) as (j2, c2) eqn:R2.
        simpl in *.
        inversion Heqj; subst; clear Heqj.
        assert (IHi2 := IHi2 j2 c a H eq_refl).
        apply t_pair_in_seq_r with (c:=c1).
        destruct i2 as (j2, c2).
    induction H; intros i.
  Qed.
*)
  Lemma translate_1:
    forall a i,
    WLang.IPairIn a i ->
    PPairIn a (tr i).
  Proof.
    intros i a H.
    induction H; simpl.
    - left.
      constructor.
      assumption.
    - auto using p_pair_in_seq_l.
    - auto using p_pair_in_seq_r.
    - admit.
    - admit.
  Admitted.
End Defs.
