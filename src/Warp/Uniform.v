From Stdlib Require Import Lists.List Bool.Bool.
From Faial.Core Require Import Var.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Semantics Participation.
From Faial.Warp Require Lang Reference.

Import ListNotations.

(* Warp-uniform control flow for this one-conditional fragment. A test that
   mentions neither the thread identifier nor a value read from memory has
   the same value in every thread, whatever the input and schedule. *)
Fixpoint closed_nexp (e : nexp) : bool :=
  match e with
  | NNum _ => true
  | NTid | NVar _ => false
  | NBin _ e1 e2 => closed_nexp e1 && closed_nexp e2
  end.

Fixpoint closed_bexp (e : bexp) : bool :=
  match e with
  | BBool _ => true
  | NRel _ e1 e2 => closed_nexp e1 && closed_nexp e2
  | BRel _ e1 e2 => closed_bexp e1 && closed_bexp e2
  | BNot inner => closed_bexp inner
  end.

(* The strict form used by the proofs: every branch in the code has a closed
   test whose value is b. *)
Fixpoint uniform_tests (b : bool) (code : Lang.t) : bool :=
  match code with
  | Lang.Read _ _ body => uniform_tests b body
  | Lang.Seq first rest => uniform_tests b first && uniform_tests b rest
  | Lang.Cond test yes no =>
      closed_bexp test &&
      match b_step 0 test with Some v => Bool.eqb v b | None => false end &&
      uniform_tests b yes && uniform_tests b no
  | _ => true
  end.

Fixpoint has_primitive (code : Lang.t) : bool :=
  match code with
  | Lang.AddZero | Lang.Barrier _ => true
  | Lang.Read _ _ body => has_primitive body
  | Lang.Seq first rest => has_primitive first || has_primitive rest
  | Lang.Cond _ yes no => has_primitive yes || has_primitive no
  | _ => false
  end.

(* The paper's rule: every branch around a warp primitive has a closed test
   whose value is b. Branches without a primitive may diverge. *)
Fixpoint primitives_uniform (b : bool) (code : Lang.t) : bool :=
  match code with
  | Lang.Read _ _ body => primitives_uniform b body
  | Lang.Seq first rest => primitives_uniform b first && primitives_uniform b rest
  | Lang.Cond test yes no =>
      (negb (has_primitive yes || has_primitive no) ||
       (closed_bexp test &&
        match b_step 0 test with Some v => Bool.eqb v b | None => false end)) &&
      primitives_uniform b yes && primitives_uniform b no
  | _ => true
  end.

(* Every thread takes the same branch around each warp primitive, so a
   collective in the taken branch runs with the whole warp in every execution. *)
Definition warp_uniform (programs : list Lang.t) :=
  exists b, Forall (fun code => primitives_uniform b code = true) programs.

Lemma closed_nexp_step : forall e tid, closed_nexp e = true -> n_step tid e = n_step 0 e.
Proof.
  induction e as [| n | x | o e1 IH1 e2 IH2]; intros tid Hclosed; cbn in *;
    try discriminate; try reflexivity.
  apply andb_true_iff in Hclosed as [H1 H2].
  now rewrite (IH1 tid H1), (IH2 tid H2).
Qed.

Lemma closed_bexp_step : forall e tid, closed_bexp e = true -> b_step tid e = b_step 0 e.
Proof.
  induction e as [v | o e1 e2 | o e1 IH1 e2 IH2 | inner IH];
    intros tid Hclosed; cbn in *.
  - reflexivity.
  - apply andb_true_iff in Hclosed as [H1 H2].
    now rewrite (closed_nexp_step _ tid H1), (closed_nexp_step _ tid H2).
  - apply andb_true_iff in Hclosed as [H1 H2].
    now rewrite (IH1 tid H1), (IH2 tid H2).
  - now rewrite (IH tid Hclosed).
Qed.

Lemma closed_nexp_subst : forall e x v, closed_nexp e = true -> n_subst x v e = e.
Proof.
  induction e as [| n | y | o e1 IH1 e2 IH2]; intros x v Hclosed; cbn in *;
    try discriminate; try reflexivity.
  apply andb_true_iff in Hclosed as [H1 H2].
  now rewrite (IH1 x v H1), (IH2 x v H2).
Qed.

Lemma closed_bexp_subst : forall e x v, closed_bexp e = true -> b_subst x v e = e.
Proof.
  induction e as [b | o e1 e2 | o e1 IH1 e2 IH2 | inner IH];
    intros x v Hclosed; cbn in *.
  - reflexivity.
  - apply andb_true_iff in Hclosed as [H1 H2].
    now rewrite (closed_nexp_subst _ x v H1), (closed_nexp_subst _ x v H2).
  - apply andb_true_iff in Hclosed as [H1 H2].
    now rewrite (IH1 x v H1), (IH2 x v H2).
  - now rewrite (IH x v Hclosed).
Qed.

(* A branch decision under uniform tests always takes the shared value. *)
Lemma uniform_branch_decision : forall b code tid v,
  uniform_tests b code = true -> branch_decision tid code = Some v -> v = b.
Proof.
  intros b code tid v.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros Hu Hbranch; cbn in *; try discriminate.
  - apply andb_true_iff in Hu as [Hfirst _]. exact (IH1 Hfirst Hbranch).
  - rewrite !andb_true_iff in Hu. destruct Hu as [[[Hclosed Hvalue] _] _].
    rewrite <- (closed_bexp_step _ tid Hclosed), Hbranch in Hvalue.
    now apply eqb_prop.
Qed.

Lemma uniform_tests_subst : forall b code x v,
  uniform_tests b code = true -> uniform_tests b (Lang.subst x v code) = true.
Proof.
  intros b code.
  induction code as [y address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros x v Hu; cbn in *; auto.
  - destruct (VAR.eq_dec x y); auto.
  - apply andb_true_iff in Hu as [H1 H2]. now rewrite (IH1 x v H1), (IH2 x v H2).
  - rewrite !andb_true_iff in Hu. destruct Hu as [[[Hclosed Hvalue] Hyes] Hno].
    rewrite (closed_bexp_subst _ x v Hclosed), Hclosed, Hvalue,
      (IH1 x v Hyes), (IH2 x v Hno).
    reflexivity.
Qed.

(* Ordinary steps only substitute read values or move into a branch. *)
Lemma uniform_tests_step : forall b tid input m code e m' code',
  uniform_tests b code = true ->
  thread_step tid input m code = Some (e, m', code') -> uniform_tests b code' = true.
Proof.
  intros b tid input m code. revert m.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros m e m' code' Hu Hstep; cbn in Hstep;
    try discriminate.
  - destruct (n_step tid address); try discriminate.
    inversion Hstep; subst. cbn in Hu. now apply uniform_tests_subst.
  - destruct (n_step tid address), (n_step tid contents); try discriminate.
    inversion Hstep; subst. reflexivity.
  - cbn in Hu. apply andb_true_iff in Hu as [Hfirst Hrest].
    destruct first; cbn -[thread_step] in Hstep.
    all: try solve [inversion Hstep; subst; exact Hrest].
    all: match type of Hstep with
    | context [thread_step ?owner ?base ?mem ?code] =>
        destruct (thread_step owner base mem code)
          as [[[event next_mem] next_code]|] eqn:Hfirststep; try discriminate;
        inversion Hstep; subst; cbn;
        rewrite (IH1 _ _ _ _ Hfirst Hfirststep); exact Hrest
    end.
  - destruct (b_step tid test) as [v|]; try discriminate.
    inversion Hstep; subst. cbn in Hu. rewrite !andb_true_iff in Hu.
    destruct Hu as [[_ Hyes] Hno]. destruct v; assumption.
Qed.

Lemma uniform_tests_release : forall b code code',
  at_add_zero code = Some code' -> uniform_tests b code = true ->
  uniform_tests b code' = true.
Proof.
  intros b code.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros code' Hrelease Hu; cbn in Hrelease;
    try discriminate.
  - destruct (at_add_zero first) as [first'|] eqn:Hfirst; try discriminate.
    inversion Hrelease; subst. cbn in Hu. apply andb_true_iff in Hu as [H1 H2].
    cbn. rewrite (IH1 _ eq_refl H1). exact H2.
  - inversion Hrelease; subst. reflexivity.
Qed.

Lemma release_collective_uniform : forall b ds codes codes',
  release_collective ds codes = Some codes' ->
  Forall (fun code => uniform_tests b code = true) codes ->
  Forall (fun code => uniform_tests b code = true) codes'.
Proof.
  intros b ds. induction ds as [|d ds IH]; intros [|code codes] codes' Hrelease Hall;
    cbn in Hrelease; try discriminate.
  - inversion Hrelease; subst. constructor.
  - inversion Hall; subst.
    destruct (release_collective ds codes) as [rest'|] eqn:Hrest; try discriminate.
    destruct d.
    + inversion Hrelease; subst. constructor; [assumption|eapply IH; eauto].
    + destruct (at_add_zero code) as [code'|] eqn:Hcode; try discriminate.
      inversion Hrelease; subst.
      constructor; [eapply uniform_tests_release; eauto|eapply IH; eauto].
    + inversion Hrelease; subst. constructor; [assumption|eapply IH; eauto].
Qed.

(* Ordinary code and a collective's body contain no branch. *)
Local Lemma ordinary_uniform : forall b code,
  Reference.ordinary code = true -> uniform_tests b code = true.
Proof.
  intros b code.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros Hordinary; cbn in *; try discriminate;
    auto.
  apply andb_true_iff in Hordinary as [H1 H2]. now rewrite (IH1 H1), (IH2 H2).
Qed.

Local Lemma collective_body_uniform : forall b code,
  Reference.collective_body code = true ->
  uniform_tests b code = true /\ has_primitive code = true.
Proof.
  intros b code.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros Hbody; cbn in *; try discriminate.
  - exact (IH Hbody).
  - apply orb_true_iff in Hbody as [Hbody|Hbody]; apply andb_true_iff in Hbody as [H1 H2].
    + destruct (IH2 H2) as [Hu Hp].
      rewrite (ordinary_uniform _ _ H1), Hu, Hp, orb_true_r. split; reflexivity.
    + destruct (IH1 H1) as [Hu Hp].
      rewrite (ordinary_uniform _ _ H2), Hu, Hp. split; reflexivity.
  - split; reflexivity.
Qed.

(* In the programs the reference accepts, each thread's only branch surrounds
   the collective, so the paper's rule and the strict form coincide. *)
Lemma supported_primitives_uniform : forall b code,
  Reference.supported_thread code = true ->
  primitives_uniform b code = true -> uniform_tests b code = true.
Proof.
  intros b code.
  induction code as [x address body IH | address contents | first IH1 rest IH2 |
    test yes IH1 no IH2 | site | |]; intros Hsupported Hprimitives; cbn in *;
    try discriminate.
  - exact (IH Hsupported Hprimitives).
  - apply andb_true_iff in Hprimitives as [P1 P2].
    apply orb_true_iff in Hsupported as [Hs|Hs]; apply andb_true_iff in Hs as [H1 H2].
    + now rewrite (ordinary_uniform _ _ H1), (IH2 H2 P2).
    + now rewrite (IH1 H1 P1), (ordinary_uniform _ _ H2).
  - apply andb_true_iff in Hsupported as [Hyes Hno].
    destruct (collective_body_uniform b _ Hyes) as [Hyesu Hyesp].
    rewrite Hyesp in Hprimitives. cbn in Hprimitives.
    rewrite !andb_true_iff in Hprimitives.
    destruct Hprimitives as [[[Hclosed Hvalue] _] _].
    now rewrite Hclosed, Hvalue, Hyesu, (ordinary_uniform _ _ Hno).
Qed.

Lemma supported_warp_uniform : forall programs,
  Reference.supported programs = true -> warp_uniform programs ->
  exists b, Forall (fun code => uniform_tests b code = true) programs.
Proof.
  intros programs Hsupported [b Hprimitives]. exists b.
  assert (Hall : forallb Reference.supported_thread programs = true).
  { unfold Reference.supported in Hsupported.
    destruct programs; [discriminate|exact Hsupported]. }
  rewrite forallb_forall in Hall. rewrite Forall_forall in *.
  intros code Hin. apply supported_primitives_uniform; auto.
Qed.
