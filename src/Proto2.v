Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Acc.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Proto1.

Import ListNotations.

Module L2 (M:ACC).
  Module H := History M.

Section Defs.
  Import Aniceto.Graphs.Graph.

  Inductive proto :=
  | PSkip
  | PAcc: M.E -> proto
  | PSeq : proto -> proto -> proto
  | PDecl : var -> range -> proto -> proto
  | PPar : var -> list nat -> proto -> proto.

  Fixpoint p_subst x v p :=
  match p with
  | PAcc a => PAcc (M.a_subst x v a)  
  | PSeq p1 p2 => PSeq (p_subst x v p1) (p_subst x v p2)
  | PDecl y r p2 => if VAR.eq_dec x y then p else (PDecl y (r_subst x v r) (p_subst x v p2)) 
  | PPar y r p2 => if VAR.eq_dec x y then p else (PPar x r (p_subst x v p2)) 
  | PSkip => PSkip
  end.

  Definition history := list M.A.

  Definition state := list (history * proto).

  Fixpoint join (l:state) (q:proto) :=
  match l with
  | [] => []
  | (h,p)::l => (h, PSeq p q) :: l
  end.

  Inductive SStep: (history * proto) -> state -> Prop :=
  | s_step_acc:
    forall s e a,
    M.AStep e a ->
    SStep (s, PAcc e) [(a ++ s, PSkip)]
  | s_step_seq_step:
    forall s1 p1 h p3,
    SStep (s1, p1) h ->
    SStep (s1, PSeq p1 p3) (join h p3)
  | s_step_seq_skip:
    forall s p,
    SStep (s, PSeq PSkip p) [(s, p)]
  | s_step_for_step:
    forall x r p l s,
    RStep r l ->
    SStep (s, PDecl x r p) [(s, PPar x l p)]
  | s_step_par_step:
    forall s x n l p,
    SStep (s, PPar x (n::l) p) ((s, p_subst x n p) :: (s, PPar x l p) :: [])
  | s_step_par_skip:
    forall s x p,
    SStep (s, PPar x [] p) [(s, PSkip)].

  (** Reduction must not lose any process, as we need to keep the final history
      to ensure it is safe --- with the goal of proving DRF. *)

  Inductive Step: state -> state -> Prop :=
  | step_eq:
    forall p s1 s2,
    SStep p s1 ->
    Step (p::s2) (s1 ++ s2)
  | step_skip:
    forall h s1 s2,
    Step s1 s2 ->
    Step ((h,PSkip)::s1) ((h,PSkip)::s2).

  Definition MStep := clos_refl_trans _ Step.

  Definition Value (s:state) := List.Forall (fun (s':history*proto) => let (_, p) := s' in p = PSkip) s.

  Definition BStep := BigStep _ Step Value.

  Definition L1_Safe (s:(history*proto)) := let (h, _) := s in H.Safe h.

  Definition Safe : state -> Prop := List.Forall L1_Safe.

  Definition DRF a := forall b, MStep a b -> Safe b.

  Definition SafeStep (p:state * state) :=
    let (x,y) := p in Step x y /\ Safe x /\ Safe y.

  (** Safe path *)

  Inductive SafePath : state -> state -> Prop :=
  | safe_path_step:
    forall a b,
    Reaches SafeStep a b ->
    Value b ->
    SafePath a b
  | safe_path_value:
    forall a,
    Value a ->
    Safe a ->
    SafePath a a.

  Lemma drf_to_safe:
    forall a,
    DRF a ->
    Safe a.
  Proof.
    unfold DRF; intros.
    apply H with (b:=a).
    apply rt_refl.
  Qed.

  Lemma s_step_fun:
    forall a l1 l2,
    SStep a l1 ->
    SStep a l2 ->
    l1 = l2.
  Proof.
    intros (h,p).
    generalize dependent h.
    induction p; intros;
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; auto.
    - assert (a0 = a) by eauto using M.a_step_fun; subst.
      reflexivity.
    - assert (h0 = h1) by eauto.
      subst.
      reflexivity.
    - inversion H5.
    - inversion H4.
    - assert (l0 = l) by eauto using r_step_fun.
      subst.
      reflexivity.
  Qed.

  Lemma step_fun:
    forall a b c,
    Step a b ->
    Step a c ->
    b = c.
  Proof.
    induction a; intros; inversion H; inversion H0; subst; clear H H0.
    + give_up. (*
      assert (h0 = h1) by eauto using s_step_fun.
      subst.
      reflexivity. *)
    + inversion H4.
    + inversion H8.
    + inversion H5; subst; clear H5.
      assert (s2 = s3) by eauto.
      subst.
      reflexivity.
  Admitted.
(*
  Lemma b_step_skip:
    forall h,
    BStep [(h, PSkip)] [].
  Proof.
    intros.
    apply big_step_cons with (y:=[]).
    + apply step_skip.
    + apply big_step_nil.
      reflexivity.
  Qed.
*)
(*
  Lemma big_step_to_clos_trans:
    forall x y,
    BStep x y ->
    clos_refl_trans _ Step x y.
  Proof.
    intros.
    induction H; 
      eauto using rt_trans, rt_step, rt_refl.
  Qed.
*)
  Lemma safe_nil:
    Safe [].
  Proof.
    apply Forall_nil.
  Qed.

  Lemma safe_cons:
    forall x l,
    Safe l ->
    L1_Safe x ->
    Safe (x::l).
  Proof.
    intros.
    apply Forall_cons; auto.
  Qed.

  Lemma safe_skip:
    forall h,
    H.Safe h ->
    Safe [(h, PSkip)].
  Proof.
    repeat split; auto using step_skip, safe_nil, safe_cons.
  Qed.

  Lemma value_skip:
    forall h,
    Value [(h, PSkip)].
  Proof.
    intros.
    apply Forall_cons.
    + reflexivity.
    + apply Forall_nil.
  Qed.

  Lemma safe_path_skip:
    forall h,
    H.Safe h ->
    SafePath [(h, PSkip)] [(h, PSkip)].
  Proof.
    auto using safe_path_value, value_skip, safe_skip.
  Qed.

  Lemma safe_path_in_to_safe:
    forall l l' h p,
    SafePath l l' ->
    List.In (h, p) l ->
    H.Safe h.
  Proof.
    intros.
    inversion H; subst; clear H. {
      apply reaches_to_in_fst in H1.
      destruct H1 as ((v1, v2), ((?,(?,?)), [Hj|Hj]));
          subst; simpl in *; unfold Safe in *; rewrite Forall_forall in *. {
        apply H1 in H0.
        assumption.
      }
      apply H3 in H0.
      assumption.
    }
    unfold Value in *.
    unfold Safe in *.
    rewrite Forall_forall in *.
    apply H2 in H0.
    assumption.
  Qed.

  Lemma safe_path_inv_skip:
    forall h1 l,
    SafePath [(h1, PSkip)] l ->
    H.Safe h1.
  Proof.
    intros.
    assert (Hi: List.In (h1, PSkip) [(h1, PSkip)]) by auto using in_eq.
    eapply safe_path_in_to_safe in Hi; eauto.
  Qed.

  Lemma step_inv_skip:
    forall h l,
    ~ Step [(h, PSkip)] l.
  Proof.
    intros.
    intros N.
    inversion N; subst; clear N. {
      inversion H2.
    }
    inversion H2.
  Qed.

  Lemma reaches_inv_skip:
    forall h l,
    ~ Reaches SafeStep [(h, PSkip)] l.
  Proof.
    intros.
    intros N.
    apply reaches_inv_fst_edge in N.
    destruct N as (v, (Hs, _)).
    apply step_inv_skip in Hs.
    assumption.
  Qed.

  Lemma safe_path_inv_skip_2:
    forall h l,
    SafePath [(h, PSkip)] l ->
    l = [(h, PSkip)].
  Proof.
    intros.
    inversion H; subst; clear H. {
      apply reaches_inv_skip in H0.
      contradiction.
    }
    reflexivity.
  Qed.

  Lemma is_skip p:
    { p = PSkip } + { p <> PSkip }.
  Proof.
    destruct p; auto; right; intros N; inversion N.
  Defined.

  Lemma value_not_step:
    forall x,
    Value x ->
    forall y,
    ~ Step x y.
  Proof.
    induction x; intros. {
      unfold not; intros.
      inversion H0.
    }
    intros N.
    inversion N; subst; clear N.
    - inversion H; subst; clear H.
      destruct a as (?, ?).
      subst.
      inversion H3.
    - inversion H; subst; clear H.
      apply IHx with (y:= s2) in H4.
      contradiction.
  Qed.

  Lemma value_not_safe_step:
    forall x,
    Value x ->
    forall y,
    ~ SafeStep (x, y).
  Proof.
    intros.
    intros N.
    destruct N as (Ha, _).
    apply value_not_step in Ha; auto.
  Qed.

  Lemma value_not_reaches:
    forall x,
    Value x ->
    forall y,
    ~ Reaches SafeStep x y.
  Proof.
    intros.
    intros N.
    apply reaches_inv_fst_edge in N.
    destruct N as (v, Hs).
    apply value_not_safe_step in Hs; auto.
  Qed.

  Lemma step_seq_skip:
    forall h p,
    Step [(h, PSeq PSkip p)] [(h, p)].
  Proof.
    intros.
    assert (Hr: [(h,p)] = [(h, p)] ++ []). {
      auto with *.
    }
    rewrite Hr.
    apply step_eq.
    apply s_step_seq_skip.
  Qed.

  Lemma reaches_safe_path:
    forall x y z,
    Reaches SafeStep x y ->
    SafePath y z ->
    SafePath x z.
  Proof.
    intros.
    inversion H0; subst; clear H0. {
      assert (Reaches SafeStep x z) by eauto using reaches_trans.
      eapply safe_path_step; eauto.
    }
    eapply safe_path_step; eauto.
  Qed.

  Lemma safe_path_inv_fst:
    forall x y,
    SafePath x y ->
    Safe x.
  Proof.
    intros.
    inversion H; subst; clear H. {
      apply reaches_inv_fst_edge in H0.
      destruct H0 as (v, (?, (Hx, Hy))).
      assumption.
    }
    assumption.
  Qed.

  Lemma safe_path_seq_skip:
    forall h1 p l,
    SafePath [(h1, p)] l ->
    SafePath [(h1, PSeq PSkip p)] l.
  Proof.
    intros.
    assert (Safe [(h1, p)]). {
      eauto using safe_path_inv_fst.
    }
    assert (SafeStep ([(h1, PSeq PSkip p)], [(h1, p)])). {
      repeat split.
      - auto using step_seq_skip.
      - unfold Safe in *.
        rewrite Forall_forall in *.
        intros.
        destruct H1; subst. {
          simpl.
          assert (L1_Safe (h1, p)) by auto using in_eq.
          assumption.
        }
        contradiction.
      - assumption. 
    }
    assert (Reaches SafeStep [(h1, PSeq PSkip p)] [(h1, p)]). {
      apply edge_to_reaches.
      assumption.
    }
    eauto using reaches_safe_path.
  Qed.
End Defs.
End L2.

Module PhaseOrdering (M:ACC).
  Module M1 := L1 M.
  Module M2 := L2 M.
  Module H := History M.

Section PO.
  Fixpoint size p :=
  match p with
  | M1.PAcc _
  | M1.PSkip => NNum 0
  | M1.PSync => NNum 1
  | M1.PSeq p1 p2 => add (size p1) (size p2)
  | M1.PFor x (lo, hi) p => mul (sub hi lo) (size p) 
  | M1.PLoop x l p =>
    let (lo, hi) := M1.bounds l in mul (sub (NNum hi) (NNum lo)) (size p) 
  end.

  Fixpoint flatten n p :=
  match p with
  | M1.PSkip => M2.PSkip
  | M1.PSync => M2.PSkip
  | M1.PAcc a => M2.PAcc (M.e_prefix_index n a)
  | M1.PSeq p1 p2 => M2.PSeq (flatten n p1) (flatten (add n (size p1)) p2)
  | M1.PFor x r p => M2.PDecl x r (flatten (add n (mul (NVar x) (size p))) p)  
  | M1.PLoop x r p => M2.PSkip
  (* PDecl x r (flatten p (add n (mul (NVar x) (size p))))  *)
  end.

  Definition phase_order n (s:M1.state) :=
    let (h, p) := s in (H.prefix_index n h, flatten (NNum n) p).

  Import Aniceto.Graphs.Graph.


(*
  Lemma safe_path_seq:
    forall p1 h1 h2 n m p2,
    NStep (add (NNum n) (size p1)) m ->
    M2.SafePath [phase_order n (h1, p1)] (add (NNum n) (size p1)) ->
    M2.SafePath [phase_order m (h2, p2)] ->
    M2.SafePath [(H.prefix_index n h1, M2.PSeq (flatten (NNum n) p1) (flatten (add (NNum n) (size p1)) p2))].
  Proof.
    induction p1; intros; simpl in *.
    - give_up.
    - 
  Qed.
*)
  Lemma safe_path_inv_seq:
    forall h1 p1 p2 s,
    M1.SafePath (h1, M1.PSeq p1 p2) s ->
    exists h2, M1.SafePath (h1, p1) (h2, M1.PSkip) /\ M1.SafePath (h2, p2) s.
  Proof.
  Admitted.

  Definition Incl h2 (x:M2.history * M2.proto) :=
    let (h1, _) := x in 
    incl h1 h2.

  Definition Equiv h (l:M2.history * M2.proto) :=
    H.Safe h <-> M2.L1_Safe l.
(*
  Definition PhaseOrder n h1 p h2 :=
    exists l, M2.SafePath [phase_order n (h1, p)] l /\ List.Forall (Incl (H.prefix_index m h2)) l.
*)

  Inductive PhaseOrder: M1.state -> nat -> M1.state -> nat -> Prop :=
  | phase_order_def:
    forall h1 h2 p n l m,
    NStep (add (NNum n) (size p)) m ->
    M2.SafePath [phase_order n (h1, p)] l ->
    List.Forall (Incl (H.prefix_index m h2)) l ->
    PhaseOrder (h1, p) n (h2, M1.PSkip) m.

  Lemma phase_order_inv_skip:
    forall h1 h2 n1 n2,
    PhaseOrder (h1, M1.PSkip) n1 (h2, M1.PSkip) n2 ->
    n1 = n2 /\ List.Forall (Incl (H.prefix_index n2 h2)) [(H.prefix_index n2 h1, M2.PSkip)].
  Proof.
    intros.
    inversion H; subst; clear H.
    simpl in *.
    apply n_step_inv_add_n_0 in H3.
    subst.
    apply M2.safe_path_inv_skip_2 in H5.
    subst.
    intuition.
  Qed.

  Lemma phase_order_inv_sync:
    forall h1 h2 n1 n2,
    PhaseOrder (h1, M1.PSync) n1 (h2, M1.PSkip) n2 ->
    h2 = [] /\ n2 = S n1.
  Proof.
  Admitted.

  Lemma phase_order_seq_skip:
    forall h1 p n1 h2 n2,
    PhaseOrder (h1, p) n1 (h2, M1.PSkip) n2 ->
    PhaseOrder (h1, M1.PSeq M1.PSkip p) n1 (h2, M1.PSkip) n2. 
  Proof.
    intros.
    inversion H; subst; clear H.
    apply phase_order_def with (l:=l); auto.
    + simpl.
      auto using n_step_add_0_n.
    + apply M2.safe_path_seq_skip in H5.
      unfold phase_order.
      simpl.
      give_up.
  Admitted.

  Lemma phase_order_seq:
    forall p1 p2 h1 h2 h3 n1 n2 n3,
    PhaseOrder (h1, p1) n1 (h2, M1.PSkip) n2 ->
    PhaseOrder (h2, p2) n2 (h3, M1.PSkip) n3 ->
    PhaseOrder (h1, M1.PSeq p1 p2) n1 (h3, M1.PSkip) n3.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    
  Admitted.
*)
(*
  Definition WF :=
    List.Forall (fun x => H.safe_prefix_index h2 m) l.
*)
(*
  Lemma asf: 
    M2.SafePath [(H.prefix_index n h1, flatten (NNum n) p1)] l1
    List.Forall (Incl (H.prefix_index n_p1 h3)) l1
*)
  Theorem soundness:
    forall p h1 h2 n,
    M1.SafePath (h1, p) (h2, M1.PSkip) ->
    exists m, PhaseOrder (h1, p) n (h2, M1.PSkip) m.
  Proof.
    induction p; intros; simpl in *; eexists.
    - eapply phase_order_def.
      + give_up.
      + apply M1.safe_path_to_h_safe in H.
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      + give_up.
    - eapply phase_order_def.
      + give_up.
      + apply M1.safe_path_to_h_safe in H.
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      + give_up.
    - give_up.
    - (*assert (Hn_p1: exists n_p1, NStep  (add (NNum n) (size p1)) n_p1)
        by give_up; destruct Hn_p1 as (n_p1, Hn_p1).*)
      apply safe_path_inv_seq in H.
      destruct H as (h3, (Hp1, Hp2)).
      eapply IHp1 with (n:=n) in Hp1; eauto; clear IHp1; destruct Hp1 as (m, IHp1).
      eapply IHp2 with (n:=m) in Hp2; eauto using n_step_num; clear IHp2.
      destruct Hp2 as (m', IHp2).
      apply phase_order_seq with (h2:=h3) (n2:=m); eauto.
      give_up.
    - give_up.
    - give_up.
  Admitted.


  Theorem correctness_1:
    forall p h1 h2 e n m,
    NStep e n ->
    NStep (add (NNum n) (size p)) m ->
    M1.SafePath (h1, p) (h2, M1.PSkip) ->
    exists l, M2.SafePath [phase_order n (h1, p)] l /\ List.Forall (Incl (H.prefix_index m h2)) l.
  Proof.
    induction p; intros; simpl.
    - simpl in *.
      eexists.
      apply M1.safe_path_to_h_safe in H1.
      split. {
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      }
      give_up.
    - simpl in *.
      eexists.
      split. {
        apply M1.safe_path_to_h_safe in H1.
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      }
      give_up.
    - give_up.
    - (*  M1.SafePath (h, M1.PSeq p1 p2) ->  M1.SafePath (h, p1) /\ exists h' M1.SafePath(h', p2) *)
      eexists.
      simpl in *.
      apply safe_path_inv_seq in H1.
      destruct H1 as (h3, (Hp1, Hp2)).

      (* Apply the induction hypothesis to p1: *)
      assert (Hn_p1: exists n_p1, NStep  (add (NNum n) (size p1)) n_p1)
        by give_up; destruct Hn_p1 as (n_p1, Hn_p1).
      eapply IHp1 with (n:=n) in Hp1; eauto; clear IHp1.
      destruct Hp1 as (l1, (Hp1, Hl1)).

      (* Apply the induction hypothesis to p2: *)
      assert (Hn_p2: exists n_p2, NStep (add (NNum n_p1) (size p2)) n_p2)
        by give_up; destruct Hn_p2 as (n_p2, Hn_p2).
      eapply IHp2 with (n:=n_p1) in Hp2; eauto; clear IHp2.
      destruct Hp2 as (l2, (Hp2, Hl2)); eauto.
  Admitted.

  Theorem correctness:
    forall s e n h,
    NStep e n ->
    M1.SafePath s h <-> exists l, M2.SafePath [phase_order n s] l.
  Proof.
    intros s.
    destruct s as (h, p).
    generalize dependent h.
    induction p; intros; simpl.
    - split; intros.
      + apply M1.safe_path_to_h_safe in H0.
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      + apply M2.safe_path_inv_skip, H.safe_prefix_index in H0.
        auto using M1.safe_path_skip.
    - split; intros.
      + apply M1.safe_path_to_h_safe in H0.
        apply M2.safe_path_skip, H.safe_prefix_index.
        assumption.
      + apply M2.safe_path_inv_skip, H.safe_prefix_index in H0.
        auto using M1.safe_path_sync.
    - give_up.
    - split; intros.
      + (*  M1.SafePath (h, M1.PSeq p1 p2) ->  M1.SafePath (h, p1) /\ exists h' M1.SafePath(h', p2) *)
        destruct H0 as (h2,Hy).
        apply safe_path_inv_seq in Hy.
        destruct Hy as (h3, (Hp1, Hp2)).
        eapply IHp1 in Hp1; eauto.
        assert (Hx: exists m, NStep  (add (NNum n) (size p1)) m). {
          give_up.
        }
        destruct Hx as (m, Hx).
        eapply IHp2 with (n:=m) in Hp2; eauto.
        
  Admitted.
End PO.
End PhaseOrdering.