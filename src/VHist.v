Require Import Coq.Lists.List.

Require Import AccExp.

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

  Fixpoint vhist_to_list (p:vhist) : list history :=
    match p with
    | v_one h => [h]
    | v_cons h m => h :: vhist_to_list m
    end.

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

