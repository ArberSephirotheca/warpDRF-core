Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Coq.omega.Omega.
Require Import Recdef.
Require Omega.
Require Import Var.
Require Import Tid.
Require Import Loc.
Require Import Exp.
Require Import Access.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.

Import ListNotations.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | Seq: inst -> inst -> inst
  | Access: access_exp -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.


Fixpoint i_subst x v i :=
  match i with
  | Access a => Access (access_subst x v a)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  | Loop y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2'
  | Skip => Skip
  | Sync => Sync
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  end.


Inductive Unsync : inst -> Prop :=
| unsync_skip:
  Unsync Skip
| unsync_seq:
  forall i j, 
  Unsync i ->
  Unsync j ->
  Unsync (Seq i j)
| unsync_access:
  forall a, 
  Unsync (Access a)
| unsync_for:
  forall v r i,
  Unsync i ->
  Unsync (For v r i)
| unsync_loop:
  forall v r i,
  Unsync i ->
  Unsync (Loop v r i).

Goal Unsync (Seq Skip Skip).
Proof.
simpl.
apply unsync_seq.
- apply unsync_skip.
- apply unsync_skip.
Qed.


Theorem Unsync_skip_seq_l:
forall i,
Unsync i ->
Unsync (Seq i Skip).
Proof.
intros.
apply unsync_seq.
- assumption.
- apply unsync_skip.
Qed.

Theorem Unsync_syncs:
~Unsync Sync.
Proof.
unfold not.
intros N.
inversion N.
Qed.


Inductive In : inst -> inst -> Prop :=
| in_skip:
  In Skip Skip
| in_sync:
  In Sync Sync
| in_access:
  forall a,
  In (Access a) (Access a)
| in_seq_l:
  forall k i j,
  In k i ->
  In k (Seq i j)
| in_seq_r:
  forall k i j,
  In k j ->
  In k (Seq i j)
| in_for:
  forall k v r i,
  In k i ->
  In k (For v r i)
| in_loop:
  forall k v r i,
  In k i ->
  In k (Loop v r i).

Theorem Sync_sync_in:
forall i,
Unsync i -> ~In Sync i.
Proof.
induction i; intros; intros N.
- inversion N.
- inversion H.
- inversion N; subst; clear N.
  * inversion H; subst; clear H.
    apply IHi1 in H3. 
    unfold not in *.
    apply H3.
    assumption.
  * inversion H; subst; clear H.
    apply IHi2 in H2. 
    unfold not in *.
    apply H2.
    assumption.
- inversion N.
- inversion N; subst; clear N.
  inversion H; subst; clear H.
  apply IHi in H1.
  contradiction.
- inversion N; subst; clear N.
  inversion H; subst; clear H.
  apply IHi in H1.
  contradiction.
Qed.


Theorem Sync_sync_in_rev:
forall i,
~In Sync i -> Unsync i.
Proof.
induction i; intros.
- apply unsync_skip.
- unfold not in *. contradict H. apply in_sync.
- apply unsync_seq.
  * apply IHi1.
    intros N.
    contradict H.
    apply in_seq_l.
    assumption.
  * apply IHi2.
    intros N.
    contradict H.
    apply in_seq_r.
    assumption.
- apply unsync_access.
- apply unsync_for.
  apply IHi.
  intros N.
  contradict H.
  apply in_for.
  assumption.
- apply unsync_loop.
  apply IHi.
  intros N.
  contradict H.
  apply in_loop.
  assumption.
Qed.



Import Hist.

Notation history := (list access_val).

Context `{T:Tasks}.


Inductive Run: (inst * history) -> (inst * history) -> Prop:=
| run_sync:
  forall h,
  Run (Sync, h) (Skip, [])
| run_access:
  forall a h v,
  GenAccess TID a TID_COUNT v ->
  Run ((Access a), h) (Skip, (List.concat v ++ h))
| run_seq:
  forall h h' i j k,
  Run (i, h) (j, h') ->
  Run ((Seq i k), h) ((Seq j k), h')
| run_seq_skip:
  forall h i,
  Run ((Seq Skip i), h) (i, h)
| run_for:
  forall r l i x h,
  RStep r l ->
  Run ((For x r i), h) ((Loop x l i), h)
| run_for_loop_nil:
  forall x i h,
  Run ((Loop x [] i), h) (Skip, h)
| run_for_loop_cons:
  forall x n i h l,
  Run ((Loop x (n::l) i), h) ((Seq (i_subst x (NNum n) i) (Loop x l i)), h).


Inductive Multi_Run: (inst * history) -> (inst * history) -> Prop :=
| mrun_refl:
  forall i h,
  Multi_Run (i, h) (i, h)
| mrun_step:
  forall i1 i2 i3 h1 h2 h3,
  Run (i1, h1) (i2, h2) ->
  Multi_Run (i2, h2) (i3, h3) ->
  Multi_Run (i1, h1) (i3, h3).

(*

(* If we define Multi_Run in terms of pairs, then we can use the
   Setoid tactics (see example next). *)
Inductive MRun : (inst * history) -> (inst * history) -> Prop :=
| m_run_def:
  forall i h1 j h2, 
  Multi_Run i h1 j h2 ->
  MRun  (i, h1) (j, h2).

*)

Lemma m_run_refl:
  forall x,
  Multi_Run x x.
Proof.
  intros.
  destruct x.
  apply mrun_refl.
Qed.

Theorem run_imp_mrun:
forall i1 i2 h1 h2,
Run (i1, h1) (i2, h2) ->
Multi_Run (i1, h1) (i2, h2).
Proof.
intros.
apply mrun_step with (i2:=i2) (h2:=h2).
- assumption.
- apply mrun_refl.
Qed.

Lemma m_run_trans:
  forall x y z,
  Multi_Run x y ->
  Multi_Run y z ->
  Multi_Run x z.
Proof.
  intros x y.
  intros z H.
  (* introduce the z back into the assumptions,
     so that induction doesn't capture it *)
  generalize dependent z.
 (* inversion H; subst; clear H. *)
  induction H; intros.
  - assumption.
  - apply IHMulti_Run in H1.
    inversion H1; subst; clear H1.
    + apply run_imp_mrun in H.
      assumption.
    + apply mrun_step with (i2:=i2) (h2:=h2).
      ++  assumption.
      ++ apply mrun_step with (i2:=i4) (h2:=h4).
        +++ assumption.
        +++ assumption.
Qed.

(** We register MRun's transitivity and reflexivity with Coq's tactics.
    1. Instead of using m_run_refl we can use the tactics 'reflexivity'.
    2. Instead of using m_run_trans we can use the tactics 'transitivity'.
    *)
Global Add Parametric Relation : _ Multi_Run
  reflexivity proved by m_run_refl
  transitivity proved by m_run_trans
  as m_run_setoid.



Theorem uni_skip_one:
forall i1 i2 h1 h2,
Run (i1, h1) (i2, h2) ->
Multi_Run ((Seq Skip i1), h1) (i2, h2).
Proof.
intros.
apply mrun_step with (i2:=i1) (h2:=h1).
- apply run_seq_skip.
- apply mrun_step with (i2:=i2) (h2:=h2).
  * assumption.
  * apply mrun_refl.
Qed.



Theorem mrun_transitivity: 
forall i1 i2 i3 h1 h2 h3,
Run (i1, h1) (i2, h2) ->
Run (i2, h2) (i3, h3) ->
Multi_Run (i1, h1) (i3, h3).
Proof.
intros.
apply mrun_step with (i2:=i2) (h2:=h2).
- assumption.
- apply run_imp_mrun.
  assumption.
Qed.



Theorem unit_skip_l:
  forall i1 h1 x,
  Multi_Run (i1, h1) x ->
  Multi_Run (Seq Skip i1, h1) x.
Proof.
  intros.
  transitivity (i1,h1). (* apply m_run_trans with (y:=). *)
  - apply run_imp_mrun.
    apply run_seq_skip.
  - assumption.
Qed.


(* Run (Seq Sync Skip) h2 Skip h2 ==> h2 = [] *)

Lemma sync_imp_emptyhist:
forall h i h',
Run (Sync, h) (i, h') ->
h' = [].
Proof.
intros.
inversion H.
reflexivity.
Qed.


(*
Theorem seq_mrun:
  forall i1 i2 i3 h1 h2 h3,
  Run i1 h1 i2 h2 ->
  Run i2 h2 i3 h3 ->
  MRun (Seq i1 i3, h1) (i3, h3).
Proof.
intros.
apply m_run_def.
apply mrun_step with (i2:=i3) (h2:=h3).
- apply run_seq.

generalize dependent i3.
generalize dependent h3.
inversion H; subst.
- intros.
  apply m_run_def.
  eapply mrun_step.
  * 
inversion H0; subst; clear H0.
induction H2.
  - apply m_run_def.
    eapply mrun_step.
      * 
  - *)

Theorem unit_skip_r:
  forall i1 h1 h2,
  Multi_Run (i1, h1) (Skip, h2) ->
  Multi_Run (Seq i1 Skip, h1) (Skip, h2).
Proof.
intros.
inversion H; subst; clear H.
- apply mrun_step with (i2:=Skip) (h2:=h2).
  * apply run_seq_skip.
  * apply mrun_refl.
- 

induction i1.
- inversion H1; subst.
  * apply m_run_def.
    apply mrun_step with (i2:=Skip) (h2:=h2).
      + apply run_seq_skip.
      + assumption.
  * inversion H.
- admit.
- admit.
- apply m_run_def.
  apply mrun_step with (i2:=Skip) (h2:=h2).  * destruct H1.
    + admit.
    + apply run_seq in H.
inversion H1; subst.
  * apply m_run_def.
    eapply mrun_step.
    + 
     
       
    + apply mrun_refl.

    inversion H3.
    apply mrun_step with (i2:=Skip) (h2:=h2).
      + apply run_seq.
      + assumption.
    

apply m_run_def.
induction i1.
- inversion H3; subst.
  * apply run_imp_mrun.
    apply run_seq_skip.
  * inversion H.
- 
  


Theorem unit_skip:
forall i1 i2 h1 h2,
Multi_Run i1 h1 i2 h2 ->
Multi_Run (Seq Skip i1) h1 i2 h2.
Proof.
intros.

