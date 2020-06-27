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


Inductive Run: (inst * history) -> (inst * history) -> Prop :=
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
    + auto using run_imp_mrun.
    + eauto using mrun_step.
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


Inductive Normalised: inst -> (option inst * inst) -> Prop :=
| norm_unsync:
  forall i,
  Unsync i -> 
  Normalised i (None, i)
| norm_sync:
  Normalised Sync (Some Sync, Skip)
| norm_seq_dual:
  forall i i1 i2 j j1 j2,
  Normalised i (Some i1, i2) ->
  Normalised j (Some j1, j2) ->
  Normalised (Seq i j) (Some (Seq i1 (Seq i2 j1)), j2)
| norm_seq_r:
  forall i j j1 j2,
  Unsync i -> 
  Normalised j (Some j1, j2) ->
  Normalised (Seq i j) (Some (Seq i j1), j2)
| norm_seq_l:
  forall i i1 i2 j,
  Unsync j -> 
  Normalised i (Some i1, i2) ->
  Normalised (Seq i j) (Some i1, Seq i2 j)
| norm_for_step: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (For v r i) (Some (Seq i1 (For v r (Seq i2 i1))), i2) (* still needs to replace things here *)
| norm_for_nop: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (For v r i) (None, Skip)
| norm_loop_step: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (Loop v r i) (Some (Seq i1 (Loop v r (Seq i2 i1))), i2) (* still needs to replace things here *)
| norm_loop_nop: 
  forall v r i i1 i2,
  Normalised i (Some i1, i2) ->
  Normalised (Loop v r i) (None, Skip)
.

Theorem unsync_normalisable:
  forall i,
  Unsync i ->
  Normalised i (None, i).
Proof.
intros.
apply norm_unsync.
assumption.
Qed.


Lemma unsync_insync:
forall i,
Unsync i \/ In Sync i.
Proof.
intro.
induction i.
- left.
  apply unsync_skip.
- right.
  apply in_sync.
- destruct IHi1; destruct IHi2.
    + left.
      apply unsync_seq; assumption.
    + right.
      apply in_seq_r; assumption.
    + right.
      apply in_seq_l; assumption.
    + right. 
      apply in_seq_l; assumption.
- left.
  apply unsync_access.
- destruct IHi.
  * left. 
    apply unsync_for; assumption.
  * right.
    apply in_for; assumption.
- destruct IHi.
  * left. 
    apply unsync_loop; assumption.
  * right.
    apply in_loop; assumption.
Qed.


Theorem sync_normalisable:
  forall i,
  In Sync i ->
  exists i1 i2, 
  Normalised i (Some i1, i2).
Proof.
intros i.
induction i.
  - assert (HA: ~In Sync Skip). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
  - intro. 
    exists Sync.
    exists Skip.
    apply norm_sync.
  - intro.
    inversion H; subst; clear H.
    * apply IHi1 in H2. (*i |> i1 i2*)
      assert (EX: Unsync i2 \/ In Sync i2). { apply unsync_insync. }
      destruct EX.
      + (* unsync i2 *)
        inversion H2. inversion H0.
        exists x. exists (Seq x0 i2).
        auto using norm_seq_l.
      + apply IHi2 in H. (* sync i2 *)
        inversion H; clear H. inversion H0; clear H0.
        inversion H2; clear H2. inversion H0; clear H0.
        exists (Seq x1 (Seq x2 x)).
        exists x0.
        auto using norm_seq_dual.
   * apply IHi2 in H2. (*j |> j1 j2*)
     assert (EX: Unsync i1 \/ In Sync i1). { apply unsync_insync. }
     destruct EX; destruct H2 as (x, (y, APH)).
     + exists (Seq i1 x).
       exists y.
       auto using norm_seq_r.
     + apply IHi1 in H.
       destruct H as (x2, (y2, BPH)).
       exists (Seq x2 (Seq y2 x)).
       exists y.
       auto using norm_seq_dual.
  - assert (HA: ~In Sync (Access a)). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
  - intro. 
    inversion H; subst; clear H.
    apply IHi in H2.
    destruct H2 as (x, (y, AH)).
    exists (Seq x (For v r (Seq y x))). (*will need to inst here *)
    exists y.
    auto using norm_for_step.
 - intro. 
    inversion H; subst; clear H.
    apply IHi in H2.
    destruct H2 as (x, (y, AH)).
    exists (Seq x (Loop v l (Seq y x))). (*will need to inst here *)
    exists y.
    auto using norm_loop_step.
Qed.



(* sync_normalisable and unsync_normalisable *)
Theorem allnormalisable_or:
  forall i,
  (exists j1 j2, 
  (Normalised i (Some j1, j2)))
  \/ 
  exists j, 
  (Normalised i (None, j)).
Proof.
intros.
assert (EX: Unsync i \/ In Sync i). { apply unsync_insync. }
destruct EX.
- right.
  exists i.
  auto using unsync_normalisable. 
- left.
  auto using sync_normalisable. 
Qed.

Theorem allnormalisable:
  forall i,
  (exists j1 j2, 
  (Normalised i (j1, j2))).
Proof.
intro.
assert (EX: Unsync i \/ In Sync i). { apply unsync_insync. }
destruct EX.
- exists None. exists i.
  auto using unsync_normalisable. 
- apply sync_normalisable in H.
  eauto.
  destruct H as (i1, (i2, H1)).
  exists (Some i1).
  exists i2.
  assumption.
Qed.


Lemma mrun_sync:
  forall h,
  Multi_Run (Sync, h) (Skip, []).
Proof.
  intros.
  apply run_imp_mrun.
  apply run_sync.
Qed.
(*
Lemma mrun_seq_sync_skip:
  forall h,
  Multi_Run (Seq Sync Skip, h) (Sync, h).
Proof.
  intros.
  apply 
Qed.
*)

Lemma mrun_seq_skip:
  forall i h,
  Multi_Run (Seq Skip i, h) (i, h).
Proof.
  intros.
  apply run_imp_mrun.
  apply run_seq_skip.
Qed.

Lemma run_fun:
  forall x y,
  Run x y ->
  forall z,
  Run x z ->
  y = z.
Proof.
  intros x y H.
  induction H; intros; auto.
  - inversion H; subst; clear H.
    reflexivity.
  - inversion H0; subst; clear H0.
    assert (v0 = v) by eauto using gen_access_fun.
    subst.
    reflexivity.
  - inversion H0; subst; clear H0.
    + apply IHRun in H5.
      inversion H5; subst; clear H5.
      reflexivity.
    + inversion H; subst; clear H.
  - inversion H; subst; clear H.
    + inversion H4.
    + reflexivity.
  - inversion H0; subst; clear H0.
    assert (l0 = l) by eauto using r_step_fun.
    subst.
    reflexivity.
  - inversion H; subst; clear H.
    reflexivity.
  - inversion H; subst; clear H.
    reflexivity.
Qed.
(* If multi-run is performing a step, then we can decompose it. *)
Lemma multi_run_inv_step:
  forall i h1 j h2 i' h1',
  Multi_Run (i, h1) (j, h2) ->
  i <> j ->
  Run (i, h1) (i', h1') ->
  Multi_Run (i', h1') (j, h2).
Proof.
  intros.
  inversion H; subst; clear H.
  + contradiction.
  + assert (R: (i', h1') = (i2, h3)) by eauto using run_fun.
    inversion R; subst; auto.
Qed.

Lemma mrun_seq:
  forall i h j h' k,
  Run (i, h) (j, h') ->
  Multi_Run (Seq i k, h) (Seq j k, h').
Proof.
  intros.
  auto using run_imp_mrun, run_seq.
Qed.

Fixpoint Merge  (i: option inst) (j: inst) :=
match i with
| None => j
| (Some n) => Seq n j
end.

Theorem src_norm:
forall i x hi,
Run (i, hi) x ->
exists i1 i2,
Normalised i (i1, i2) /\
Multi_Run (Merge i1 i2, hi) x.
Proof.
intro i.
assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
  destruct EX as (j1, (j2, NH)).
induction NH; subst; intros.
- inversion H; subst.
  * exists None. exists Skip.
    split; simpl.
    + auto using norm_unsync. 
    + inversion H0.
  * exists None. exists (Seq i0 j).
    split; simpl.
    + auto using norm_unsync.
    + 
- exists (Some (Seq i1 (Seq i2 j0))).
  exists j3.
  split. 
    * apply norm_seq_dual; assumption.
    * simpl. 
     
induction H; subst; inversion NH; subst.
- exists None. exists j2. split.
  * assumption.
  * admit.
- exists (Some Sync). exists Skip. split.
  * assumption.
  * 
  
      

  
  
- admit. 
- 
generalize dependent x.
intros.

intros.
assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
destruct EX as (j1, (j2, NH)).
eexists.
eexists.
split.
- eassumption.
- inversion H; subst; clear H; inversion NH; subst; simpl.
  * inversion H1.
  * transitivity (Seq Skip Skip, @nil access_val). 
    + apply mrun_seq.
      apply run_sync.
    + apply mrun_step with (i2:= Skip) (h2:=[]).
      ++ apply run_seq_skip.
      ++ apply mrun_refl.
  * transitivity (Skip, List.concat  v++ hi).
    + apply mrun_step with (i2:=Skip) (h2:=List.concat  v++ hi).
       ++ apply run_access. 
          assumption.
       ++ apply mrun_refl.
    + apply mrun_refl.
  * apply mrun_step with (i2:=Seq j k) (h2:=h').
    + auto using run_seq.
    + apply mrun_refl.
  * apply mrun_step with (i2:= Seq j j2) (h2:=h').
    + apply run_seq.
      
  * inversion H2.
(* JL TO CONTINUE HERE *)
        apply run_access.
apply mrun_step with (i2:=Seq Skip Skip) (h2:=[]).
    + eapply run_seq.
      apply run_sync.
    + apply mrun_seq.
    + 
    + 
- assert (EX: exists j1 j2, Normalised i (j1, j2)). 
    {auto using allnormalisable. }
  destruct EX as (j1, (j2, NH)).
 

Theorem src_norm:
forall i x hi,
Run (i, hi) x ->
exists i1 i2,
Normalised i (Some i1, i2) /\
Multi_Run (Seq i1 i2, hi) x.
Proof.
intros i hi x H.
remember (i, x) as a.
generalize dependent Heqa.
induction H; subst; intros; inversion Heqa; subst; clear Heqa.
- eexists.
  eexists.
  split. {
    apply norm_sync.
  }
  transitivity (Seq Skip Skip, @nil access_val).
  + auto using mrun_seq, run_sync.
  + apply mrun_seq_skip.
- 
(* The conclusion is not strong enough, we need to change it to
   Normalized i (o, i2) /\ MultiRun (merge o i2, hi) x
   where
     merge None i = i
     merge (Some i) j = Seq i j 
   *)

  
- assert (CA: forall z1 z2, ~Normalised Skip (Some z1, z2)). {

- 
induction i.
- assert (Unsync Skip).
  * apply unsync_skip.
  * apply norm_unsync.



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

(*
Theorem run_seq_kip_r:
  forall i1 h1,
  Multi_Run (Seq i1 Skip, h1) (i1, h1).
Proof.
intros.
apply mrun_step with (i2:=i1) (h2:=h1).
- 
- apply mrun_refl.
*)

(*

Theorem unit_skip_r:
  forall i1 h1 h2,
  Multi_Run (i1, h1) (Skip, h2) ->
  Multi_Run (Seq i1 Skip, h1) (Skip, h2).
Proof.
intros.
induction i1; intros; apply mrun_step with (i2:=Skip) (h2:=h1).
  * apply run_seq_skip.
  * assumption.
  * 
- 
inversion H; subst; clear H.
- apply mrun_step with (i2:=Skip) (h2:=h2).
  * apply run_seq_skip.
  * apply mrun_refl.
- apply mrun_step with (i2:=Skip) (h2:=h2).
  * 
  * apply mrun_refl.

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

*)

