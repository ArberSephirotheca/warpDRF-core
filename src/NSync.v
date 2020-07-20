Require Import Coq.Lists.List.
(* Require Import Coq.Strings.String. *)
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
Require Import AccExp.
Require Import Util.
Require Aniceto.Graphs.Graph.
Require Import Tasks.
Require Import Hist.
Require Import Omega.
Require Import Lia.

Import ListNotations.


Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | If
  | Hole
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.


  
Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Sync => Sync
  | If => If
  | Hole => Hole
  | Seq i2 i3 => Seq (i_subst x v i2) (i_subst x v i3)
  | For y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    For y (r_subst x v r) i2'
  | Loop y r i2 =>
    let i2' := if VAR.eq_dec x y then i2 else i_subst x v i2 in
    Loop y r i2'
  end.


Notation history := (list access_val).

Notation mhistory := (list history).

(* Why can't I use this in the sig of Run? *)
Notation histpair := (mhistory * history).

Context `{T:Tasks}.


Inductive Run: ((mhistory * history) * inst) -> (mhistory * history) -> Prop :=
| run_skip:
    forall x,
    Run (x, Skip) x
| run_sync:
  forall h hs,
    Run ((hs, h), Sync) (h::hs, [])
| run_seq:
    forall i j x y z,
      Run (x, i) y ->
      Run (y,j) z ->
      Run (x, Seq i j) z
| run_for:
  forall r l v x y i,
    RStep r l ->
    Run (x, Loop v l i) y ->
    Run (x, For v r i) y
| run_loop_nil:
    forall x i y v,
    Run (x,i) y ->
    Run (x, Loop v [] i) y
| run_loop_cons:
    forall x i y v l n z,
      Run (x, i_subst v (NNum n) i) y ->
      Run (y, Loop v l i) z ->
      Run (x, Loop v (n::l) i) z.

Goal
  forall hs i x, 
  Run (hs, i) x ->
  Run (hs, Seq Skip i) x.
Proof.
  intros hs i x HR.
  apply run_seq with (y:=hs).
  - apply run_skip.
  - assumption.
Qed.

Goal
  forall hs i x, 
  Run (hs, i) x ->
  Run (hs, Seq i Skip) x.
Proof.
  intros hs i x HR.
  eapply run_seq; eauto.
  apply run_skip.
Qed.



Inductive NSEquiv : inst -> inst -> Prop :=
| equiv_unit_r:
    forall i j,
      NSEquiv i j ->
      NSEquiv (Seq Skip i) j
| equiv_unit_l:
    forall i j,
      NSEquiv i j ->
      NSEquiv (Seq i Skip) j
| equiv_assoc:
    forall x y z x' y' z',
      NSEquiv x x' ->
      NSEquiv y y' ->
      NSEquiv z z' ->
      NSEquiv (Seq x (Seq y z)) (Seq (Seq x' y') z')
| equiv_eq:
    forall x,
      NSEquiv x x
| equiv_seq:
    forall x y x' y',
      NSEquiv x x' ->
      NSEquiv y y' ->
      NSEquiv (Seq x y) (Seq x' y')
| equiv_for:
    forall x y r l,
      NSEquiv x y ->
      NSEquiv (For l r x) (For l r y)
| equiv_loop:
    forall x y l r,
      NSEquiv x y ->
      NSEquiv (Loop l r x) (Loop l r y).


Notation nsequivstar := (clos_refl_sym_trans_n1 _ NSEquiv).

Global Add Parametric Relation : _ nsequivstar
    reflexivity proved by (rstn1_refl inst NSEquiv)                                   
    symmetry proved by (clos_rstn1_sym inst NSEquiv)
    transitivity proved by (clos_rstn1_trans inst NSEquiv)
      as nsequivstar_setoid.

Lemma i_subst_equiv:
  forall i j,
    NSEquiv i j ->
    forall v n,
    NSEquiv (i_subst v (NNum n) i) (i_subst v (NNum n) j).
Proof.
  intros i j HE.
  induction HE.
  - intros. simpl. assert (IHHE:= IHHE v n).
    apply equiv_unit_r.
    assumption.
  -  intros. simpl. assert (IHHE:= IHHE v n).
    apply equiv_unit_l.
    assumption.
  - intros. simpl.
    assert (IHHE1 := IHHE1 v n).
    assert (IHHE2 := IHHE2 v n).
    assert (IHHE3 := IHHE3 v n).
    apply equiv_assoc; assumption.
  - intros. apply equiv_eq.
  - intros.
    assert (IHHE1 := IHHE1 v n).
    assert (IHHE2 := IHHE2 v n).
    simpl.
    apply equiv_seq; assumption.
  - intros.
    assert (IHHE := IHHE v n).
    simpl.
    apply equiv_for.
    destruct (Set_VAR.MF.eq_dec v l); assumption.
  - intros.
    simpl.
    assert (IHHE:=IHHE v n).
    apply equiv_loop.
    destruct (Set_VAR.MF.eq_dec v l); assumption.
Qed.
        

  
Lemma equiv_one_run_l:
  forall x ht,
    Run x ht ->
    forall hs i,
      x = (hs, i) ->
      forall j,
      NSEquiv i j ->
      Run (hs, j) ht.
Proof.
  intros x ht HR.
  induction HR.
  - intros; inversion H; subst; clear H;
    inversion H0; subst; clear H0. apply run_skip.
  - intros; inversion H; subst; clear H;
    inversion H0; subst; clear H0. apply run_sync.
  - intros; inversion H; subst; clear H;
      inversion H0; subst; clear H0.
    + assert (HS: y = hs). {
        inversion HR1. reflexivity.
      }
      subst.
      assert (IHHR2:= IHHR2 hs j eq_refl j0 H3).
      assumption.
    + assert (HS: y = z). {
        inversion HR2. reflexivity.
      }
      subst.
      assert (IHHR1:= IHHR1 hs i eq_refl j0 H3).
      assumption.
    + assert (IHHR1:= IHHR1 hs i eq_refl x' H2).
      assert (HE: NSEquiv (Seq y0 z0) (Seq y' z')). {
        apply equiv_seq; assumption.
      }
      assert (IHHR2:= IHHR2 y (Seq y0 z0) eq_refl (Seq y' z') HE).
      inversion IHHR2; subst; clear IHHR2.
      apply run_seq with (y:=y1).
      * eapply run_seq; eauto.
      * assumption.
    + assert (Hi: NSEquiv i i) by auto using equiv_eq.
      assert (Hj: NSEquiv j j) by auto using equiv_eq.
      assert (IHHR1 := IHHR1 hs i eq_refl i Hi).
      assert (IHHR2 := IHHR2 y j eq_refl j Hj).
      eapply run_seq; eauto.
    + assert (IHHR1 := IHHR1 hs i eq_refl x' H2).
      assert (IHHR2 := IHHR2 y j eq_refl y' H4).
      eapply run_seq; eauto.
  - intros. inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    + eapply run_for; eauto.
    + assert (HE: NSEquiv (Loop v l i) (Loop v l y0)) by auto using equiv_loop.
      assert (IHHR:=IHHR hs (Loop v l i) eq_refl (Loop v l y0) HE).
      eapply run_for; eauto.
 
  - intros; inversion H; subst; clear H;
      inversion H0; subst; clear H0.
    + apply run_loop_nil. assumption.
    + assert (IHHR := IHHR hs i eq_refl y0 H4).
      apply run_loop_nil. assumption.
  - intros; inversion H; subst; clear H;
      inversion H0; subst; clear H0.
    + eapply run_loop_cons; eauto.
    + assert (HE: NSEquiv (Loop v l i) (Loop v l y0)) by auto using equiv_loop.
      assert (IHHR2 := IHHR2 y (Loop v l i) eq_refl (Loop v l y0) HE).
      eapply run_loop_cons; eauto.
      assert (HES: NSEquiv (i_subst v (NNum n) i) (i_subst v (NNum n) y0)). {
        apply i_subst_equiv.
        assumption.
      }
      assert (IHHR1 := IHHR1 hs (i_subst v (NNum n) i) eq_refl (i_subst v (NNum n) y0) HES).
      assumption.
Qed.


Lemma run_i_skip:
  forall i hs,
    NSEquiv i Skip ->
    Run (hs, i) hs.
Proof.
  intros.
  induction i.
  - apply run_skip.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + apply run_seq with (y:=hs).
      * apply run_skip.
      * apply IHi2 in H3. assumption.
    + apply run_seq with (y:=hs).
      * apply IHi1 in H3. assumption.
      * apply run_skip.
  - inversion H.
  - inversion H.
Qed.
    

Lemma run_i_sync:
  forall j,
    NSEquiv j Sync ->
    forall h hs,
      Run (hs, h, j) (h :: hs, []).
Proof.
  intro j.
  induction j.
  - intros HE h. inversion HE.
  - intros. apply run_sync.
  - intros HE h hs. inversion HE.
  - intros HE h hs. inversion HE.
  - intros HE h hs. inversion HE; subst.
    + apply run_seq with (y:=(hs,h)).
      * apply run_skip.
      * eapply IHj2 in H2; eauto.
    + apply run_seq with (y:=(h::hs, [])).
      * eapply IHj1 in H2; eauto.
      * apply run_skip.
  - intros HE h hs. inversion HE.
  - intros HE h hs. inversion HE.
Qed.


Lemma run_i_for:
  forall j' v r i l,
    NSEquiv j' (For v r i) ->
    RStep r l ->
    forall y h',
    (forall j, NSEquiv j (Loop v l i) -> Run (h', j) y) ->
    Run (h', Loop v l i) y ->
    Run (h', j') y.
Proof.
  intros jh.
  induction jh; intros vh rh ih lh HE; inversion HE; subst; clear HE.
  - intros.
    eapply IHjh2 in H2; eauto.
    apply run_seq with (y:=h').
    + apply run_i_skip. apply equiv_eq.
    + assumption.
  - intros.
    eapply IHjh1 in H2; eauto.
    + apply run_seq with (y:=y).
      * assumption.
      * apply run_i_skip. apply equiv_eq.
  - intros.
    eapply run_for; eauto.
  - intros.
    assert (HEQ: NSEquiv (Loop vh lh jh) (Loop vh lh ih)). {
      apply equiv_loop.
      assumption.
    }
    assert (H1 := H1 (Loop vh lh jh) HEQ).
    eapply run_for; eauto.
Qed.


Lemma run_i_loop_nil:
  forall j v i h' y,
  NSEquiv j (Loop v [] i) ->
  (forall j : inst, NSEquiv j i -> Run (h', j) y) ->
  Run (h', i) y -> 
  Run (h', j) y.
Proof.
  intros j.
  induction j; intros vh ih hh yh HE;
    inversion HE; subst; clear HE.
  - intros.
    eapply IHj2 in H2; eauto.
    apply run_seq with (y:=hh).
    + apply run_i_skip. apply equiv_eq.
    + assumption.
  - intros.
    eapply IHj1 in H2; eauto.
    apply run_seq with (y:=yh).
    + assumption.
    + apply run_i_skip.
      apply equiv_eq.
  - intros.
    apply run_loop_nil.
    assumption.
  - intros.
    apply run_loop_nil.
    apply H in H0.
    assumption.
Qed.


Lemma run_i_loop_cons:
  forall k v n l i z h' y,
  NSEquiv k (Loop v (n :: l) i) ->
  Run (h', i_subst v (NNum n) i) y ->
  Run (y, Loop v l i) z ->
  (forall j : inst, NSEquiv j (i_subst v (NNum n) i) -> Run (h', j) y) ->
  (forall j : inst, NSEquiv j (Loop v l i) -> Run (y, j) z) ->
  Run (h', k) z.
Proof.
  intros k.
  induction k;
    intros vn nn ln i0 zn hn yn HE; inversion HE; subst; clear HE.
  - intros.
    eapply IHk2 in H1; eauto.
    apply run_seq with (y:=hn).
    + apply run_i_skip. apply equiv_eq.
    + assumption.
  - intros.
    eapply IHk1 in H1; eauto.
    apply run_seq with (y:=zn).
    + assumption.
    + apply run_i_skip. apply equiv_eq.
  - intros.
    eapply run_loop_cons; eauto.
  - intros.
    apply run_loop_cons with (y:=yn).
    + assert (H2 := H2 (i_subst vn (NNum nn) k)).
      assert (HEQ: NSEquiv (i_subst vn (NNum nn) k) (i_subst vn (NNum nn) i0)). {
        apply i_subst_equiv.
        assumption.
      }
      apply H2 in HEQ.
      assumption.
    + assert (H3 := H3 (Loop vn ln k)).
      assert (HEQ: NSEquiv (Loop vn ln k) (Loop vn ln i0)). {
        apply equiv_loop.
        assumption.
      }
      apply H3 in HEQ.
      assumption.
Qed.

Lemma run_i_seq:
  forall k i j h' y z,
  NSEquiv k (Seq i j) ->
  Run (h', i) y ->
  Run (y, j) z -> 
  (forall j : inst, NSEquiv j i -> Run (h', j) y) ->
  (forall j0 : inst, NSEquiv j0 j -> Run (y, j0) z) ->
  Run (h', k) z.
Proof.
  intros k.
  induction k;
    intros ih jh hh yh zh HE; inversion HE; subst; clear HE.
  - intros.
    eapply IHk2 in H2; eauto.
    apply run_seq with (y:=hh).
    + apply run_i_skip. apply equiv_eq.
    + assumption.
  - intros.
    eapply IHk1 in H2; eauto.
    apply run_seq with (y:=zh).
    + assumption.
    + apply run_i_skip. apply equiv_eq.
  - intros.
    inversion H; subst; clear H.
    assert (HEQ: NSEquiv (Seq k1 y) (Seq x' y')). {
      apply equiv_seq; assumption.
    }
    apply H1 in HEQ.
    apply H2 in H5.
    inversion HEQ; subst; clear HEQ.
    apply run_seq with (y:=y1).
    + assumption.
    + apply run_seq with (y:= yh); assumption.
  - intros.
    apply run_seq with (y:= yh); assumption.
  - intros.
    apply run_seq with (y:= yh).
    + apply H1 in H2. assumption.
    + apply H3 in H4. assumption.
Qed.
    
    

      
Lemma equiv_one_run_r:
  forall x ht,
    Run x ht ->
    forall hs i,
      x = (hs, i) ->
      forall j,
      NSEquiv j i ->
      Run (hs, j) ht.
Proof.
  intros x ht HR.
  induction HR.
  - intros hs i Hx j HE.
    inversion Hx; subst; clear Hx.
    apply run_i_skip.
    assumption.
  - intros h' i Hx j HE.
    inversion Hx; subst; clear Hx.
    auto using run_i_sync.
  - intros h' i' Hx j' HE.
    inversion Hx; subst; clear Hx.
    assert (IHHR1 := IHHR1 h' i eq_refl).
    assert (IHHR2 := IHHR2 y j eq_refl).
    eapply run_i_seq; eauto.
  - intros h' i' Hx j' HE.
    inversion Hx; subst; clear Hx.
    assert (IHHR := IHHR h' (Loop v l i) eq_refl).
    eapply run_i_for; eauto.
  - intros h' i' Hx j' HE.
    inversion Hx; subst; clear Hx.
    assert (IHHR := IHHR h' i eq_refl).
    eapply run_i_loop_nil; eauto.
  - intros h' i' Hx j' HE.
    inversion Hx; subst; clear Hx.
    assert (IHHR1 := IHHR1 h' (i_subst v (NNum n) i) eq_refl).
    assert (IHHR2 := IHHR2 y (Loop v l i) eq_refl).
    eapply run_i_loop_cons; eauto.
Qed.
    

    

Lemma equiv_star_run:
  forall i j,
    nsequivstar i j ->
    forall hs x,
    Run (hs, i) x ->
    Run (hs, j) x.
Proof.
  intros i j HE.
  induction HE.
  - intros. assumption.
  - intros hs x HR.
    apply IHHE in HR.
    destruct H as [Hyz | Hzy].
    + eapply equiv_one_run_l; eauto.
    + eapply equiv_one_run_r; eauto.
Qed.


Inductive Unsync : inst -> Prop :=
| unsync_skip:
    Unsync Skip
| unsync_if:
    Unsync If
| unsync_hole:
    Unsync Hole
| unsync_seq:
    forall i j, 
      Unsync i ->
      Unsync j ->
  Unsync (Seq i j)
| unsync_for:
    forall v r i,
      Unsync i ->
      Unsync (For v r i)
| unsync_loop:
    forall v r i,
      Unsync i ->
      Unsync (Loop v r i).



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


Theorem none_normalisable_unsync:
  forall i,
  Normalised i (None, i) ->
  Unsync i.
Proof.
intros.
induction i; inversion H; assumption.
Qed.


Inductive In : inst -> inst -> Prop :=
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
      In k (Loop v r i)
| in_refl:
    forall x,
      In x x.

Theorem some_normalisable_in_sync:
  forall i i1 i2,
  Normalised i (Some i1, i2) ->
  In Sync i.
Proof.
intros i.
induction i; intros; inversion H; subst; auto using in_refl. 
- apply IHi2 in H5. apply IHi1 in H3. 
  auto using in_seq_l.
- apply IHi2 in H5.
  auto using in_seq_r.
- apply IHi1 in H5. 
  auto using in_seq_l.
- apply IHi in H1.
  auto using in_for.
- apply IHi in H1.
  auto using in_loop.
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
  apply in_refl.
- left.
  apply unsync_if.
- left.
  apply unsync_hole.
- destruct IHi1; destruct IHi2.
    + left.
      apply unsync_seq; assumption.
    + right.
      apply in_seq_r; assumption.
    + right.
      apply in_seq_l; assumption.
    + right. 
      apply in_seq_l; assumption.
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
  - assert (HA: ~In Sync If). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
  - intro.
    assert (HA: ~In Sync Hole). 
    { 
      unfold not.
      intro.
      inversion H.
    }
    contradiction.
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

Lemma in_sync_to_not_unsync:
  forall i,
  In Sync i ->
  ~ Unsync i.
Proof.
  induction i; intros; intros N; inversion H; subst; clear H;
    inversion N; subst; clear N.
  - apply IHi1 in H2; contradiction.
  - apply IHi2 in H2; contradiction.
  - apply IHi in H2; contradiction.
  - apply IHi in H2; contradiction.
Qed.




(* Normalisation is NOT a function in general! *)
Lemma norm_fun_unsync:
  forall i i2,
  Unsync i ->
  Normalised i (None, i2) ->
  forall j2,
  Normalised i (None, j2)  ->
  (i2 = j2).
Proof.
intros i i2 HUS HN. 
intros j2 HM.
induction i; inversion HN; subst; inversion HM; auto; subst.
- inversion HUS. 
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
- inversion HUS; subst.
  apply some_normalisable_in_sync in H0.
  apply in_sync_to_not_unsync in H0.
  subst. contradict H0. assumption.
Qed.
