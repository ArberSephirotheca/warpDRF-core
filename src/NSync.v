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
      
    
    apply run_seq
    

      
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
    

Lemma equiv_one_run_r:
  forall j i,
  NSEquiv j i ->
  forall x ht,
    Run x ht ->
    forall hs,
      x = (hs, i) ->
      Run (hs, j) ht.
Proof.
  intros j i HE.
  induction HE.
  -  intros x0 h0 HR h' Hx; inversion Hx; subst.
     eapply IHHE in HR; eauto.
     eapply run_seq; eauto.
     apply run_skip.
  -  intros x0 h0 HR h' Hx; inversion Hx; subst.
     eapply IHHE in HR; eauto.
     eapply run_seq; eauto.
     apply run_skip.
  -  intros x0 h0 HR h' Hx; inversion Hx; subst.
     inversion HR; subst; clear HR.
     inversion H4; subst; clear H4.
     assert (IHHE1 := IHHE1 (h',x') y1 H6 h' eq_refl).
     assert (IHHE2 := IHHE2 (y1,y') y0 H7 y1 eq_refl).
     assert (IHHE3 := IHHE3 (y0,z') h0 H5 y0 eq_refl).
     eapply run_seq; eauto.
     eapply run_seq; eauto.
  -  intros x0 h0 HR h' Hx; inversion Hx; subst.
     assumption.
  -  intros x0 h0 HR h' Hx; inversion Hx; subst.
     inversion HR; subst; clear HR.
     assert (IHHE1 := IHHE1 (h',x') y0 H4 h' eq_refl).
     assert (IHHE2 := IHHE2 (y0,y') h0 H5 y0 eq_refl).
     eapply run_seq; eauto.
  - intros x0 h0 HR h' Hx; inversion Hx; subst.
    inversion HR; subst; clear HR.
    apply run_for with (l:=l0).
    + assumption.
    + assert  (HL: forall vs v hv hp, Run (hv, Loop v vs y) hp -> Run (hv, Loop v vs x) hp). {
        intros vs.
        induction vs.
        * intros.
          apply run_loop_nil.
          inversion H0; subst.
          assert (IHHE:=IHHE (hv, y) hp H7 hv eq_refl).
          assumption.
        * intros.
          inversion H0; subst.
          assert (IHvs := IHvs v y0 hp H10).
          assert (IHHE := IHHE (hv, y) y0).
          (* NEED TO define i_subst on histories somehow? *)
          admit.
      }
      assert (HL := HL l0 l h' h0 H6).
      assumption.
  - intros. (*Use HL above *).
          
    

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
    destruct H as [Hyz | Hzy].
    + apply IHHE in HR.
