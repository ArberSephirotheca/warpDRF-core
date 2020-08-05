Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.


Require Import Var.
Require Import Tid.
Require Import NExp.
Require Import BExp.
Require Import AccExp.
Require Import Tasks.
Require Import InUtil.

Require Import Lia.

Import ListNotations.
Require Conc.

Section C1.
  Context {A:Access}.
  Inductive inst :=
  | Skip
  | Sync
  | If: bexp -> inst -> inst
  | Block: Conc.inst -> inst
  | Seq: inst -> inst -> inst
  | For : var -> range -> inst -> inst
  | Loop : var -> list nat -> inst -> inst.



Fixpoint i_subst x v i :=
  match i with
  | Skip => Skip
  | Sync => Sync
  | Block c => Block (Conc.i_subst x v c)
  | If b i => If (b_subst x v b) (i_subst x v i)
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

Notation histpair := (mhistory * history) % type.

Context `{T:Tasks}.

(* ----------------------- PHASESET ------------------- *)

Inductive phaseset :=
| ph_one: history -> phaseset
| ph_many: history -> mhistory -> history -> phaseset.


Definition merge (p1 p2:phaseset): phaseset :=
match p1, p2 with
| ph_one h1, ph_one h2 => ph_one (h1 ++ h2)
| ph_one h1, ph_many h2 m2 t2 => ph_many (h1 ++ h2) m2 t2
| ph_many h1 m1 t1, ph_one h2 => ph_many h1 m1 (h1 ++ h2)
| ph_many h1 m1 t1, ph_many h2 m2 t2 =>
  ph_many h1 (m1 ++ (t1 ++ h2) :: m2) t2
end.

Definition phase_to_list (p:phaseset) : mhistory :=
match p with
| ph_one h => [h]
| ph_many h m t => h::m ++ [t]
end.

Inductive PIn a : phaseset -> Prop :=
| p_in_one: forall h,
  List.In a h ->
  PIn a (ph_one h)
| p_in_head: forall h m t,
  List.In a h ->
  PIn a (ph_many h m t)
| p_in_mid: forall h m t,
  MIn a m ->
  PIn a (ph_many h m t)
| p_in_tail: forall h m t,
  List.In a t ->
  PIn a (ph_many h m t)
  .

(* -------------------- RUN --------------------------- *)

Inductive Run2: inst -> phaseset -> Prop :=
| run2_skip:
  Run2 Skip (ph_one [])
| run2_sync:
  Run2 Sync (ph_many [] [] [])
| run2_block:
  forall c h,
  ~ Conc.Var TID c -> (* This is a well-formedness property; assume we have it *)
  Conc.RunAll TID_COUNT c h ->
  Run2 (Block c) (ph_one h)
| run2_seq: forall i j mh_i mh_j mh,
  Run2 i mh_i ->
  Run2 j mh_j ->
  merge mh_i mh_j = mh ->
  Run2 (Seq i j) mh
| run2_if_true: forall b i mh,
  BStep b true ->
  Run2 i mh ->
  Run2 (If b i) mh
| run2_if_false: forall b i,
  BStep b false ->
  Run2 (If b i) (ph_one [])
| run2_for_cons:
  forall e1 e2 n1 n2 i x h1 h2 h3,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 < n2 ->
  Run2 (i_subst x (NNum n1) i) h1 ->
  Run2 (For x (NNum (S n1), NNum n2) i) h2 ->
  merge h1 h2 = h3 ->
  Run2 (For x (e1, e2) i) h3
| run2_for_nil:
  forall x i e1 e2 n1 n2,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 >= n2 ->
  Run2 (For x (e1, e2) i) (ph_one []).

Inductive IIn (a:access_val) : inst -> Prop :=
| i_in_block: forall i,
  Conc.IIn a i ->
  IIn a (Block i)
| i_in_seq_l: forall i j,
  IIn a i ->
  IIn a (Seq i j)
| i_in_seq_r: forall i j,
  IIn a j ->
  IIn a (Seq i j)
| i_in_if: forall b i,
  BStep b true ->
  IIn a i ->
  IIn a (If b i)
 | i_in_for: forall e1 e2 i n1 n2 n x,
  NStep e1 n1 ->
  NStep e2 n2 ->
  n1 <= n < n2 ->
  IIn a (i_subst x (NNum n) i) ->
  IIn a (For x (e1,e2) i)
  .

Goal Run2 (Seq Sync Skip) (ph_many [] [] []).
Proof.
  eapply run2_seq.
  + apply run2_sync.
  + apply run2_skip.
  + reflexivity.
Qed.

Goal Run2 (Seq Sync Sync) (ph_many [] [[]] []).
Proof.
  eapply run2_seq.
  + apply run2_sync.
  + apply run2_sync.
  + reflexivity.
Qed.

Goal Run2 (Seq (Seq Sync Sync) Sync) (ph_many [] [[]; []] []).
Proof.
  eapply run2_seq.
  - eapply run2_seq.
    + apply run2_sync.
    + apply run2_sync.
    + reflexivity.
  - apply run2_sync.
  - reflexivity.
Qed.

Inductive Run: (histpair * inst) -> histpair -> Prop :=
| run_skip:
    forall x,
    Run (x, Skip) x
| run_sync:
  forall h hs,
    Run ((hs, h), Sync) (h::hs, [])
| run_block:
  forall c h1 h2 m,
  Conc.RunAll TID_COUNT c h1 ->
  Run ((m, h2), Block c) (m, h1 ++ h2) 
| run_seq:
    forall i j x y z,
      Run (x, i) y ->
      Run (y,j) z ->
      Run (x, Seq i j) z
| run_if_true:
    forall i b x y,
      BStep b true ->
      Run (x, i) y ->
      Run (x, If b i) y
| run_if_false:
    forall i b x,
      BStep b false ->
      Run (x, If b i) x
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

  Lemma p_in_inv_one: forall a h,
    PIn a (ph_one h) ->
    List.In a h.
  Proof.
    intros.
    inversion H; subst; auto.
  Qed.

  Lemma p_in_inv_many: forall a h m t,
    PIn a (ph_many h m t) ->
    List.In a h \/ MIn a m \/ List.In a t.
  Proof.
    intros.
    inversion H; subst; auto.
  Qed.

  Lemma p_in_inv_merge:
    forall a p1 p2,
    PIn a (merge p1 p2) ->
    PIn a p1 \/ PIn a p2.
  Proof.
    intros.
    destruct p1, p2; simpl in *.
    - apply p_in_inv_one in H.
      apply in_app_iff in H.
      destruct H; auto using p_in_one.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]].
      + apply in_app_iff in H.
        destruct H; auto using p_in_one, p_in_head.
      + auto using p_in_mid.
      + auto using p_in_tail.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]]; auto using p_in_head, p_in_mid.
      apply in_app_iff in H.
      destruct H; auto using p_in_head, p_in_one.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]]; auto using p_in_head, p_in_tail.
      apply m_in_inv_app in H.
      destruct H; auto using p_in_mid.
      assert (R: (l1 ++ l2) :: l3 = [l1++l2] ++ l3) by auto.
      rewrite R in H.
      apply m_in_inv_app in H.
      destruct H as [H|H]; auto using p_in_mid.
      apply m_in_inv_cons_nil in H.
      apply in_app_iff in H.
      destruct H; auto using p_in_tail, p_in_head.
  Qed.

  Lemma run_p_in_to_i_in:
    forall i h,
    Run2 i h ->
    forall a,
    PIn a h ->
    IIn a i.
  Proof.
    intros i h H.
    induction H; intros.
    - apply p_in_inv_one in H.
      contradiction.
    - apply p_in_inv_many in H.
      destruct H as [H|[H|H]]; try contradiction.
      apply m_in_nil in H.
      contradiction.
    - apply p_in_inv_one in H1.
      apply i_in_block.
      eapply Conc.run_all_to_i_in in H; eauto.
    - subst.
      apply p_in_inv_merge in H2.
      destruct H2; auto using i_in_seq_l, i_in_seq_r.
    - auto using i_in_if.
    - apply p_in_inv_one in H0.
      contradiction.
    - subst.
      apply p_in_inv_merge in H5.
      destruct H5 as [Hi|Hi].
      + eauto using i_in_for.
      + apply IHRun2_2 in Hi.
        inversion Hi; subst; clear Hi.
        eapply i_in_for with (n:=n); eauto.
        assert (n0 = S n1) by eauto using n_step_fun, n_step_num.
        assert (n3 = n2) by eauto using n_step_fun, n_step_num.
        subst.
        lia.
    - apply p_in_inv_one in H2.
      contradiction.
  Qed.
(*
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
      NSEquiv (Loop l r x) (Loop l r y)
| equiv_if:
    forall b x y x' y',
      NSEquiv x x' ->
      NSEquiv y y' ->      
      NSEquiv (If b x y) (If b x' y')
.


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
  - intros.
    assert (IHHE1 := IHHE1 v n).
    assert (IHHE2 := IHHE2 v n).
    simpl.
    apply equiv_if; assumption.
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
    + apply run_if_true; assumption.
    + assert (IHHR:=IHHR hs i eq_refl x' H5).
      apply run_if_true; assumption.
  - intros. inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    + apply run_if_false; assumption.
    + assert (IHHR:=IHHR hs j eq_refl y' H6).
      apply run_if_false; assumption.
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
      assert (IHHR1 := IHHR1 hs (i_subst v (NNum n) i)
                             eq_refl (i_subst v (NNum n) y0) HES).
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
    
Lemma run_i_ite_true:
  forall k b i j y h',
    NSEquiv k (If b i j) ->
    BStep b true ->
    (forall j : inst, NSEquiv j i -> Run (h', j) y) ->
    Run (h', i) y ->
    Run (h', k) y.
Proof.
  intro k.
  induction k; intros bh ih jh yh hh HE; inversion HE; subst; clear HE.
  - intros.
    eapply run_if_true; assumption.
  - intros.
    apply run_if_true.
    + assumption.
    + apply H0 in H1.
      assumption.
  - intros.
    apply run_seq with (y:=hh).
    + apply run_i_skip.
      apply equiv_eq.
    + eapply IHk2 in H2; eauto.
  - intros.
    eapply IHk1 in H2; eauto.
    eapply run_seq with (y:=yh); eauto.
    apply run_i_skip.
    apply equiv_eq.
Qed.


Lemma run_i_ite_false:
  forall k b i j y h',
    NSEquiv k (If b i j) ->
    BStep b false ->
    (forall j0 : inst, NSEquiv j0 j -> Run (h', j0) y) ->
    Run (h', j) y ->
    Run (h', k) y.
Proof.
  intro k.
  induction k; intros bh ih jh yh hh HE; inversion HE; subst; clear HE.
  - intros.
    eapply run_if_false; assumption.
  - intros.
    apply H0 in H6.
    apply run_if_false; assumption.
  - intros.
    apply run_seq with (y:=hh).
    + apply run_i_skip.
      apply equiv_eq.
    + eapply IHk2 in H2; eauto.
  - intros.
    eapply IHk1 in H2; eauto.
    eapply run_seq with (y:=yh); eauto.
    apply run_i_skip.
    apply equiv_eq.
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
    assert (IHHR:=IHHR h' i eq_refl).
    eapply run_i_ite_true; eauto.
  - intros h' i' Hx j' HE.
    inversion Hx; subst; clear Hx.
    assert (IHHR:=IHHR h' j eq_refl).
    eapply run_i_ite_false; eauto.
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
*)
End C1.