Require Import AccExp.
Require Import Tasks.
Require Import NSync.

Section Defs.

  Context {A:Access}.
  Context `{T:Tasks}.
 
Inductive Unsync : inst -> Prop :=
| unsync_skip:
    Unsync Skip
| unsync_if:
    forall b i,
      Unsync i ->
      Unsync (If b i)
| unsync_block:
    forall c,
    Unsync (Block c)
| unsync_seq:
    forall i j, 
      Unsync i ->
      Unsync j ->
  Unsync (Seq i j)
| unsync_for:
    forall v r i,
      Unsync i ->
      Unsync (For v r i).



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
      (*j1 = If (BExp.BBool true) i1 -> *)
      Normalised (For v r i) (Some (Seq i1 (For v r (Seq i2 i1))), i2)
| norm_if_true:
    forall i b i1 i2,
      Normalised i (Some i1, i2) ->
      Normalised (If b i) (Some (If b i1), If b i2)
| norm_if_false:
    forall i b i1 i2,
      Normalised i (Some i1, i2) ->
      Normalised (If b i) (None, Skip)
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
  | in_if_t:
    forall b k i j,
      In k i ->
      In k (If b i j)
| in_if_f:
    forall b k i j,
      In k j ->
      In k (If b i j)
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
- destruct IHi1; destruct IHi2.
    + left.
      apply unsync_if; assumption.
    + right.
      apply in_if_f; assumption.
    + right.
      apply in_if_t; assumption.
    + right.
      apply in_if_t; assumption.
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
  - intros.
    (* NEED TO FIGURE OUT WHAT TO DO HERE! *)
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


Fixpoint Merge  (i: option inst) (j: inst) :=
match i with
| None => j
| (Some n) => Seq n j
end.


Lemma unsync_src_norm:
  forall i j,
    Normalised i j->
    forall i1 i2,
      j = (i1, i2) ->
      forall h x,
        Run (h, i) x ->    
        Run (h, Merge i1 i2) x.
Proof.
  intros i j HN.
  induction HN; intros ih1 ih2 Hi hh xh HR; inversion Hi; subst; clear Hi; simpl.
  - assumption.
  - assert (HEQ: NSEquiv (Seq Sync Skip) Sync ). {
      apply equiv_unit_l.
      apply equiv_eq.
    }
    eapply equiv_one_run_r; eauto.
  - inversion HR; subst; clear HR.
    assert (IHHN1 := IHHN1 (Some i1) i2 eq_refl hh y H3).
    assert (IHHN2 := IHHN2 (Some j1) ih2 eq_refl y xh H4).
    simpl in *.
    inversion IHHN1; subst; clear IHHN1.
    inversion IHHN2; subst; clear IHHN2.
    eauto using run_seq.
  - inversion HR; subst; clear HR.
    assert (IHHN := IHHN (Some j1) ih2 eq_refl y xh H5).
    inversion IHHN; subst; clear IHHN.
    simpl in *.
    eauto using run_seq.
  - inversion HR; subst; clear HR.
    assert (IHHN := IHHN (Some i1) i2 eq_refl hh y H4).
    inversion IHHN; subst; clear IHHN.
    simpl in *.
    eauto using run_seq.
  - 
     
End Defs.
