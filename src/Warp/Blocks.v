From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import Var.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store Code Model Order Agree.

Import ListNotations.

(* In a well-sited kernel an instance is one dynamic block: it forms at most
   one group, and no thread arrives after its release. A loop body is run
   again in each iteration, so the invariant is stated on running code: the
   rest of each iteration names a site at most once, and the code after a
   part names none of the sites that part may still run. *)

Lemma nodup_app_disjoint : forall {A} (l1 l2 : list A) a,
  NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
  intros A l1 l2 a H Hin1 Hin2. induction l1 as [|b l1 IH]; [contradiction|].
  cbn in H. apply NoDup_cons_iff in H as [Hb H].
  destruct Hin1 as [->|Hin1]; [apply Hb, in_or_app; right; exact Hin2|exact (IH H Hin1)].
Qed.

Lemma sites_subst : forall c x value, sites (subst x value c) = sites c.
Proof.
  induction c; intros x value; cbn; try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - apply IHc.
  - now rewrite IHc1, IHc2.
  - destruct (VAR.eq_dec x v); [reflexivity|now rewrite IHc].
  - destruct (VAR.eq_dec x v); [reflexivity|now rewrite IHc].
Qed.

Lemma static_subst : forall c x value, static (subst x value c) = static c.
Proof.
  induction c; intros x value; cbn; try reflexivity.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
  - now rewrite IHc1, IHc2.
  - now rewrite IHc1, IHc2.
  - apply IHc.
  - destruct (VAR.eq_dec x v); [reflexivity|apply IHc].
Qed.

Lemma reach_sites : forall c s w, reach c s w = true -> In s (sites c).
Proof.
  induction c; intros s w H; cbn in H |- *; try discriminate.
  - eapply IHc; eauto.
  - apply orb_true_iff in H as [H|H]; apply in_or_app; [left|right]; eauto.
  - apply orb_true_iff in H as [H|H]; apply in_or_app; [left|right]; eauto.
  - destruct w; [discriminate|]. eapply IHc; eauto.
  - destruct w as [|j w]; [discriminate|].
    apply orb_true_iff in H as [H|H]; apply andb_true_iff in H as [_ H];
      apply in_or_app; [left|right]; eauto.
  - apply orb_true_iff in H as [H|H].
    + apply andb_true_iff in H as [H _]. apply site_eqb_true in H. subst. left; reflexivity.
    + right. eapply IHc; eauto.
  - apply orb_true_iff in H as [H|H].
    + apply andb_true_iff in H as [H _]. apply site_eqb_true in H. subst. left; reflexivity.
    + right. eapply IHc; eauto.
Qed.

Lemma step_sites : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> incl (sites c') (sites c).
Proof.
  induction c; intros tid input m e m' c' H.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. rewrite sites_subst. apply incl_refl.
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. intros a [].
  - apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + apply incl_refl.
    + intros a [].
    + intros a [].
    + cbn. apply incl_app_app; [eapply IHc1; eauto|apply incl_refl].
  - cbn in H. destruct (b_step tid b) as [[]|]; try discriminate;
      inversion H; subst; cbn; [apply incl_appl|apply incl_appr]; apply incl_refl.
  - cbn in H. inversion H; subst. cbn. intros a Ha.
    apply in_app_iff in Ha as [Ha|Ha]; exact Ha.
  - apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]].
    + cbn. intros a Ha. apply in_app_iff in Ha as [Ha|Ha]; apply in_or_app; right; exact Ha.
    + intros a [].
    + cbn. apply incl_app_app; [eapply IHc1; eauto|apply incl_refl].
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H. match type of H with context [n_step ?t ?a] =>
      destruct (n_step t a) eqn:Harg end; try discriminate.
    inversion H; subst. apply incl_refl.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma resume_sites : forall c r x,
  at_collective c = Some x -> incl (sites (resume c r)) (sites c).
Proof.
  induction c; intros r x H; cbn in H; try discriminate.
  - cbn. apply incl_app_app; [eapply IHc1; eauto|apply incl_refl].
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    cbn. apply incl_app_app; [eapply IHc1; reflexivity|apply incl_refl].
  - cbn. rewrite sites_subst. intros a Ha. right. exact Ha.
Qed.

Fixpoint ws (c : code) : Prop :=
  match c with
  | Seq first rest =>
      ws first /\ static rest = true /\ NoDup (sites rest) /\
      (forall s, In s (sites first) -> ~ In s (sites rest))
  | Iter _ rest body => ws rest /\ static body = true /\ NoDup (sites body)
  | Wait _ _ _ _ _ body => static body = true /\ NoDup (sites c)
  | _ => static c = true /\ NoDup (sites c)
  end.

Lemma static_ws : forall c, static c = true -> NoDup (sites c) -> ws c.
Proof.
  induction c; intros Hstatic Hnodup; cbn in *; try (split; assumption).
  - apply andb_true_iff in Hstatic as [H1 H2].
    split; [apply IHc1; [exact H1|eapply NoDup_app_remove_r; exact Hnodup]|].
    split; [exact H2|]. split; [eapply NoDup_app_remove_l; exact Hnodup|].
    intros s Hs. eapply nodup_app_disjoint; eauto.
  - discriminate.
  - discriminate.
Qed.

Lemma step_ws : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') -> ws c -> ws c'.
Proof.
  induction c; intros tid input m e m' c' H Hws.
  - cbn in H. destruct (n_step tid n); try discriminate.
    inversion H; subst. cbn in Hws. destruct Hws as [Hs Hn].
    apply static_ws; [now rewrite static_subst|now rewrite sites_subst].
  - cbn in H. destruct (n_step tid n), (n_step tid n0); try discriminate.
    inversion H; subst. cbn. split; [reflexivity|constructor].
  - cbn in Hws. destruct Hws as [Hws1 [Hstatic [Hnodup Hdisj]]].
    apply step_seq_view in H as
      [[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[[-> [_ [_ ->]]]|[first' [Hfirst ->]]]]].
    + apply static_ws; assumption.
    + cbn. split; [reflexivity|constructor].
    + cbn. split; [reflexivity|constructor].
    + cbn. split; [eapply IHc1; eauto|]. split; [exact Hstatic|]. split; [exact Hnodup|].
      intros s Hs. apply Hdisj. eapply step_sites; eauto.
  - cbn in H. destruct (b_step tid b) as [[]|]; try discriminate;
      inversion H; subst; cbn in Hws; destruct Hws as [Hs Hn];
      apply andb_true_iff in Hs as [Hs1 Hs2]; apply static_ws; try assumption;
      [eapply NoDup_app_remove_r|eapply NoDup_app_remove_l]; exact Hn.
  - cbn in H. inversion H; subst. cbn in Hws |- *. destruct Hws as [Hs Hn].
    split; [apply static_ws; assumption|]. split; assumption.
  - cbn in Hws. destruct Hws as [Hws1 [Hs Hn]].
    apply step_iter_view in H as [[_ [_ [_ ->]]]|[[_ [_ [_ ->]]]|[rest' [Hrest ->]]]].
    + cbn. split; [apply static_ws; assumption|]. split; assumption.
    + cbn. split; [reflexivity|constructor].
    + cbn. split; [eapply IHc1; eauto|]. split; assumption.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H. match type of H with context [n_step ?t ?a] =>
      destruct (n_step t a) eqn:Harg end; try discriminate.
    inversion H; subst. cbn in Hws |- *. exact Hws.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma resume_ws : forall c r x, at_collective c = Some x -> ws c -> ws (resume c r).
Proof.
  induction c; intros r x H Hws; cbn in H; try discriminate.
  - cbn in Hws |- *. destruct Hws as [Hws1 [Hs [Hn Hdisj]]].
    split; [eapply IHc1; eauto|]. split; [exact Hs|].
    split; [exact Hn|]. intros s Hin. apply Hdisj. eapply resume_sites; [exact H|exact Hin].
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    cbn in Hws |- *. destruct Hws as [Hws1 [Hs Hn]].
    split; [eapply IHc1; [reflexivity|exact Hws1]|]. split; assumption.
  - cbn in Hws |- *. destruct Hws as [Hs Hn]. apply NoDup_cons_iff in Hn as [_ Hn].
    split; [split; [reflexivity|constructor]|].
    split; [now rewrite static_subst|]. split; [now rewrite sites_subst|].
    intros s [].
Qed.

(* After a release, the released thread can no longer reach the instance it
   left: the rest of the iteration does not name the site again, and the
   loop body names it only for later iterations. *)
Lemma resume_unreachable : forall c r s w value fn,
  ws c -> at_collective c = Some ((s, w), value, fn) -> reach (resume c r) s w = false.
Proof.
  induction c; intros r s w value fn Hws H; cbn in H; try discriminate.
  - cbn in Hws. destruct Hws as [Hws1 [_ [_ Hdisj]]].
    cbn [resume reach]. rewrite (IHc1 _ _ _ _ _ Hws1 H). cbn.
    destruct (reach c2 s w) eqn:Hr; [|reflexivity]. exfalso.
    apply (Hdisj s); [|exact (reach_sites _ _ _ Hr)].
    exact (reach_sites _ _ _ (at_collective_reach _ _ _ _ _ H)).
  - destruct (at_collective c1) as [[[[s1 v1] w1] f1]|] eqn:Hr; try discriminate.
    inversion H; subst. cbn in Hws. destruct Hws as [Hws1 _].
    cbn [resume reach]. rewrite Nat.eqb_refl, Nat.ltb_irrefl, (IHc1 _ _ _ _ _ Hws1 eq_refl).
    reflexivity.
  - inversion H; subst. cbn in Hws. destruct Hws as [_ Hn].
    apply NoDup_cons_iff in Hn as [Hnotin _].
    cbn [resume reach]. rewrite reach_subst. cbn.
    destruct (reach c (Site n b) []) eqn:Hr; [|reflexivity]. exfalso.
    apply Hnotin. exact (reach_sites _ _ _ Hr).
Qed.

Lemma in_replace_thread : forall (codes : list code) tid c d,
  In d (replace_thread tid c codes) -> d = c \/ In d codes.
Proof.
  induction codes as [|x codes IH]; intros [|tid] c d Hin; cbn in Hin; auto.
  - destruct Hin as [<-|Hin]; auto. right; right; exact Hin.
  - destruct Hin as [<-|Hin]; [right; left; reflexivity|].
    destruct (IH _ _ _ Hin); auto. right; right; assumption.
Qed.

Lemma advance_ws : forall input a st e st',
  advance input a st = Some (e, st') -> Forall ws (threads st) -> Forall ws (threads st').
Proof.
  intros input [tid|i] st e st' Hstep Hws; rewrite Forall_forall in Hws |- *.
  - apply thread_view in Hstep as [c [o [m' [c' [Hc [Hthread [_ ->]]]]]]].
    intros d Hin. cbn in Hin. apply in_replace_thread in Hin as [->|Hin].
    + eapply step_ws; [exact Hthread|apply Hws; eapply nth_error_In; exact Hc].
    + apply Hws; exact Hin.
  - apply release_view in Hstep as [_ [_ [_ ->]]].
    intros d Hin. cbn in Hin. apply In_nth_error in Hin as [t Ht].
    rewrite release_nth in Ht.
    destruct (nth_error (threads st) t) as [c|] eqn:Hc; [|discriminate].
    cbn in Ht. inversion Ht; subst d. apply nth_error_In in Hc.
    unfold release_one. destruct (at_collective c) as [[[i' value] fn]|] eqn:Hat;
      [|apply Hws; exact Hc].
    destruct (instance_eqb i i'); [|apply Hws; exact Hc].
    eapply resume_ws; [exact Hat|apply Hws; exact Hc].
Qed.

(* When no thread may reach an instance, no later step releases it. *)
Lemma unreachable_instance_never_released : forall input st trace last i,
  execution input st trace last ->
  (forall c, In c (threads st) -> may_reach i c = false) ->
  groups_at i trace = [].
Proof.
  intros input st trace last i Hexec.
  induction Hexec as [st|a st e st' trace last Hstep Hexec IH]; intros Hfar;
    [reflexivity|].
  assert (Hfar' : forall c, In c (threads st') -> may_reach i c = false).
  { destruct a as [tid|j].
    - apply thread_view in Hstep as [c [o [m' [c' [Hc [Hthread [_ ->]]]]]]].
      intros d Hin. cbn in Hin. apply in_replace_thread in Hin as [->|Hin];
        [|apply Hfar; exact Hin].
      destruct (may_reach i c') eqn:Hr; [|reflexivity].
      pose proof (step_may_reach _ _ _ _ _ _ _ _ Hthread Hr) as Hback.
      rewrite (Hfar c (nth_error_In _ _ Hc)) in Hback. discriminate.
    - apply release_view in Hstep as [_ [_ [_ ->]]].
      intros d Hin. cbn in Hin. apply In_nth_error in Hin as [t Ht].
      rewrite release_nth in Ht.
      destruct (nth_error (threads st) t) as [c|] eqn:Hc; [|discriminate].
      cbn in Ht. inversion Ht; subst d. apply nth_error_In in Hc.
      destruct (may_reach i (release_one j (supplied j (threads st)) t c)) eqn:Hr;
        [|reflexivity].
      pose proof (release_one_may_reach _ _ _ _ _ Hr) as Hback.
      rewrite (Hfar c Hc) in Hback. discriminate. }
  specialize (IH Hfar').
  destruct a as [tid|j].
  - apply thread_view in Hstep as [_ [o [_ [_ [_ [_ [-> _]]]]]]].
    destruct o; exact IH.
  - apply release_view in Hstep as [Harrived [_ [-> _]]]. cbn.
    destruct (instance_eqb i j) eqn:Hij; [|exact IH].
    apply instance_eqb_true in Hij. subst j. exfalso.
    destruct (arrived i (threads st)) as [|t rest] eqn:Ha; [contradiction|].
    assert (Hin : In t (arrived i (threads st))) by (rewrite Ha; left; reflexivity).
    apply select_spec in Hin as [c [Hc Hw]].
    pose proof (waits_at_reaches _ _ Hw) as Hreach.
    rewrite (Hfar c (nth_error_In _ _ Hc)) in Hreach. discriminate.
Qed.

(* Each instance forms at most one group. After a release, the group's
   threads have moved past the instance, and every other thread could not
   reach it, so no thread can arrive later. *)
Theorem instance_released_once : forall input st trace last,
  execution input st trace last -> Forall ws (threads st) ->
  forall i, length (groups_at i trace) <= 1.
Proof.
  intros input st trace last Hexec.
  induction Hexec as [st|a st e st' trace last Hstep Hexec IH]; intros Hws i;
    [cbn; lia|].
  pose proof (advance_ws _ _ _ _ _ Hstep Hws) as Hws'.
  destruct a as [tid|j].
  - apply thread_view in Hstep as [_ [o [_ [_ [_ [_ [-> _]]]]]]].
    destruct o; apply IH; exact Hws'.
  - apply release_view in Hstep as [Harrived [Hunknown [-> Hst']]]. cbn.
    destruct (instance_eqb i j) eqn:Hij; [|apply IH; exact Hws'].
    apply instance_eqb_true in Hij. subst j.
    assert (Hfar : forall c, In c (threads st') -> may_reach i c = false).
    { rewrite Hst'. cbn. intros d Hin. apply In_nth_error in Hin as [t Ht].
      rewrite release_nth in Ht.
      destruct (nth_error (threads st) t) as [c|] eqn:Hc; [|discriminate].
      cbn in Ht. inversion Ht; subst d.
      destruct (waits_at i c) eqn:Hw.
      - apply waits_at_true in Hw as [value [fn Hat]].
        rewrite (release_one_waiting _ _ _ _ _ _ Hat).
        destruct i as [s w]. unfold may_reach. cbn [fst snd].
        rewrite Forall_forall in Hws.
        exact (resume_unreachable _ _ _ _ _ _ (Hws c (nth_error_In _ _ Hc)) Hat).
      - rewrite (release_one_other _ _ _ _ Hw).
        eapply enabled_release_excludes; eauto. }
    rewrite (unreachable_instance_never_released _ _ _ _ _ Hexec Hfar). cbn. lia.
Qed.

Corollary well_sited_groups_unique : forall input programs trace last,
  well_sited programs -> execution input (initial programs) trace last ->
  forall i, length (groups_at i trace) <= 1.
Proof.
  intros input programs trace last Hwell Hexec i.
  apply (instance_released_once _ _ _ _ Hexec); cbn.
  apply Forall_forall. intros c Hc. unfold well_sited in Hwell. rewrite Forall_forall in Hwell.
  destruct (Hwell c Hc) as [Hstatic Hnodup]. now apply static_ws.
Qed.

Corollary reference_groups_unique : forall fuel input programs trace last,
  run fuel input programs = Some (trace, last) -> forall i, length (groups_at i trace) <= 1.
Proof.
  intros fuel input programs trace last Hrun i.
  apply run_sound in Hrun as [Hwell [Hexec _]].
  exact (well_sited_groups_unique _ _ _ _ Hwell Hexec i).
Qed.
