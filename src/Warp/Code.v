From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Faial.Core Require Import Var AVal NatUtil.
From Faial.Core Require Mem.
From Faial.Expr.SIMT.N Require Import Exp.
From Faial.Expr.SIMT.B Require Import Exp.
From Faial.Warp Require Import Store.

Import ListNotations.

(* Kernel code with structured loops. A loop repeats its body until a Break
   leaves it; Continue ends the current iteration early. Iter k rest body is a
   loop in progress: iteration k, with rest left to run in that iteration.
   Source programs use Loop; Iter appears as they run. *)
Inductive code :=
| Read : var -> nexp -> code -> code
| Write : nexp -> nexp -> code
| Seq : code -> code -> code
| Cond : bexp -> code -> code -> code
| Loop : code -> code
| Iter : nat -> code -> code -> code
| Break
| Continue
| Barrier : nat -> code
| AddZero : nat -> code
| Skip.

(* Substitute a value read into x. A Read binds its variable in its body, so an
   inner Read of the same variable shadows it. *)
Fixpoint subst x v (c : code) : code :=
  match c with
  | Read y address body =>
      Read y (n_subst x v address)
        (if VAR.eq_dec x y then body else subst x v body)
  | Write address contents => Write (n_subst x v address) (n_subst x v contents)
  | Seq first rest => Seq (subst x v first) (subst x v rest)
  | Cond test yes no => Cond (b_subst x v test) (subst x v yes) (subst x v no)
  | Loop body => Loop (subst x v body)
  | Iter k rest body => Iter k (subst x v rest) (subst x v body)
  | Break => Break
  | Continue => Continue
  | Barrier n => Barrier n
  | AddZero n => AddZero n
  | Skip => Skip
  end.

(* One step of one thread. A Break or Continue drops the rest of its sequence
   and ends the innermost iteration; the loop then exits or starts the next
   iteration. A collective does not step: the warp releases it (Model.v). *)
Fixpoint step (tid : nat) (input : nat -> nat) (m : Mem.t) (c : code)
    : option (option observation * Mem.t * code) :=
  match c with
  | Read x address body =>
      match n_step tid address with
      | Some a =>
          let v := load input m a in
          Some (Some (Observe (av_read tid a) v), m, subst x (NNum v) body)
      | None => None
      end
  | Write address contents =>
      match n_step tid address, n_step tid contents with
      | Some a, Some v =>
          Some (Some (Observe (av_write tid a) v), Map_NAT.add a v m, Skip)
      | _, _ => None
      end
  | Seq first rest =>
      match first with
      | Skip => Some (None, m, rest)
      | Break => Some (None, m, Break)
      | Continue => Some (None, m, Continue)
      | _ =>
          match step tid input m first with
          | Some (e, m', first') => Some (e, m', Seq first' rest)
          | None => None
          end
      end
  | Cond test yes no =>
      match b_step tid test with
      | Some b => Some (None, m, if b then yes else no)
      | None => None
      end
  | Loop body => Some (None, m, Iter 0 body body)
  | Iter k rest body =>
      match rest with
      | Skip | Continue => Some (None, m, Iter (S k) body body)
      | Break => Some (None, m, Skip)
      | _ =>
          match step tid input m rest with
          | Some (e, m', rest') => Some (e, m', Iter k rest' body)
          | None => None
          end
      end
  | Break | Continue | Barrier _ | AddZero _ | Skip => None
  end.

(* Codes that end an iteration or a sequence rather than step. *)
Definition ender (c : code) : bool :=
  match c with Skip | Break | Continue => true | _ => false end.

Lemma step_ender : forall tid input m c, ender c = true -> step tid input m c = None.
Proof. intros tid input m [] H; try discriminate; reflexivity. Qed.

Lemma step_seq_other : forall tid input m first rest,
  ender first = false ->
  step tid input m (Seq first rest) =
    match step tid input m first with
    | Some (e, m', first') => Some (e, m', Seq first' rest)
    | None => None
    end.
Proof. intros tid input m first rest H. destruct first; try discriminate; reflexivity. Qed.

Lemma step_iter_other : forall tid input m k rest body,
  ender rest = false ->
  step tid input m (Iter k rest body) =
    match step tid input m rest with
    | Some (e, m', rest') => Some (e, m', Iter k rest' body)
    | None => None
    end.
Proof. intros tid input m k rest body H. destruct rest; try discriminate; reflexivity. Qed.

Lemma step_not_ender : forall tid input m c e m' c',
  step tid input m c = Some (e, m', c') -> ender c = false.
Proof.
  intros tid input m c e m' c' H. destruct (ender c) eqn:Hend; [|reflexivity].
  now rewrite step_ender in H.
Qed.

Lemma step_seq_first : forall tid input m first rest e m' first',
  step tid input m first = Some (e, m', first') ->
  step tid input m (Seq first rest) = Some (e, m', Seq first' rest).
Proof.
  intros tid input m first rest e m' first' H.
  rewrite step_seq_other by (eapply step_not_ender; eauto). now rewrite H.
Qed.

Lemma step_iter_rest : forall tid input m k rest body e m' rest',
  step tid input m rest = Some (e, m', rest') ->
  step tid input m (Iter k rest body) = Some (e, m', Iter k rest' body).
Proof.
  intros tid input m k rest body e m' rest' H.
  rewrite step_iter_other by (eapply step_not_ender; eauto). now rewrite H.
Qed.

Lemma step_seq_view : forall tid input m first rest e m' c',
  step tid input m (Seq first rest) = Some (e, m', c') ->
  (first = Skip /\ e = None /\ m' = m /\ c' = rest) \/
  (first = Break /\ e = None /\ m' = m /\ c' = Break) \/
  (first = Continue /\ e = None /\ m' = m /\ c' = Continue) \/
  (exists first', step tid input m first = Some (e, m', first') /\ c' = Seq first' rest).
Proof.
  intros tid input m first rest e m' c' H.
  destruct (ender first) eqn:Hend.
  - destruct first; try discriminate; cbn in H; inversion H; subst.
    + right; left; repeat split.
    + right; right; left; repeat split.
    + left; repeat split.
  - rewrite step_seq_other in H by exact Hend.
    destruct (step tid input m first) as [[[ev mem] f']|] eqn:Hfirst; [|discriminate].
    inversion H; subst. right; right; right. eauto.
Qed.

Lemma step_iter_view : forall tid input m k rest body e m' c',
  step tid input m (Iter k rest body) = Some (e, m', c') ->
  ((rest = Skip \/ rest = Continue) /\ e = None /\ m' = m /\ c' = Iter (S k) body body) \/
  (rest = Break /\ e = None /\ m' = m /\ c' = Skip) \/
  (exists rest', step tid input m rest = Some (e, m', rest') /\ c' = Iter k rest' body).
Proof.
  intros tid input m k rest body e m' c' H.
  destruct (ender rest) eqn:Hend.
  - destruct rest; try discriminate; cbn in H; inversion H; subst.
    + right; left; repeat split.
    + left; repeat split; auto.
    + left; repeat split; auto.
  - rewrite step_iter_other in H by exact Hend.
    destruct (step tid input m rest) as [[[ev mem] r']|] eqn:Hrest; [|discriminate].
    inversion H; subst. right; right. eauto.
Qed.

(* A step's next operation depends only on the code; only a read's result
   depends on memory, and replaying that value reproduces the step. *)
Lemma step_replay : forall c tid input m e m' c',
  step tid input m c = Some (e, m', c') ->
  m' = effect e m /\ readable input m e /\
  (forall o, e = Some o -> av_owner (access o) = tid) /\
  (forall n, readable input n e ->
    step tid input n c = Some (e, effect e n, c')).
Proof.
  induction c; intros tid input m e m' c' H.
  - cbn in H. destruct (n_step tid n) eqn:Haddress; try discriminate.
    inversion H; subst. repeat split; try reflexivity.
    + intros o Ho; inversion Ho; reflexivity.
    + intros other Hread. cbn in Hread. cbn. rewrite Haddress, Hread. reflexivity.
  - cbn in H. destruct (n_step tid n) eqn:Haddress, (n_step tid n0) eqn:Hvalue;
      try discriminate.
    inversion H; subst. repeat split; try reflexivity.
    + intros o Ho; inversion Ho; reflexivity.
    + intros other _. cbn. rewrite Haddress, Hvalue. reflexivity.
  - apply step_seq_view in H as
      [[-> [-> [-> ->]]]|[[-> [-> [-> ->]]]|[[-> [-> [-> ->]]]|[first' [Hfirst ->]]]]].
    1-3: repeat split; try reflexivity; try (intros o Ho; discriminate);
      intros other _; reflexivity.
    destruct (IHc1 _ _ _ _ _ _ Hfirst) as [Hmem [Hread [Howner Hreplay]]].
    repeat split; try assumption.
    intros other Hread'. apply step_seq_first. now apply Hreplay.
  - cbn in H. destruct (b_step tid b) eqn:Htest; try discriminate.
    inversion H; subst. repeat split; try reflexivity.
    + intros o Ho; discriminate.
    + intros other _. cbn. rewrite Htest. reflexivity.
  - cbn in H. inversion H; subst. repeat split; try reflexivity;
      try (intros o Ho; discriminate); intros other _; reflexivity.
  - apply step_iter_view in H as
      [[[-> | ->] [-> [-> ->]]]|[[-> [-> [-> ->]]]|[rest' [Hrest ->]]]].
    1-3: repeat split; try reflexivity; try (intros o Ho; discriminate);
      intros other _; reflexivity.
    destruct (IHc1 _ _ _ _ _ _ Hrest) as [Hmem [Hread [Howner Hreplay]]].
    repeat split; try assumption.
    intros other Hread'. apply step_iter_rest. now apply Hreplay.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

Lemma step_equiv : forall tid input m n c e m' c',
  (forall address, load input m address = load input n address) ->
  step tid input m c = Some (e, m', c') ->
  exists n', step tid input n c = Some (e, n', c') /\
    (forall address, load input m' address = load input n' address).
Proof.
  intros tid input m n c e m' c' Heq Hstep.
  apply step_replay in Hstep as [-> [Hr [_ Hreplay]]].
  exists (effect e n). split.
  - apply Hreplay. eapply readable_equiv; eauto.
  - now apply effect_equiv.
Qed.

Theorem steps_swap : forall input t u m left right e m1 left' f m2 right',
  t <> u ->
  step t input m left = Some (e, m1, left') ->
  step u input m1 right = Some (f, m2, right') ->
  (forall x y, e = Some x -> f = Some y ->
    ~ Conflict (access x) (access y)) ->
  exists n1 n2,
  step u input m right = Some (f, n1, right') /\
  step t input n1 left = Some (e, n2, left') /\
  (forall address, load input n2 address = load input m2 address).
Proof.
  intros input t u m left right e m1 left' f m2 right' Hneq Hleft Hright Hsafe.
  apply step_replay in Hleft as [Hm1 [He [Howner Hleft]]].
  apply step_replay in Hright as [Hm2 [Hf [Howner' Hright]]].
  assert (Hcompat : compatible e f)
    by (eapply nonconflicting_compatible; eauto).
  subst m1 m2.
  exists (effect f m), (effect e (effect f m)).
  repeat split.
  - apply Hright. now apply (proj1 (readable_effect _ _ _ _ Hcompat)).
  - apply Hleft.
    apply (proj2 (readable_effect _ _ _ _ (compatible_sym _ _ Hcompat))).
    exact He.
  - apply effects_commute. exact Hcompat.
Qed.

Lemma step_enabled_memory : forall c tid input m e m' c' other,
  step tid input m c = Some (e, m', c') ->
  exists f n' next, step tid input other c = Some (f, n', next).
Proof.
  induction c; intros tid input m e m' c' other H.
  - cbn in H. destruct (n_step tid n) eqn:Haddress; try discriminate.
    cbn. rewrite Haddress. eauto.
  - cbn in H. destruct (n_step tid n) eqn:Haddress, (n_step tid n0) eqn:Hvalue;
      try discriminate.
    cbn. rewrite Haddress, Hvalue. eauto.
  - apply step_seq_view in H as [[-> _]|[[-> _]|[[-> _]|[first' [Hfirst ->]]]]].
    1-3: cbn; eauto.
    destruct (IHc1 _ _ _ _ _ _ other Hfirst) as [f [n' [next Hnext]]].
    exists f, n', (Seq next c2). now apply step_seq_first.
  - cbn in H. destruct (b_step tid b) eqn:Htest; try discriminate.
    cbn. rewrite Htest. eauto.
  - cbn. eauto.
  - apply step_iter_view in H as [[[-> | ->] _]|[[-> _]|[rest' [Hrest ->]]]].
    1-3: cbn; eauto.
    destruct (IHc1 _ _ _ _ _ _ other Hrest) as [f [n' [next Hnext]]].
    exists f, n', (Iter n next c2). now apply step_iter_rest.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
  - cbn in H; discriminate.
Qed.

(* Thread lists. *)

Fixpoint replace_thread (tid : nat) (c : code) (codes : list code) : list code :=
  match tid, codes with
  | 0, _ :: rest => c :: rest
  | S tid', first :: rest => first :: replace_thread tid' c rest
  | _, [] => []
  end.

Lemma replace_thread_length : forall codes tid c,
  length (replace_thread tid c codes) = length codes.
Proof. induction codes as [|first rest IH]; intros [|tid] c; cbn; auto. Qed.

Lemma replace_thread_other : forall codes tid other c,
  other <> tid -> nth_error (replace_thread tid c codes) other = nth_error codes other.
Proof.
  induction codes as [|first rest IH]; intros [|tid] [|other] c Hneq; cbn;
    try reflexivity; try (exfalso; apply Hneq; reflexivity).
  apply IH. congruence.
Qed.

Lemma replace_thread_same : forall codes tid c,
  tid < length codes -> nth_error (replace_thread tid c codes) tid = Some c.
Proof.
  induction codes as [|first rest IH]; intros [|tid] c Hlt; cbn in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma replace_threads_commute : forall codes t u c d,
  t <> u ->
  replace_thread u d (replace_thread t c codes) = replace_thread t c (replace_thread u d codes).
Proof.
  induction codes as [|head rest IH]; intros [|t] [|u] c d Hneq; cbn; try congruence.
  f_equal. apply IH. congruence.
Qed.

Lemma replace_thread_map : forall (f : code -> code) codes tid c,
  map f (replace_thread tid c codes) = replace_thread tid (f c) (map f codes).
Proof.
  intros f codes. induction codes as [|c codes IH]; intros [|tid] d; cbn; auto.
  now rewrite IH.
Qed.
