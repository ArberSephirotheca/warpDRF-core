From Stdlib Require Import Lists.List Arith.PeanoNat.
From Faial.Core Require Import NatUtil AVal.
From Faial.Core Require Mem.

(* Shared memory. Writes are immediately visible; a fixed input function
   supplies the initial value of every location. An observation records one
   access and the value it read or wrote. *)

Record observation := Observe {
  access : access_val;
  value : nat;
}.

Definition load (input : nat -> nat) (m : Mem.t) (address : nat) : nat :=
  match Map_NAT.find address m with
  | Some v => v
  | None => input address
  end.

Lemma load_after_write : forall input m address v,
  load input (Map_NAT.add address v m) address = v.
Proof.
  intros. unfold load. rewrite Map_NAT_Facts.add_eq_o by reflexivity. reflexivity.
Qed.

(* Replay an observed write; reads and control steps leave memory unchanged. *)
Definition effect (e : option observation) (m : Mem.t) : Mem.t :=
  match e with
  | Some (Observe a v) =>
      match av_mode a with
      | m_read => m
      | m_write => Map_NAT.add (av_index a) v m
      end
  | None => m
  end.

(* A read can be replayed in a memory that holds the value it observed. *)
Definition readable input m (e : option observation) : Prop :=
  match e with
  | Some (Observe a v) =>
      match av_mode a with
      | m_read => load input m (av_index a) = v
      | m_write => True
      end
  | None => True
  end.

Lemma effect_equiv : forall input m n e,
  (forall address, load input m address = load input n address) ->
  forall address, load input (effect e m) address = load input (effect e n) address.
Proof.
  intros input m n [[[t index mode] v]|] Heq address; cbn; auto.
  destruct mode; cbn; auto.
  unfold load in *. destruct (Nat.eq_dec index address); subst;
    [rewrite !Map_NAT_Facts.add_eq_o by reflexivity|
     rewrite !Map_NAT_Facts.add_neq_o by assumption]; auto.
Qed.

Lemma readable_equiv : forall input m n e,
  (forall address, load input m address = load input n address) ->
  readable input m e -> readable input n e.
Proof.
  intros input m n [[[t index mode] v]|] Heq Hr; cbn in *; auto.
  destruct mode; cbn in *; auto. now rewrite <- Heq.
Qed.

(* Two accesses are compatible when they touch different locations or both
   read. *)
Definition compatible (e f : option observation) : Prop :=
  forall x y, e = Some x -> f = Some y ->
  av_index (access x) <> av_index (access y) \/
  (av_mode (access x) = m_read /\ av_mode (access y) = m_read).

Lemma compatible_sym : forall e f, compatible e f -> compatible f e.
Proof.
  intros e f H y x Hy Hx. specialize (H x y Hx Hy). intuition congruence.
Qed.

Lemma nonconflicting_compatible : forall t u e f,
  t <> u ->
  (forall x, e = Some x -> av_owner (access x) = t) ->
  (forall y, f = Some y -> av_owner (access y) = u) ->
  (forall x y, e = Some x -> f = Some y -> ~ Conflict (access x) (access y)) ->
  compatible e f.
Proof.
  intros t u e f Hneq He Hf Hsafe x y Hx Hy.
  specialize (He _ Hx). specialize (Hf _ Hy). specialize (Hsafe _ _ Hx Hy).
  apply safe_not_conflict_rw in Hsafe. inversion Hsafe; intuition congruence.
Qed.

Lemma load_effect_other : forall input m e address,
  (forall o, e = Some o -> av_mode (access o) = m_write ->
    address <> av_index (access o)) ->
  load input (effect e m) address = load input m address.
Proof.
  intros input m [[[owner index mode] v]|] address H; cbn; auto.
  destruct mode; cbn; auto.
  unfold load. rewrite Map_NAT_Facts.add_neq_o; [reflexivity|].
  specialize (H (Observe (av_write owner index) v) eq_refl eq_refl).
  cbn in H. congruence.
Qed.

Lemma readable_effect : forall input m e f,
  compatible e f -> (readable input (effect e m) f <-> readable input m f).
Proof.
  intros input m e [[[owner index mode] v]|] H; cbn; try tauto.
  destruct mode; cbn; try tauto.
  rewrite load_effect_other; [tauto|].
  intros o Ho Hwrite.
  specialize (H o (Observe (av_read owner index) v) Ho eq_refl).
  cbn in H. intuition congruence.
Qed.

Lemma effects_commute : forall input m e f,
  compatible e f -> forall address,
  load input (effect e (effect f m)) address =
  load input (effect f (effect e m)) address.
Proof.
  intros input m [[[t x xm] v]|] [[[u y ym] w]|] H address; cbn; auto.
  destruct xm, ym; cbn; auto.
  assert (Hxy : x <> y).
  { specialize (H (Observe (av_write t x) v) (Observe (av_write u y) w)
      eq_refl eq_refl). cbn in H. intuition discriminate. }
  unfold load. destruct (Nat.eq_dec x address), (Nat.eq_dec y address);
    subst; try congruence;
    repeat first [rewrite Map_NAT_Facts.add_eq_o by reflexivity |
                  rewrite Map_NAT_Facts.add_neq_o by congruence];
    reflexivity.
Qed.
