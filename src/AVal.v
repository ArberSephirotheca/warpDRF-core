Require Import Coq.Lists.List.
Require Import Tictac.
Require Import Coq.micromega.Lia.

Import ListNotations.
Section Defs.
  Inductive mode := m_read | m_write.

  Definition mode_eqb m1 m2 :=
  match m1, m2 with
  | m_read, m_read | m_write, m_write => true
  | _, _ => false
  end.

  (** One dimension *)
  Record access_val := {
    av_owner : nat;
    av_index: nat;
    av_mode: mode;
  }.

  Definition av_write (owner:nat) (index:nat) : access_val := {|
    av_owner := owner;
    av_index := index;
    av_mode := m_write;
  |}.

  Definition av_read (owner:nat) (index:nat) : access_val := {|
    av_owner := owner;
    av_index := index;
    av_mode := m_write;
  |}.

  Inductive Conflict (a1 a2:access_val) : Prop :=
  | conflict_l:
    av_owner a1 <> av_owner a2 ->
    av_index a1 = av_index a2 ->
    av_mode a1 = m_write ->
    Conflict a1 a2
  | conflict_r:
    av_owner a1 <> av_owner a2 ->
    av_index a1 = av_index a2 ->
    av_mode a2 = m_write ->
    Conflict a1 a2.

  Inductive Safe (a1 a2:access_val) : Prop :=
  | safe_owner:
    av_owner a1 = av_owner a2 ->
    Safe a1 a2
  | safe_index:
    av_index a1 <> av_index a2 ->
    Safe a1 a2
  | safe_mode:
    av_mode a1 = m_read ->
    av_mode a2 = m_read ->
    Safe a1 a2.

  Lemma safe_conflict_absurd:
    forall a1 a2,
    Safe a1 a2 ->
    Conflict a1 a2 ->
    False.
  Proof.
    intros a1 a2 H N.
    invc N.
    all: invc H.
    all: intuition.
    all: assert (N: m_write = m_read) by (rewrite H2 in *; auto).
    all: inversion N.
  Qed.

  Lemma safe_or_conflict:
    forall a1 a2,
    Safe a1 a2 \/ Conflict a1 a2.
  Proof.
    intros.
    assert (hx: av_owner a1 = av_owner a2 \/ av_owner a1 <> av_owner a2) by lia.
    destruct hx. {
      auto using safe_owner.
    }
    assert (hx: av_index a1 <> av_index a2 \/ av_index a1 = av_index a2) by lia.
    destruct hx. {
      auto using safe_index.
    }
    assert (hx: (av_mode a1 = m_read /\ av_mode a2 = m_read) \/ (av_mode a1 = m_write \/ av_mode a2 = m_write)). {
      destruct (av_mode a1); intuition.
      destruct (av_mode a2); intuition.
    }
    destruct hx as [(hx1, hx2)| [hx1 |hx2]].
    all: auto using safe_mode, conflict_l, conflict_r.
  Qed.

  Lemma safe_not_conflict_rw:
    forall a1 a2,
    ~ Conflict a1 a2 <-> Safe a1 a2.
  Proof.
    split; intros.
    - destruct (safe_or_conflict a1 a2); auto.
      contradiction.
    - intros N.
      eauto using safe_conflict_absurd.
  Qed.

  Lemma conflict_not_safe_rw:
    forall a1 a2,
    ~ Safe a1 a2 <-> Conflict a1 a2.
  Proof.
    split; intros.
    - destruct (safe_or_conflict a1 a2); auto.
      contradiction.
    - intros N.
      eauto using safe_conflict_absurd.
  Qed.

  Lemma a_safe_sym:
    forall a1 a2,
    Safe a1 a2 ->
    Safe a2 a1.
  Proof.
    intros.
    inversion H; auto using safe_mode, safe_owner, safe_index.
  Qed.

End Defs.
