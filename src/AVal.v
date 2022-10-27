Require Import Coq.Lists.List.
Require Import Tictac.

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

  Definition Conflict (a1 a2:access_val) :=
    av_owner a1 <> av_owner a2 /\
    av_index a1 = av_index a2 /\
    (av_mode a1 = m_write \/ av_mode a2 = m_write).

  Definition Safe (a1 a2:access_val) :=
    ~ Conflict a1 a2.

  Lemma a_safe_eq_tid:
    forall v1 v2,
    av_owner v1 = av_owner v2 -> 
    Safe v1 v2.
  Proof.
    intros.
    destruct v1 as (n1, n2, n3);
    destruct v2 as (n4, n5, n6).
    simpl in *; subst.
    unfold Safe.
    unfold not.
    intros N.
    unfold Conflict in *.
    destruct N as (N1,N2).
    simpl in *.
    intuition.
  Qed.

  Lemma a_safe_sym:
    forall a1 a2,
    Safe a1 a2 ->
    Safe a2 a1.
  Proof.
    unfold Safe.
    intros.
    unfold Conflict in *.
    unfold not.
    intuition.
  Qed.

End Defs.
