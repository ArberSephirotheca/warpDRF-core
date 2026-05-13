From Stdlib Require Arith.Compare_dec.

From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FSetAVL.
From Stdlib Require Import Arith.Peano_dec.

Require Import Aniceto.Map.

From Stdlib Require FSets.FMapFacts.
From Stdlib Require Structures.OrderedTypeEx.
Module NAT := Stdlib.Structures.OrderedTypeEx.Nat_as_OT.
Module Map_NAT := FMapAVL.Make NAT.
Module Map_NAT_Facts := FMapFacts.Facts Map_NAT.
Module Map_NAT_Props := FMapFacts.Properties Map_NAT.
Module Map_NAT_Extra := MapUtil Map_NAT.
Module Set_NAT := FSetAVL.Make NAT.

Definition set_nat := Set_NAT.t.

Lemma nat_eq_rw:
  forall (k k':nat), NAT.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.
