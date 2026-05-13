Require Import NatUtil.

  Definition t := Map_NAT.t nat.
  Definition empty : t := Map_NAT.empty nat.
  Definition union (m1 m2: t) : t :=
    Map_NAT.map2 (fun o1 o2 =>
      match o1, o2 with
      | Some _, Some n
      | Some n, None
      | None, Some n => Some n
      | None, None => None
      end) m1 m2.
  Module MapsTo.

    Inductive t (idx:nat) : nat -> Mem.t -> (nat -> nat) -> Prop :=
    | defined:
      forall v f m,
      Map_NAT.MapsTo idx v m ->
      t idx v m f
    | undefined:
      forall f m,
      ~ Map_NAT.In idx m ->
      t idx (f idx) m f.

    Lemma read:
      forall idx m f,
      exists v, t idx v m f.
    Proof.
      intros.
      destruct (Map_NAT_Facts.In_dec m idx) as [hm|hm]. {
        apply Map_NAT_Extra.in_to_mapsto in hm.
        destruct hm as (x, hm).
        exists x.
        apply defined.
        assumption.
      }
      exists (f idx).
      apply undefined.
      assumption.
    Qed.
   End MapsTo.
