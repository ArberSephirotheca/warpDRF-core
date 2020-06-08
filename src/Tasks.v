Require Import Var.
Require Import Omega.
Class Tasks := {
  TID_COUNT: nat;
  TID : var;
  T1: var;
  T2: var;
  t1_neq_tid: T1 <> TID;
  t2_neq_tid: T2 <> TID;
  t1_neq_t2: T1 <> T2;
  tid_count_ge_2: TID_COUNT >= 2;
}.

Ltac tasks_absurd :=
match goal with
| [ H: @T1 ?T = @T2 ?T |- _ ] => assert (@T1 T <> @T2 T) by auto using t1_neq_t2; contradiction
| [ H: @T2 ?T = @T1 ?T |- _ ] => assert (@T2 T <> @T1 T) by auto using t1_neq_t2; contradiction
| [ H: @TID ?T = @T2 ?T |- _ ] => assert (@TID T <> @T2 T) by auto using t2_neq_tid; contradiction
| [ H: @T2 ?T = @TID ?T |- _ ] => assert (@T2 T <> @TID T) by auto using t2_neq_tid; contradiction
| [ H: @TID ?T = @T1 ?T |- _ ] => assert (@TID T <> @T1 T) by auto using t1_neq_tid; contradiction
| [ H: @T1 ?T = @TID ?T |- _ ] => assert (@T1 T <> @TID T) by auto using t1_neq_tid; contradiction
end.


Ltac remove_eq ta tb :=
let H := fresh "H" in
destruct (Set_VAR.MF.eq_dec ta tb) as [H|H];
  try (tasks_absurd || contradiction ); simpl in *; clear H.
Section Defs.
  Context `{T:Tasks}.
  Lemma tid_count_1_lt:
    1 < TID_COUNT.
  Proof.
    assert (X := tid_count_ge_2).
    unfold ge in X.
    auto.
  Qed.

  Lemma other_task:
    forall n,
    n < TID_COUNT ->
    exists m, n <> m /\ m < TID_COUNT.
  Proof.
    intros.
    assert (Hx := tid_count_1_lt).
    inversion H; subst; clear H. {
      destruct n. {
        omega.
      }
      exists 0.
      omega.
    }
    exists m.
    omega.
  Qed.

End Defs.

