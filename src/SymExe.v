Set Implicit Arguments.
Require Coq.Lists.List.

Section Props.
  Variable A : Type.
  Notation state := (list A).
  Class Lang := {
    AStep: A -> state -> Prop;
    a_is_value: A -> bool;
    red_leaf: A -> option state;
    red_leaf_to_a_step:
      forall a s,
      red_leaf a = Some s -> AStep a s;
    a_step_to_red_leaf:
      forall a s,
      AStep a s ->
      red_leaf a = Some s;
    step_to_is_value_false:
      forall (a : A) (s : state), red_leaf a = Some s -> a_is_value a = false;
  }.
  Context {C:Lang}.

  Inductive Step: state -> state -> Prop :=
  (* Leaf reduction *)
  | step_eq:
    forall a l1 l2,
    AStep a l1 ->
    Step (a::l2) (l1 ++ l2)

  | step_cons:
    forall a l1 l2,
    a_is_value a = true ->
    Step l1 l2 ->
    Step (a :: l1) (a :: l2).

  Fixpoint step (l:state) : option state :=
  match l with
  | cons x l2 =>
    if a_is_value x then
      match step l2 with
      | Some l2 => Some (cons x l2)
      | None => None
      end
    else
      match red_leaf x with
      | Some l1 => Some (app l1 l2)
      | None => None
      end
  | nil => None
  end.
  Definition Value := List.Forall (fun x => a_is_value x = true).

  Theorem step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    induction s1; intros; simpl in *.
    - inversion H.
    - destruct (a_is_value a) eqn:Ha. {
        destruct (step _) eqn:Hr. {
          inversion H; subst; clear H.
          apply step_cons; auto.
        }
        inversion H.
      }
      destruct (red_leaf _) eqn:Hr. {
        inversion H; subst.
        apply step_eq.
        apply red_leaf_to_a_step; auto.
      }
      inversion H.
  Qed.

  Theorem prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    induction s1; intros; simpl; inversion H; clear H; simpl; auto; subst.
    - apply a_step_to_red_leaf in H3.
      rewrite H3.
      assert (R: a_is_value a = false). {
        apply step_to_is_value_false with (s:=l1).
        assumption.
      }
      rewrite R.
      reflexivity.
    - rewrite H2.
      apply IHs1 in H4.
      rewrite H4.
      reflexivity.
  Qed.

End Props.

