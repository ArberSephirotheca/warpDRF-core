Set Implicit Arguments.

Section Defs.
    Variable A: Type.
    Inductive state :=
    | Empty: state
    | Leaf: A -> state
    | Par: state -> state -> state.
End Defs.

Arguments Empty {A}.

Section Props.
  Variable A : Type.
  Notation state := (state A).
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
    step_is_value_true:
      forall a : A, a_is_value a = true -> red_leaf a = None;
  }.
  Context {C:Lang}.

  Definition is_par (s:state) :=
  match s with
  | Par _ _ => true
  | _ => false
  end.

  Definition is_halted_leaf s :=
  match s with
  | Leaf a => a_is_value a
  | _ => false
  end.

  Definition is_par_l_leaf s :=
   match s with
   | Par (Leaf a) _ => a_is_value a
   | _ => false
   end.

  Inductive Step: state -> state -> Prop :=
  (* Leaf reduction *)
  | step_leaf:
    forall a s,
    AStep a s ->
    Step (Leaf a) s

  (* Par reduction *)
  | step_par_l:
    (*

            s1 --> s2
      ---------------------
      s1 || s3 ==> s2 || s3

     *)
    forall s1 s2 s3,
    is_par s1 = false ->
    Step s1 s2 -> 
    Step (Par s1 s3) (Par s2 s3)
  | step_par_empty:
    (*

      {} || s ==> s

     *)
    forall (s:state),
    Step (Par Empty s) s
  | step_par_r:
    (*

                     s1 --> s2
        -----------------------------------
        (h, skip) || s1 ==> (h, skip) || s2

     *)
    forall a s1 s2,
    a_is_value a = true ->
    Step s1 s2 ->
    Step (Par (Leaf a) s1) (Par (Leaf a) s2)

  | step_par_par:
    forall s1 s2 s3,
    Step (Par (Par s1 s2) s3) (Par s1 (Par s2 s3)).

  Definition red_par f s1 s2 :=
    if is_halted_leaf s1 then
      match f s2 with
      | Some s3 => Some (Par s1 s3)
      | None => None
      end
    else
      match s1 with
      | Empty => Some s2
      | Par s3 s4 => Some (Par s3 (Par s4 s2))
      | _ =>
        match f s1 with
        | Some s3 => Some (Par s3 s2)
        | None => None
        end
      end.

  Inductive RedPar f: state -> state -> state -> Prop :=
  | red_par_1:
    forall s,
    RedPar f Empty s s
  | red_par_2:
    forall a s1 s2,
    f s1 = Some s2 ->
    a_is_value a = true ->
    RedPar f (Leaf a) s1 (Par (Leaf a) s2)
  | red_par_3:
    forall s1 s2 s3,
    RedPar f (Par s1 s2) s3 (Par s1 (Par s2 s3))
  | red_par_4:
    forall s1 s2 s3,
    is_par s1 = false ->
    f s1 = Some s3 ->
    RedPar f s1 s2 (Par s3 s2).

  Lemma red_par_inv_some:
    forall f s1 s2 s3,
    red_par f s1 s2 = Some s3 ->
    RedPar f s1 s2 s3.
  Proof.
    unfold red_par; intros.
    destruct s1.
    - inversion H.
      clear H.
      constructor.
    - destruct (is_halted_leaf (Leaf a)) eqn:Ha. {
        simpl in *.
        destruct (f _) eqn:Hf; inversion H; subst.
        constructor; auto.
      }
      destruct (f _) eqn:Hf; inversion H; subst; simpl in *.
      constructor; auto.
    - inversion H; subst; clear H.
      constructor.
  Qed.

  Lemma some_to_red_par f (f_none: f (@Empty A) = None) (f_some: forall (a:A) (s:state), f (@Leaf A a) = Some s -> a_is_value a = false)  (f_leaf_value: forall a, a_is_value a = true -> f (Leaf a) = None) :
    forall s1 s2 s3,
    RedPar f s1 s2 s3 ->
    red_par f s1 s2 = Some s3.
  Proof.
    intros.
    inversion H; simpl; auto; clear H.
    - subst.
      unfold red_par.
      assert (Hx: is_halted_leaf (Leaf a) = true) by auto.
      rewrite Hx.
      rewrite H0.
      reflexivity.
    - subst.
      destruct s1; simpl in *; try rewrite H0; auto.
      + rewrite f_none in *.
        inversion H1.
      + unfold red_par.
        assert (Hx: a_is_value a = false) by eauto using f_some.
        simpl.
        rewrite Hx.
        destruct (f (Leaf a)) eqn:Hf. {
          inversion Hx; subst.
          inversion H1; subst; clear H1.
          reflexivity.
        }
        inversion H1.
      + inversion H0.
  Qed.

  Fixpoint step (s:state) : option state :=
  match s with
  | Leaf s => red_leaf s
  | Par s1 s2 => red_par step s1 s2
  | Empty => None
  end.

  Inductive Value: state -> Prop :=
  | value_skip:
    forall a,
    a_is_value a = true ->
    Value (Leaf a)
  | value_par:
    forall s1 s2,
    Value s1 ->
    Value s2 ->
    Value (Par s1 s2).

  Theorem step_to_prop:
    forall s1 s2,
    step s1 = Some s2 ->
    Step s1 s2.
  Proof.
    induction s1; intros; simpl in *.
    - inversion H.
    - apply red_leaf_to_a_step in H; constructor; auto.
    - apply red_par_inv_some in H.
      inversion H; subst; clear H; try (constructor; auto).
  Qed.

  Let step_leaf_to_is_value_false:
    forall (a : A) (s : state), step (Leaf a) = Some s -> a_is_value a = false.
  Proof.
    intros.
    simpl in *.
    eauto using step_to_is_value_false.
  Qed.

  Let a_is_value_true_to_step_none:
    forall a : A, a_is_value a = true -> step (Leaf a) = None.
  Proof.
    intros.
    simpl.
    eauto using step_is_value_true.
  Qed.

  Theorem prop_to_step:
    forall s1 s2,
    Step s1 s2 ->
    step s1 = Some s2.
  Proof.
    induction s1; intros; simpl; inversion H; clear H; simpl; auto; subst.
    - auto using a_step_to_red_leaf.
    - apply IHs1_1 in H4.
      apply some_to_red_par; auto.
      constructor; auto.
    - apply IHs1_2 in H4.
      apply some_to_red_par; auto.
      constructor; auto.
  Qed.

End Props.

