
Tactic Notation "invc" ident(X) := inversion X; subst; clear X.

(**
  The `pick_hyp` tactics lets us find an hypothesis by type,
  rather than by name.
  
  The type may be given partially.
  
  When the type is given
  *)


Tactic Notation "with_any_hyp" uconstr(ty) tactic(cont) :=
  (* https://stackoverflow.com/questions/55992567/ *)
  first [
    (* iterate over all assumptions and try the following chain;
       the first chain that has success will make the whole thing
       succeed. *)
    match goal with
      H : _ |- _ =>
      (* Create a variable *)
      let X := fresh in
      (* Try to assign it to the given type/pattern *)
      pose (X := H : ty);
      (* If it succeeds, we no longer need X *)
      clear X;
      (* pass the assumption we found to the continuation cont *)
      cont H
    end
  | (* If the above fails, we want to hide the error message, because it
       might be confusing, so we fail and return a match error instead *)
    fail ].


(** Here is a usage example. *)
Goal forall P Q, P /\ Q -> Q.
Proof.
  intros.
  (* The following will fail with no applicable tactic *)
  (* pick_hyp (Q /\ Q) ltac:(fun H => idtac). *)

  (* we run some code, given by the ltac function:   *)
  with_any_hyp (_ /\ Q) ltac:(fun H =>
    destruct H as (Ha, Hb);
    apply Hb
  ).
Qed.


(**
  The `with_hyp` tactics lets us refer to a hypothesis by type,
  rather than by name.
  
  The `with_hyp` tactics will fail when you have more than one hypothesis
  with the same given type.
  
  The type may be given partially.
  *)


Tactic Notation "with_hyp" uconstr(ty) tactic(cont) :=
  let with_hyp_err x H H' :=
    let t1 := type of H in
    let t2 := type of H' in
    idtac "Expecting a single hypothesis of type " x " but found at least 2";
    idtac H  ":" t1;
    idtac H' ":" t2;
    fail 1
  in
  with_any_hyp ty ltac:(fun H =>
    (* If we do find an assumption, then we take its concrete type *)
    let ty := type of H in
    match goal with
      (* Check if there are more than one assumptions with that type *)
    | [ H: ty, H': ty |- _ ] => with_hyp_err ty H H' (* if there are, err *)
    | _ => cont H (* We are safe, there exactly one assumption with this type *)
    end
  ).


(** Here is a usage example. *)
Goal forall P Q, P /\ Q -> Q.
Proof.
  intros.
  (* we run some code, given by the ltac function:   *)
  with_hyp (_ /\ _) ltac:(fun H =>
    destruct H as (Ha, Hb);
    apply Hb
  ).
Qed.

(** A useful tactics that renames an assumption that matches a certain type. *)
Tactic Notation "rename_hyp" uconstr(ty) "as" ident(Y) :=
  with_hyp ty ltac:(fun H => rename H into Y).

Goal forall P Q, P /\ Q -> Q.
Proof.
  intros.
  (* We give a name to the assumption P /\ Q: *)
  rename_hyp (_ /\ _) as Hab.
  destruct Hab as (Ha, Hb).
  apply Hb.
Qed.

(** Invert; subst; clear the hypothesis with the given type. *)

Tactic Notation "invc_hyp" uconstr(ty) :=
  with_hyp ty ltac:(fun H => invc H).
