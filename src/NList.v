Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Util.
Import ListNotations.

Section Defs.
  Variable A:Type.
  Inductive nlist :=
  | n_one: A -> nlist
  | n_cons: A -> nlist -> nlist.

  Fixpoint list_to_nlist (l:list A) : option nlist :=
  match l with
  | [x] => Some (n_one x)
  | x::l =>
    match list_to_nlist l with
    | Some l => Some (n_cons x l)
    | None => None
    end
  | [] => None
  end.

  Fixpoint nlist_to_list (l:nlist) : list A :=
  match l with
  | n_one x => [x]
  | n_cons x l => x :: (nlist_to_list l)
  end.

  Lemma nlist_to_list_rw_cons:
    forall a l,
    nlist_to_list (n_cons a l) = a::nlist_to_list l.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma list_to_nlist_rw_cons:
    forall a b l,
    list_to_nlist (a :: b :: l) =
    match list_to_nlist (b :: l) with
    | Some l => Some (n_cons a l)
    | None => None
    end.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.
  
  Lemma list_to_nlist_rw:
    forall l,
    list_to_nlist (nlist_to_list l) = Some l.
  Proof.
    induction l; intros. {
      simpl.
      reflexivity.
    }
    rewrite nlist_to_list_rw_cons.
    destruct l. {
      simpl.
      reflexivity.
    }
    rewrite nlist_to_list_rw_cons.
    rewrite list_to_nlist_rw_cons.
    rewrite <- nlist_to_list_rw_cons.
    rewrite IHl.
    reflexivity.
  Qed.

  Lemma nlist_to_list_rw:
    forall l l',
    list_to_nlist l = Some l' ->
    nlist_to_list l' = l.
  Proof.
    induction l; intros. {
      inversion H; subst; clear H.
    }
    destruct l. {
      inversion H; subst; clear H.
      reflexivity.
    }
    rewrite list_to_nlist_rw_cons in H.
    destruct (list_to_nlist (_ :: _)) eqn:R. {
      assert (IHl := IHl n eq_refl).
      inversion H.
      subst.
      simpl.
      rewrite IHl.
      reflexivity.
    }
    inversion H.
  Qed.

  Definition is_nil (l:list A) :=
    match l with
    | [] => true
    | _ => false
    end.

  Definition list_to_nlist_ex (x:A) (l:list A) : nlist :=
  match list_to_nlist l with
  | Some l => l
  | None => n_one x
  end.

  Lemma neq_nil_to_nlist:
    forall l,
    l <> [] ->
    exists l',
    list_to_nlist l = Some l'.
  Proof.
    induction l; intros. {
      contradiction.
    }
    destruct l. {
      eexists.
      reflexivity.
    }
    destruct IHl. {
      intros N; inversion N.
    }
    rewrite list_to_nlist_rw_cons.
    rewrite H0.
    eauto.
  Qed.

End Defs.

Arguments n_one _ x.
Arguments n_cons _ x l.

Section Extra.
  Fixpoint fold_right {A B:Type} (f:B->A->A) (a:A) (l:nlist B) :=
  match l with
  | n_one x => f x a
  | n_cons x l => f x (fold_right f a l)
  end.

  Lemma fold_right_spec:
    forall A B (f:B->A->A) l a,
    fold_right f a l = List.fold_right f a (nlist_to_list l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Fixpoint app {A:Type} (l1 l2:nlist A) :=
    match l1 with
    | n_one x => n_cons x l2
    | n_cons x l1 => n_cons x (app l1 l2)
    end. 

  Lemma app_spec:
    forall A l1 l2,
    nlist_to_list (@app A l1 l2) = List.app (nlist_to_list l1) (nlist_to_list l2).
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl1.
    reflexivity.
  Qed.

  Fixpoint map {A B:Type} (f:A -> B) l :=
    match l with
    | n_one x => n_one (f x)
    | n_cons x l => n_cons (f x) (map f l)
    end.

  Lemma map_spec:
    forall A B (f:A->B) l,
    nlist_to_list (map f l) = List.map f (nlist_to_list l).
  Proof.
    induction l; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

  Definition prepend {A:Type} (l1:nlist A) (l2: list (nlist A)) : list (nlist A) :=
    List.map (fun x => app l1 x) l2.

  Definition list_nlist_to_list {A:Type} :=
    List.map (@nlist_to_list A).

  Lemma prepend_spec:
    forall A (l2:list (nlist A)) (l1:nlist A),
    list_nlist_to_list (@prepend A l1 l2) =
      Util.prepend (nlist_to_list l1) (list_nlist_to_list l2).
  Proof.
    induction l2; intros. {
      simpl.
      reflexivity.
    }
    simpl.
    rewrite IHl2.
    rewrite app_spec.
    reflexivity.
  Qed.

  Lemma list_nlist_to_list_app:
    forall A l1 l2,
    @list_nlist_to_list A (l1 ++ l2)
    = list_nlist_to_list l1 ++ list_nlist_to_list l2.
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    rewrite IHl1.
    reflexivity.
  Qed.

  Definition prod {A:Type} (l1 l2: list (nlist A)) : list (nlist A) :=
    List.fold_right (fun x accum => prepend x l2 ++ accum) [] l1.

  Lemma prod_spec:
    forall A l1 l2,
    list_nlist_to_list (@prod A l1 l2) =
    Util.prod (list_nlist_to_list l1) (list_nlist_to_list l2).
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    rewrite list_nlist_to_list_app.
    rewrite prepend_spec.
    rewrite IHl1.
    reflexivity.
  Qed.

  Definition head {A:Type} (l:nlist A) :=
    match l with
    | n_one x | n_cons x _ => x
    end.
(*
  Fixpoint combine {A B:Type} (l:nlist A) (l':nlist B) :=
  let p := (head l, head l') in
  match l, l' with
  | n_cons _ l, n_cons _ l' => n_cons p (combine l l')
  | _, _ => n_one p
  end.

  Definition map2 {A B C:Type} (f:A->B->C) l1 l2 :=
    map
      (fun (p:A * B) => let (v1,v2) := p in f v1 v2)
      (combine l1 l2).
*)
(*
  Definition map2_prod {A:Type} := Util.map2 (@prod A).
*)
  Definition list_list_nlist_to_list {A:Type} :=
    List.map (@list_nlist_to_list A).

  Lemma list_list_nlist_to_list_cons_rw:
    forall A l1 l2,
    @list_list_nlist_to_list A (l1 :: l2) =
    list_nlist_to_list l1 :: list_list_nlist_to_list l2.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma map2_prod_spec:
    forall A l1 l2,
    list_list_nlist_to_list (Util.map2 (@prod A) l1 l2) =
    map2 Util.prod (list_list_nlist_to_list l1) (list_list_nlist_to_list l2).
  Proof.
    induction l1; intros. {
      reflexivity.
    }
    simpl.
    destruct l2. {
      simpl.
      rewrite map2_nil_r.
      reflexivity.
    }
    rewrite list_list_nlist_to_list_cons_rw.
    rewrite map2_cons_rw.
    rewrite map2_cons_rw.
    rewrite <- IHl1.
    rewrite list_list_nlist_to_list_cons_rw.
    rewrite prod_spec.
    reflexivity.
  Qed.

End Extra.