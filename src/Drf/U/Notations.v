From Faial.Drf.U Require Import Lang.
From Faial.Drf.U Require Import Subst.
From Faial.Drf.U Require Import CIn.
From Faial.Drf.U Require Import CSeq.

Module CLangNotations.
  Declare Scope lang_scope.
  Notation  "'FOR' x '∈' r '{' c '}' " := (For x r c) : lang_scope.
  Infix ";" := Seq (at level 50, only printing) : lang_scope.
  Notation "c [ x := v ]" := (f x v c) (at level 30, only printing) : lang_scope.
  Infix ";;" := c_seq (at level 50, only printing) : lang_scope.
  Infix "∈" := CIn (at level 30, only printing) : lang_scope.
  Infix "∈" := CPairIn (at level 30, only printing) : lang_scope.
End CLangNotations.
