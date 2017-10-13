Require Import Unicode.Utf8.
From mathcomp Require Import ssreflect.


Local Ltac mysplit :=
  simpl;
  match goal with
  | |- _ ∧ _ => split
  | |- ∃ _: _, _ => esplit
  | |- _ ↔ _ => split
  end.

Ltac split := mysplit.



Ltac destruct_conjs :=
  repeat match goal with
  | H : ∃ _:_,_ |- _ => case: H => *
  | H : _ ∧ _ |- _ => case: H => *
  | H : _ * _ |- _ => destruct H
  end.
