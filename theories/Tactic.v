Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect.
From gctt Require Import Axioms.


Local Ltac mysplit :=
  simpl;
  match goal with
  | |- _ ∧ _ => split
  | |- ∃ _: _, _ => esplit
  | |- _ ↔ _ => split
  end.

Ltac split := mysplit.



Ltac destruct_conjs :=
  repeat
    match goal with
    | H : ∃ _:_,_ |- _ => case: H => *
    | H : _ ∧ _ |- _ => case: H => *
    | H : _ * _ |- _ => case: H => * || destruct H
    end.


Ltac rewrite_ :=
  let x := fresh in
  move=> x; rewrite x; clear x.


Ltac specialize_clocks κ :=
  repeat
    match goal with
    | X : ∀ (κ : CLK), ?P |- _ => specialize (X κ)
    end.


Ltac destruct_eqs :=
  repeat
    match goal with
    | H : _ = _ |- _ => dependent destruction H
    end.


Ltac backthruhyp :=
  let H := fresh in
  match goal with
  | H : _ → ?P |- ?P => apply H
  end.

Ltac specialize_hyps :=
  repeat
    match goal with
    | H : ∀ κ : CLK, ?P, κ : CLK |- _ => specialize (H κ)
    | H : ?R (?e1, ?e2) -> ?P, H' : ?R (?e1, ?e2) |- _ => specialize (H H')
    end.


Theorem universal_extensionality :
  ∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x = Q x)
    → (∀ x, P x) = (∀ x, Q x).
Proof.
  move=> A P Q E.
  apply: propositional_extensionality; split => *.
  ++ rewrite -E. auto.
  ++ rewrite E. auto.
Qed.

Theorem later_extensionality :
  ∀ κ (P Q : Prop),
    (▷[κ] (P = Q))
    → (▷[κ] P) = (▷[κ] Q).
Proof.
  move=> κ P Q E.
  apply: propositional_extensionality.
  split => *; Later.gather; move=> [X Y].
  ++ rewrite -X; auto.
  ++ rewrite X; auto.
Qed.


Ltac reorient :=
  match goal with
  | H : ?Y = _ |- ?X = ?Y => symmetry; etransitivity; first eassumption
  end.

Ltac eqcd :=
  apply: universal_extensionality
  || apply: later_extensionality
  || apply: functional_extensionality.
