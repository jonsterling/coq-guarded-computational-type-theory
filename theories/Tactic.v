Require Import Unicode.Utf8 Program.Equality Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect.
From gctt Require Import Notation Axioms.

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
    | H : _ × _ |- _ => case: H => * || destruct H
    end.


Ltac rewrite_ :=
  let x := fresh in
  move=> x; rewrite x; clear x.


Ltac specialize_clocks κ :=
  repeat
    match goal with
    | X : ∀ (κ : 𝕂), ?P |- _ => specialize (X κ)
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
    | H : ∀ κ : 𝕂, ?P, κ : 𝕂 |- _ => specialize (H κ)
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



Ltac use H :=
  match goal with
  | |- ?ty1 =>
    let ty2 := type of H in
    replace ty1 with ty2;
    [ exact H | idtac ]
  end.


Ltac rewrites_with T :=
  move=> *; simpl; T;
  repeat (match goal with | [H : context[eq _ _] |- _] => rewrite H end);
  T;
  auto.

Ltac rewrites := rewrites_with idtac.
