Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Axiom CLK : Type.
Axiom LocalClock : ∃ κ : CLK, True.

Module Later.
  Axiom t : CLK -> Prop -> Prop.
  Axiom map : forall κ (p q : Prop), (p -> q) -> (t κ p -> t κ q).
  Axiom cart : ∀ κ (p q : Prop), t κ (p ∧ q) = ((t κ p) ∧ (t κ q)).

  Theorem join : ∀ κ p q, t κ p → t κ q → t κ (p ∧ q).
  Proof.
    move=> *.
    by [rewrite cart].
  Qed.

  Local Ltac elim_aux y :=
  lazymatch goal with
  | H1 : t ?κ _, H2 : t?κ _ |- _ =>
    let x := fresh in
    have := join H1 H2 => x;
    clear H1; clear H2;
    elim_aux x
  | |- t ?κ _ => apply: map y
  end.

  Ltac gather :=
    let x := fresh in elim_aux x.
End Later.

Notation "▷[ κ ] ϕ" := (Later.t κ ϕ) (at level 0).

(* True in any topos. *)
Axiom constructive_definite_description :
  forall (A : Type) (P : A->Prop),
    (exists! x, P x) -> { x : A | P x }.

Theorem dependent_unique_choice :
  forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).
Proof.
  move=> A B R H.
  eexists => x.
  apply: proj2_sig.
  apply: constructive_definite_description.
  auto.
Qed.


Theorem unique_choice :
  forall {A B:Type} (R:A -> B -> Prop),
    (forall x:A,  exists! y : B, R x y) ->
    (exists f : A -> B, forall x:A, R x (f x)).
Proof.
  move=> A B.
  apply: dependent_unique_choice.
Qed.


Axiom propositional_extensionality :
  ∀ (P Q : Prop),
    (P ↔ Q)
    -> P = Q.

Theorem binrel_extensionality :
  ∀ (T1 T2 : Type) (R1 R2 : T1 * T2 → Prop),
    (∀ x y, R1 (x, y) ↔ R2 (x, y))
    → R1 = R2.
Proof.
  move=> T1 T2 R1 R2 F.
  apply: functional_extensionality.
  move=> [x y].
  apply: propositional_extensionality.
  eauto.
Qed.
