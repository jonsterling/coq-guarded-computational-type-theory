Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.

From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

Axiom CLK : Type.
Axiom LocalClock : ∃ κ : CLK, True.

Module Later.
  Axiom t : CLK -> Prop -> Prop.
  Axiom map : forall κ (p q : Prop), (p -> q) -> (t κ p -> t κ q).
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
