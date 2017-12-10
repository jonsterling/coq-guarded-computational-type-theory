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
  Axiom force : ∀ p, (∀ κ, t κ (p κ)) = (∀ κ, p κ).
  Axiom loeb : ∀ κ p, (t κ p → p) → p.
  Axiom next : ∀ κ (p : Prop), p → t κ p.

  Theorem join : ∀ κ p q, t κ p → t κ q → t κ (p ∧ q).
  Proof.
    move=> *.
    by [rewrite cart].
  Qed.

  Local Ltac elim_aux y :=
    lazymatch goal with
    | H1 : t ?κ _, H2 : t ?κ _ |- _ =>
      let x := fresh in
      have := join H1 H2 => x;
      clear H1; clear H2;
      elim_aux x
    | |- t ?κ _ => refine (map _ y)
  end.

  Ltac gather :=
    lazymatch goal with
    | x : t ?κ _ |- _ => elim_aux x
    | _ => let x := fresh in elim_aux x
    end.

  Axiom Total : Type → Prop.
  Definition Inh (A : Type) : Prop := ∃ x : A, True.

  Axiom yank_existential :
    ∀ A P κ,
      Total A
      → Inh A
      → t κ (∃ x : A, P x)
      → ∃ x : A, t κ (P x).

  Axiom pow_total : ∀ A, Total (A → Prop).
  Theorem pow_inh : ∀ A, Inh (A → Prop).
  Proof.
    move=> A.
    by exists (fun _ => True).
  Qed.

  Hint Resolve pow_total pow_inh.
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
