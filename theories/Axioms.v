Require Import Unicode.Utf8 Program.Tactics Logic.FunctionalExtensionality.
From gctt Require Import Notation.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Axiom 𝕂 : Type.
Axiom LocalClock : ∃ κ : 𝕂, ⊤.

Module Later.
  Axiom t : 𝕂 → Ω → Ω.
  Axiom map : forall κ (p q : Ω), (p → q) → (t κ p → t κ q).
  Axiom cart : ∀ κ (p q : Ω), t κ (p ∧ q) = ((t κ p) ∧ (t κ q)).
  Axiom force : ∀ p, (∀ κ, t κ (p κ)) = (∀ κ, p κ).
  Axiom loeb : ∀ κ p, (t κ p → p) → p.
  Axiom next : ∀ κ (p : Ω), p → t κ p.
  Axiom commute_eq : ∀ κ (p q : Ω), ((t κ p) = (t κ q)) = t κ (p = q).

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

  Axiom Total : Type → Ω.
  Definition Inh (A : Type) : Ω := ∃ x : A, ⊤.

  Axiom yank_existential :
    ∀ A P κ,
      Total A
      → Inh A
      → t κ (∃ x : A, P x)
      → ∃ x : A, t κ (P x).

  Axiom push_existential :
    ∀ A P κ,
      (∃ x : A, t κ (P x))
      → t κ (∃ x : A, P x).

  Axiom push_universal :
    ∀ A P κ,
      (∀ x : A, t κ (P x))
      → t κ (∀ x : A, P x).

  Axiom pow_total : ∀ A, Total (A → Ω).
  Axiom nat_total : Total nat.

  Theorem pow_inh : ∀ A, Inh (A → Ω).
  Proof.
    move=> A.
    by exists (fun _ => ⊤).
  Qed.

  Theorem nat_inh : Inh nat.
  Proof.
    by exists 0.
  Qed.

  Hint Resolve pow_total pow_inh nat_total nat_inh.
End Later.

Notation "▷[ κ ] ϕ" := (Later.t κ ϕ) (at level 50) : type_scope.

Module LaterT.
  Axiom t : 𝕂 → Type → Type.
  Axiom next : ∀ κ (X : Type), X → t κ X.
  Axiom map : ∀ κ (X Y : Type), (X → Y) → (t κ X → t κ Y).
  Axiom map_spec : ∀ κ (X Y : Type) (f : X → Y) x, map f (next κ x) = next κ (f x).

  Axiom loeb : ∀ κ X, (t κ X → X) → X.
  Axiom loeb_spec : ∀ κ X (F : t κ X → X), loeb F = F (next κ (loeb F)).

  (* succ witnesses the contractivity of ▷[κ] on Ω *)
  Axiom succ : ∀ κ, t κ Ω → Ω.
  Axiom succ_spec : ∀ κ ϕ, ▷[κ] ϕ = succ (next κ ϕ).
End LaterT.


Notation "▶[ κ ] X" := (LaterT.t κ X) (at level 50) : type_scope.

(* True in any topos. *)
Axiom constructive_definite_description :
  forall (A : Type) (P : A → Ω),
    (exists! x, P x)
    →{ x : A | P x }.

Theorem dependent_unique_choice {A B} {R : ∀ x : A, B x → Ω}:
  (forall x:A, exists! y : B x, R x y)
  → (∃ f, ∀ x:A, R x (f x)).
Proof.
  move=> ?.
  eexists => ?.
  apply: proj2_sig.
  by apply: constructive_definite_description.
Qed.


Theorem unique_choice {A B} {R : A → B → Ω}:
  (∀ x:A, exists! y : B, R x y)
  → (∃ f : A → B, ∀ x:A, R x (f x)).
Proof.
  apply: dependent_unique_choice.
Qed.

Axiom propositional_extensionality :
  ∀ (P Q : Ω),
    (P ↔ Q)
    → P = Q.

Theorem binrel_extensionality {T1 T2} {R1 R2 : T1 × T2 → Ω} :
  (∀ x y, R1 (x, y) ↔ R2 (x, y))
  → R1 = R2.
Proof.
  move=> ?.
  apply: functional_extensionality.
  move=> [? ?].
  by apply: propositional_extensionality.
Qed.
