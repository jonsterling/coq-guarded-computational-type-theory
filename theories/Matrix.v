Require Import Unicode.Utf8.

From gctt Require Import Terms.


(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := Tm.t 0 * Tm.t 0 → Prop.

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := Tm.t 0 * behavior → Prop.

Definition empty : matrix :=
  fun _ => False.


Module Law.
  Definition universe_system (σ : matrix) :=
    ∀ X, σ X → ∃ i, fst X ⇓ Tm.univ i.

  Definition extensional_at (σ : matrix) X :=
    ∀ R', σ (fst X, R') → snd X = R'.

  Definition extensional (σ : matrix) :=
    ∀ A R, σ (A, R) → extensional_at σ (A, R).
End Law.