Require Import Unicode.Utf8.

From gctt Require Import Term.


(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := Tm.t 0 * Tm.t 0 → Prop.

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := Tm.t 0 * behavior → Prop.

Definition empty : matrix :=
  fun _ => False.

Record is_per (R : behavior) :=
  { symmetric : ∀ e0 e1, R (e0, e1) → R (e1, e0);
    transitive : ∀ e0 e1 e2, R (e0, e1) → R (e1, e2) → R (e0, e2)
  }.


Module Law.
  Definition universe_system (σ : matrix) :=
    ∀ X, σ X → ∃ i, fst X ⇓ Tm.univ i.

  Definition extensional_at (σ : matrix) X :=
    ∀ R', σ (fst X, R') → snd X = R'.

  Definition extensional (σ : matrix) :=
    ∀ A R, σ (A, R) → extensional_at σ (A, R).

  Definition per_valued (σ : matrix) :=
    ∀ A R, σ (A, R) → is_per R.
End Law.
