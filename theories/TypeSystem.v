Require Import Unicode.Utf8.

From gctt Require Import Term Axioms.

(* candidate relation *)
Definition rel := Tm.t 0 * Tm.t 0 → Ω.

(* candidate type system *)
Definition cts := Tm.t 0 * rel → Ω.

Definition empty : cts :=
  fun _ => False.

Record is_per (R : rel) :=
  { symmetric : ∀ e0 e1, R (e0, e1) → R (e1, e0);
    transitive : ∀ e0 e1 e2, R (e0, e1) → R (e1, e2) → R (e0, e2)
  }.

Module TS.
  Section Law.
    Variable σ : cts.

    Definition universe_system :=
      ∀ X, σ X → ∃ i, fst X ⇓ Tm.univ i.

    Definition extensional_at X :=
      ∀ R', σ (fst X, R') → snd X = R'.

    Definition extensional :=
      ∀ A R, σ (A, R) → extensional_at (A, R).

    Definition per_valued :=
      ∀ A R, σ (A, R) → is_per R.
  End Law.
End TS.