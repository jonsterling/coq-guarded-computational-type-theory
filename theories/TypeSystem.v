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


Definition rel_computational (R : rel) :=
  ∀ e0 e1 e2, e0 ≼0 e1 → R (e0, e2) → R (e0, e1).

Record is_cper (R : rel) :=
  { per : is_per R;
    crel : rel_computational R
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

    Definition cper_valued :=
      ∀ A R, σ (A, R) → is_cper R.

    Definition type_computational_at (X : Tm.t 0 * rel) :=
      ∀ A, fst X ≼0 A → σ (A, snd X).

    Definition type_computational :=
      ∀ A R, σ (A, R) → type_computational_at (A, R).
  End Law.
End TS.