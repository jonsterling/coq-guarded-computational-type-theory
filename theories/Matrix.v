Require Import Unicode.Utf8.

From gctt Require Import Terms.


(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := Tm.t 0 * Tm.t 0 → Prop.

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := Tm.t 0 * behavior → Prop.

Definition based_matrix_functional (σ : matrix) (A : Tm.t 0) : Prop :=
  ∀ R1 R2,
    σ (A, R1)
    → σ (A, R2)
    → R1 = R2.

Definition matrix_functional (σ : matrix) : Prop :=
  ∀ A, based_matrix_functional σ A.
