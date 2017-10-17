Require Import Unicode.Utf8.

From gctt Require Import Terms.


(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := Tm.t 0 * Tm.t 0 → Prop.

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := Tm.t 0 * behavior → Prop.

Definition functional (σ : matrix) : Prop :=
  ∀ A R1 R2,
    σ (A, R1)
    → σ (A, R2)
    → R1 = R2.

Definition empty : matrix :=
  fun _ => False.
