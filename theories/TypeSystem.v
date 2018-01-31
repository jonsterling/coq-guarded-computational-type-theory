Require Import Unicode.Utf8 ssreflect Program.Equality.
Set Bullet Behavior "Strict Subproofs".

From ctt Require Import Notation Program OpSem Axioms.

(* candidate relation *)
Definition rel := Prog.t 0 × Prog.t 0 → Ω.

(* candidate type system *)
Definition cts := Prog.t 0 × rel → Ω.

Definition empty : cts :=
  fun _ => ⊥.

Record is_per (R : rel) :=
  { symmetric :
      ∀ M0 M1,
        R (M0, M1)
        → R (M1, M0);

    transitive :
      ∀ M0 M1 M2,
        R (M0, M1)
        → R (M1, M2)
        → R (M0, M2)
  }.


Definition rel_computational (R : rel) :=
  ∀ M0 M1 M2,
    M0 ≼₀ M1
    → R (M0, M2)
    → R (M1, M2).

Record is_cper (R : rel) :=
  { per : is_per R;
    crel : rel_computational R
  }.

Module TS.
  Section Law.
    Variable σ : cts.

    Class universe_system :=
      { is_universe_system :
          ∀ X,
            σ X
            → ∃ i, π₁ X ⇓ Prog.univ i }.

    Definition extensional_at X :=
      ∀ R',
        σ (π₁ X, R')
        → π₂ X = R'.

    Class extensional :=
      { is_extensional :
          ∀ A R,
            σ (A, R)
            → extensional_at (A, R) }.

    Class cper_valued :=
      { is_cper_valued :
          ∀ A R,
            σ (A, R)
            → is_cper R }.

    Definition type_computational_at (X : Prog.t 0 × rel) :=
      ∀ A,
        π₁ X ≼₀ A
        → σ (A, π₂ X).

    Class type_computational :=
      { is_type_computational :
          ∀ A R,
            σ (A, R)
            → type_computational_at (A, R) }.
  End Law.

  Inductive Pick (τ : cts) A Ms : Prop :=
  | pick : (∀ R, τ (A, R) → R Ms) → Pick τ A Ms.

  Module PickNotation.
    Notation "τ @ A" := (Pick τ A) (at level 10).
  End PickNotation.

  Import PickNotation.

  Lemma Pick_lemma {τ} `{TS.extensional τ} {A} {R} :
    τ (A, R)
    → τ @ A = R.
  Proof.
    move=> AR.
    apply: binrel_extensionality => x y; split.
    - move=> []; by apply.
    - move=> xy; constructor=> R' AR'.
      replace R' with R; auto.
      apply: TS.is_extensional; eauto.
  Qed.

  Hint Resolve Pick_lemma.
End TS.

Export TS.PickNotation.