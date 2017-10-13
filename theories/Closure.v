Require Import Unicode.Utf8.
From mathcomp Require Import ssreflect.

From gctt Require Import OrderTheory.
From gctt Require Import Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.

From gctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.

Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Ltac morphism_monotone :=
  match goal with
  | |- @mon_func _ _ _ _ ?m _ _ =>
    apply: (@mon_prop _ _ _ _ m);
    eauto
  end.

Hint Resolve Later.map.

Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 ∧ e2 ⇓ e3) (at level 0).

  Ltac prove_monotone :=
    simpl; move=> *; T.destruct_conjs;
    repeat T.split; eauto.

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ R = fun e12 => [fst e12, snd e12] ⇓ Tm.ax).
    + prove_monotone.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ R = fun e12 => ([fst e12, snd e12] ⇓ Tm.tt ∨ [fst e12, snd e12] ⇓ Tm.ff)).
    + prove_monotone.
  Defined.

  Definition later : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ κ B R',
            A ⇓ Tm.ltr κ B
            ∧ ▷[ κ ] (τ (B, R'))
            /\ R = fun e12 => ▷[ κ ] (R' e12)).
    + prove_monotone.
  Defined.

  Definition prod : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B C R1 R2,
            A ⇓ Tm.prod B C
            ∧ τ (B, R1)
            ∧ τ (C, R2)
            ∧ R = fun es =>
                    ∃ e11 e12 e21 e22,
                      (fst es ⇓ Tm.pair e11 e12)
                      ∧ (snd es ⇓ Tm.pair e21 e22)
                      ∧ R1 (e11, e21)
                      ∧ R2 (e12, e22)).
    + prove_monotone.
  Defined.

  Definition isect : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B S,
            A ⇓ Tm.isect B
            ∧ (∀ κ, τ (B κ, S κ))
            ∧ R = fun es => ∀ κ, S κ es).
    + prove_monotone.
  Defined.
End Close.

Module Sig.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : matrix) (X : Tm.t 0 * behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
  | isect of Close.isect τ X
  | later of Close.later τ X.

  (* The map defined above really is monotone. *)
  Definition mono (σ : matrix) : monotone matrix matrix.
  Proof.
    make_morphism.
    + exact (t σ).
    + move=> τ1 τ2 P X tQ; case tQ => Q;
      [ apply: init; eauto
      | apply: unit
      | apply: bool
      | apply: prod
      | apply: isect
      | apply: later
      ]; morphism_monotone.
  Defined.
End Sig.


Module Clo.
  Definition t (σ : matrix) := lfp (Sig.mono σ).


  Theorem roll : ∀ σ, Sig.t σ (t σ) = t σ.
  Proof.
    move=> σ.
    apply: binrel_extensionality => [A R].
    T.split => [X | X].
    + rewrite /t.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
      end.
      auto.
    + rewrite /t in X.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ Q'
      end.
      apply: Q'.
      auto.
  Qed.


  Theorem ind :
    ∀ (σ : matrix) (X : Tm.t 0 * behavior) (P : Prop),
      t σ X
      → (σ X → P)
      → (Close.unit (t σ) X → P)
      → (Close.bool (t σ) X → P)
      → (Close.prod (t σ) X → P)
      → (Close.isect (t σ) X → P)
      → (Close.later (t σ) X → P)
      → P.
  Proof.
    move=> σ [A R] P C init unit bool prod isect later.
    rewrite -roll in C.
    case: C; auto.
  Qed.
End Clo.