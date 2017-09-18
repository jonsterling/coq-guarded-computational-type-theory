Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

Require Import OrderTheory.
Require Import Axioms.
Require Import Terms.

Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.


Set Implicit Arguments.


Hint Resolve Later.map.

(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := ℘ (Tm.t 0 * Tm.t 0).

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := ℘ (Tm.t 0 * behavior).


Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Ltac morphism_monotone :=
  match goal with
  | |- @mon_func _ _ _ _ ?m _ _ =>
    apply: (@mon_prop _ _ _ _ m);
    eauto
  end.

Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 ∧ e2 ⇓ e3) (at level 0).

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ ∀ e1 e2,
            R (e1, e2) ↔ [e1, e2] ⇓ Tm.ax).
    + firstorder.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ ∀ e1 e2,
           R (e1, e2) ↔ ([e1, e2] ⇓ Tm.tt ∨ [e1, e2] ⇓ Tm.ff)).
    + firstorder.
  Defined.

  Definition later : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ κ B,
            A ⇓ Tm.ltr κ B
            ∧ ▷[ κ ] (τ (B, R))).
    + move=> τ1 τ2 τ1τ2 [A R] [κ [B [A_eval Q]]].
      econstructor; eauto.
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
            ∧ ∀ e1 e2,
                R (e1, e2) ↔ ∃ e11 e12 e21 e22,
                  (e1 ⇓ Tm.pair e11 e12)
                  ∧ (e2 ⇓ Tm.pair e21 e22)
                  ∧ R1 (e11, e21)
                  ∧ R2 (e12, e22)).
    + move=> τ1 τ2 P [A R].
      firstorder.
      do 4 eexists.
      split; eauto.
  Defined.
End Close.

Module TyF.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : matrix) (X : Tm.t 0 * behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
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
      | apply: later
      ]; morphism_monotone.
  Defined.
End TyF.

(* Because the map is monotone, we can take its least fixed point to
   get a closure operator on refinement matrices.*)
Definition CTyF (σ : matrix) := lfp (TyF.mono σ).

Theorem CTyFUnroll (σ : matrix) : CTyF σ == TyF.mono σ (CTyF σ).
  rewrite /CTyF.
  symmetry.
  refine (lfp_fixed_point matrix _ (TyF.mono σ)).
Qed.


Module Univ.
  Print nat.

  Definition Empty : matrix :=
    fun _ => False.

  Definition Spine (i : nat) : matrix.
  Proof.
    elim: i => [|i'].
    + exact (CTyF Empty).
    + move=> τ [A R].
      exact
        (exists j,
            j <= i'
            ∧ A ⇓ Tm.univ j
            /\ forall e1 e2,
                R (e1, e2) ↔
                  exists S, CTyF τ (e1, S) ∧ CTyF τ (e2, S)).
  Defined.

  Definition Nuprl (i : nat) : matrix :=
    CTyF (Spine i).

  Definition Nuprlω : matrix :=
    fun X => ∃ n, Nuprl n X.

  Ltac roll_matrix :=
    rewrite /Nuprl /CTyF;
    match goal with
    | |- lfp ?m ?x =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
    end.

  Ltac prove_is_type :=
    match goal with
    | |- exists R, Nuprl ?i (?A, R) =>
      have: exists R, TyF.t (Spine i) (Nuprl i) (A, R);
      last (move=> [R T]; exists R; roll_matrix)
    end.

  Theorem test : ∃ R, Nuprl 1 (Tm.prod Tm.unit (Tm.univ 0), R).
  Proof.
    prove_is_type.
    + econstructor.
      apply: TyF.prod.
      simpl.
      do 4 eexists.
      repeat split.
      ++ eauto.
      ++ have: exists R, Nuprl 1 (Tm.unit, R).
         +++ prove_is_type.
             ++++ econstructor.
                  apply: TyF.unit.
                  simpl.
apply: eval_prod.

    + auto.
  Admitted.



End Univ.