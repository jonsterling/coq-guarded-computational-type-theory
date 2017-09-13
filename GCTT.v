Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

Require Import OrderTheory.
Require Import Axioms.
Require Import Terms.

Set Implicit Arguments.


Hint Resolve Later.map.

(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := ℘ (Tm.t 0 * Tm.t 0).

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := ℘ (Tm.t 0 * behavior).

Definition eq_mem (τ : matrix) (e1 e2 A : Tm.t 0) :=
  exists R,
    τ (A, R)
    /\ R (e1, e2).

Notation "τ ⊧ e1 ≐ e2 ∈ A" := (eq_mem τ e1 e2 A) (at level 1).

Theorem eq_mem_map : forall (τ1 τ2 : matrix) e1 e2 A, (∀ X, τ1 X -> τ2 X) -> τ1 ⊧ e1 ≐ e2 ∈ A -> τ2 ⊧ e1 ≐ e2 ∈ A.
Proof.
  move=> τ1 τ2 e1 e2 A F e1e2.
  elim: e1e2 => R [Aτ1R e1Re2].
  exists R.
  split.
  + by [apply: F].
  + by [].
Qed.

Hint Resolve eq_mem_map.

Module Close.
  Print Tm.t.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 /\ e2 ⇓ e3) (at level 0).

  Definition unit A R :=
    A ⇓ Tm.unit
    /\ forall e1 e2,
      R (e1, e2) <-> [e1, e2] ⇓ Tm.ax.

  Definition bool A R :=
    A ⇓ Tm.bool
    /\ forall e1 e2,
      R (e1, e2) <-> ([e1, e2] ⇓ Tm.tt \/ [e1, e2] ⇓ Tm.ff).

  Definition later (τ : matrix) A R :=
    exists κ B,
      A ⇓ Tm.ltr κ B
      /\ ▷[ κ ] (τ (B, R)).

  (* Note: it may seem like a simpler definition that uses τ ⊧ e ≐ e' ∈ A is possible,
       but that is only a correct definition for a *functional* refinement matrix afaict.
       Because we don't want to assume that just yet, we need this definition. *)
  Definition prod (τ : matrix) A R :=
    exists B C R1 R2,
      A ⇓ Tm.prod B C
      /\ τ (B, R1)
      /\ τ (C, R2)
      /\ forall e1 e2,
          R (e1, e2) <-> exists e11 e12 e21 e22,
            (e1 ⇓ Tm.pair e11 e12)
            /\ (e2 ⇓ Tm.pair e21 e22)
            /\ R1 (e11, e21)
            /\ R2 (e12, e22).
End Close.

Module TyF.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : matrix) (A : Tm.t 0) (R : behavior) : Prop :=
  | init of σ (A, R)
  | unit of Close.unit A R
  | bool of Close.bool A R
  | prod of Close.prod τ A R
  | later of Close.later τ A R.

  Definition fn σ τ X :=
    t σ τ (fst X) (snd X).


  (* The map defined above really is monotone. *)
  Definition mono (σ : matrix) : monotone matrix matrix.
  Proof.
    refine {| mon_func := fn σ |}.
    move=> τ1 τ2 P [A R] [Q|Q|Q|Q|Q].
    + by [apply: init].
    + by [apply: unit].
    + by [apply: bool].
    + apply: prod; firstorder; do 4 eexists; split; eauto.
    + apply: later; firstorder; econstructor; eauto.
  Defined.
End TyF.

(* Because the map is monotone, we can take its least fixed point to
   get a closure operator on refinement matrices.*)
Definition CTyF (σ : matrix) := lfp (TyF.mono σ).