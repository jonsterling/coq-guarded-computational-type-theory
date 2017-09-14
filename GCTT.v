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


Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Ltac morphism_monotone f :=
  apply: (@mon_prop _ _ _ _ f).



Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 /\ e2 ⇓ e3) (at level 0).

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         /\ forall e1 e2,
            R (e1, e2) <-> [e1, e2] ⇓ Tm.ax).
    + firstorder.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        /\ forall e1 e2,
           R (e1, e2) <-> ([e1, e2] ⇓ Tm.tt \/ [e1, e2] ⇓ Tm.ff)).
    + firstorder.
  Defined.

  Definition later : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (exists κ B,
            A ⇓ Tm.ltr κ B
            /\ ▷[ κ ] (τ (B, R))).
    + move=> τ1 τ2 τ1τ2 [A R] [κ [B [A_eval Q]]].
      econstructor; eauto.
  Defined.

  Definition prod : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (exists B C R1 R2,
            A ⇓ Tm.prod B C
            /\ τ (B, R1)
            /\ τ (C, R2)
            /\ forall e1 e2,
                R (e1, e2) <-> exists e11 e12 e21 e22,
                  (e1 ⇓ Tm.pair e11 e12)
                  /\ (e2 ⇓ Tm.pair e21 e22)
                  /\ R1 (e11, e21)
                  /\ R2 (e12, e22)).
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
    + move=> τ1 τ2 P X [Q|Q|Q|Q|Q].
      ++ by [apply: init].
      ++ apply: unit.
         morphism_monotone Close.unit; eauto.
      ++ by [apply: bool].
      ++ apply: prod.
         morphism_monotone Close.prod; eauto.
      ++ apply: later.
         morphism_monotone Close.later; eauto.
  Defined.
End TyF.

(* Because the map is monotone, we can take its least fixed point to
   get a closure operator on refinement matrices.*)
Definition CTyF (σ : matrix) := lfp (TyF.mono σ).