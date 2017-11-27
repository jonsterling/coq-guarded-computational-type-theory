Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
From mathcomp Require Import ssreflect.

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Term.


Set Bullet Behavior "Strict Subproofs".

From gctt Require Tactic.
Module T := Tactic.
Module M := Matrix.


Set Implicit Arguments.

Hint Resolve Later.map.

Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 ∧ e2 ⇓ e3) (at level 0).

  Definition unit (τ : M.matrix) X :=
    fst X ⇓ Tm.unit
    ∧ snd X = fun es => [fst es, snd es] ⇓ Tm.ax.

  Definition bool (τ : M.matrix) X :=
    fst X ⇓ Tm.bool
    ∧ snd X = fun es => ([fst es, snd es] ⇓ Tm.tt ∨ [fst es, snd es] ⇓ Tm.ff).

  Definition prod τ X :=
    ∃ B C R1 R2,
      fst X ⇓ Tm.prod B C
      ∧ τ (B, R1)
      ∧ τ (C, R2)
      ∧ snd X =
        fun es =>
          ∃ e11 e12 e21 e22,
            (fst es ⇓ Tm.pair e11 e12)
            ∧ (snd es ⇓ Tm.pair e21 e22)
            ∧ R1 (e11, e21)
            ∧ R2 (e12, e22).

  Definition later (τ : M.matrix) X :=
    ∃ κ B R',
      fst X ⇓ Tm.ltr κ B
      ∧ ▷[ κ ] (τ (B, R'))
      /\ snd X = fun e12 => ▷[ κ ] (R' e12).

  Definition isect (τ : M.matrix) X :=
    ∃ B S,
      fst X ⇓ Tm.isect B
      ∧ (∀ κ, τ (B κ, S κ))
      ∧ snd X = fun es => ∀ κ, S κ es.

  Ltac prove_monotone :=
    compute; move=> *; T.destruct_conjs;
    repeat T.split; eauto.

  Module Monotone.
    Local Obligation Tactic := prove_monotone.
    Program Instance unit : Proper (Poset.order ==> Poset.order) unit.
    Program Instance bool : Proper (Poset.order ==> Poset.order) bool.
    Program Instance prod : Proper (Poset.order ==> Poset.order) prod.
    Program Instance isect : Proper (Poset.order ==> Poset.order) isect.
    Program Instance later : Proper (Poset.order ==> Poset.order) later.
  End Monotone.

  Global Ltac simplify :=
    unfold unit, bool, prod, later, isect in *.
End Close.

Module Sig.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : M.matrix) (X : Tm.t 0 * M.behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
  | isect of Close.isect τ X
  | later of Close.later τ X.


  Program Instance monotonicity {σ : M.matrix} : Monotone (t σ).
  Next Obligation.
    move=> τ1 τ2 p [A R].
    case => *.
    + by [apply: init].
    + by [apply: unit].
    + by [apply: bool].
    + apply: prod.
      apply: Close.Monotone.prod; eauto; eauto.
    + apply: isect.
      apply: Close.Monotone.isect; eauto; eauto.
    + apply: later.
      apply: Close.Monotone.later; eauto; eauto.
  Qed.
End Sig.


Module Clo.
  Program Definition t (σ : M.matrix) := LFP.t (Sig.t σ).

  Theorem roll : ∀ σ, Sig.t σ (t σ) = t σ.
  Proof.
    move=> σ.
    apply: binrel_extensionality => [A R].
    T.split => [X | X]; [rewrite /t|];
    edestruct (LFP.roll (Sig.t σ));
    auto.
  Qed.

  Theorem ind :
    ∀ Y (σ ρ : M.matrix),
      t σ Y
      → (∀ X, σ X → ρ X)
      → (∀ X, Close.unit ρ X → ρ X)
      → (∀ X, Close.bool ρ X → ρ X)
      → (∀ X, Close.prod ρ X → ρ X)
      → (∀ X, Close.isect ρ X → ρ X)
      → (∀ X, Close.later ρ X → ρ X)
      → ρ Y.
  Proof.
    move=> [A R] σ ρ AcloR init unit bool prod isect later.
    rewrite /t /LFP.t in AcloR.
    simpl in AcloR.
    rewrite -/M.matrix in AcloR.

    destruct AcloR.
    destruct H.
    apply: H.
    + move=> [A' R']; elim; auto.
    + auto.
  Qed.

  Local Hint Constructors Sig.t.

  Ltac elim_clo :=
    let x := fresh in
    move=> x;
    apply: (ind x).

  Instance monotonicity : Monotone t.
  Proof.
    split; move=> ? ? ? ?.
    elim_clo => *; rewrite -roll; eauto.
  Qed.

  Ltac use_universe_system :=
    match goal with
    | H : M.Law.universe_system ?σ, H' : ?σ ?X |- _ =>
      destruct (H X H')
    end.


  Local Ltac rewrite_functionality_ih :=
    repeat match goal with
    | ih : M.Law.extensional_at _ _ |- _ =>
      rewrite /M.Law.extensional_at in ih;
      simpl in ih;
      erewrite ih
    end.

  Local Ltac functionality_case :=
    match goal with
    | ih : M.Law.extensional _ |- _ =>
      move=> [? ?] //= ? ?;
      rewrite /M.Law.extensional_at; rewrite -roll; case => //= ?;
      Close.simplify;
      try use_universe_system; try by [apply: ih; eauto];
      T.destruct_conjs; T.evals_to_eq; T.destruct_eqs;
      simpl in *
    end.

  Local Ltac moves :=
    move=> *.


  Theorem extensionality
    : ∀ σ,
      M.Law.universe_system σ
      → M.Law.extensional σ
      → M.Law.extensional (t σ).
  Proof.
    move=> ? ? ? ? ?; elim_clo; functionality_case.
    + congruence.
    + congruence.
    + do 2 T.reorient.
      rewrite_functionality_ih; eauto.
    + do 2 T.reorient.
      do ?(T.eqcd; moves).
      T.specialize_hyps.
      rewrite_functionality_ih;
      eauto.
    + do 2 T.reorient.
      do ?(T.eqcd; moves).
      Later.gather => *.
      T.destruct_conjs.
      rewrite_functionality_ih;
      eauto.
  Qed.

  Hint Resolve monotonicity extensionality.
End Clo.
