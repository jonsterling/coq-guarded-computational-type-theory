Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
From mathcomp Require Import ssreflect.

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.


Set Bullet Behavior "Strict Subproofs".

From gctt Require Tactic.
Module T := Tactic.
Module M := Matrix.


Set Implicit Arguments.

Local Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Local Ltac morphism_monotone :=
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

  Definition unit : monotone M.matrix M.matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ R = fun e12 => [fst e12, snd e12] ⇓ Tm.ax).
    + prove_monotone.
  Defined.

  Definition bool : monotone M.matrix M.matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ R = fun e12 => ([fst e12, snd e12] ⇓ Tm.tt ∨ [fst e12, snd e12] ⇓ Tm.ff)).
    + prove_monotone.
  Defined.

  Definition later : monotone M.matrix M.matrix.
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

  Definition prod : monotone M.matrix M.matrix.
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

  Definition isect : monotone M.matrix M.matrix.
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
  Inductive t (σ τ : M.matrix) (X : Tm.t 0 * M.behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
  | isect of Close.isect τ X
  | later of Close.later τ X.

  (* The map defined above really is monotone. *)
  Definition mono (σ : M.matrix) : monotone M.matrix M.matrix.
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
  Definition t (σ : M.matrix) := lfp (Sig.mono σ).


  Theorem roll : ∀ σ, Sig.t σ (t σ) = t σ.
  Proof.
    move=> σ.
    apply: binrel_extensionality => [A R].
    T.split => [X | X].
    + rewrite /t.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x)
      end.
      auto.
    + rewrite /t in X.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x) => _ Q'
      end.
      apply: Q'.
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
    rewrite /t /lfp in AcloR.
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
    apply: (ind _ x).

  Theorem monotonicity : ∀ σ1 σ2, (σ1 ⊑ σ2) → t σ1 ⊑ t σ2.
  Proof.
    move=> ? ? ? ?.
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
      try use_universe_system; try by [apply: ih; eauto];
      T.destruct_conjs; T.evals_to_eq; T.destruct_eqs
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
    + rewrite_functionality_ih;
      eauto.
    + do ?(T.eqcd; moves).
      T.specialize_hyps.
      rewrite_functionality_ih;
      eauto.
    + do ?(T.eqcd; moves).
      Later.gather => *.
      T.destruct_conjs.
      rewrite_functionality_ih;
      eauto.
  Qed.

  Hint Resolve monotonicity extensionality.
End Clo.
