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

Module Connective.
  Inductive ctor := unit | bool | prod | later | isect.

  Inductive unit_val : M.behavior :=
  | ax : unit_val (Tm.ax, Tm.ax).

  Inductive bool_val : M.behavior :=
  | tt : bool_val (Tm.tt, Tm.tt)
  | ff : bool_val (Tm.ff, Tm.ff).

  Inductive prod_val (R0 R1 : M.behavior) : M.behavior :=
  | pair :
      ∀ e00 e01 e10 e11,
        R0 (e00, e10)
        → R1 (e01, e11)
        → prod_val R0 R1 (Tm.pair e00 e01, Tm.pair e10 e11).

  Inductive cext (R : M.behavior) : M.behavior :=
  | mk_cext :
      ∀ e0 e1 v0 v1,
        e0 ⇓ v0
        → e1 ⇓ v1
        → R (v0, v1)
        → cext R (e0, e1).

  Inductive has (τ : M.matrix) : ctor → Tm.t 0 * M.behavior → Prop :=
  | has_unit : has τ unit (Tm.unit, cext unit_val)
  | has_bool : has τ bool (Tm.bool, cext bool_val)
  | has_prod :
      ∀ A0 A1 R0 R1,
        τ (A0, R0)
        → τ (A1, R1)
        → has τ prod (Tm.prod A0 A1, cext (prod_val R0 R1))
  | has_later :
      ∀ κ B R,
        ▷[κ] (τ (B, R))
        → has τ later (Tm.ltr κ B, fun e0e1 => ▷[κ] (R e0e1))
  | has_isect :
      ∀ B S,
        (∀ κ, τ (B κ, S κ))
        → has τ isect (Tm.isect B, fun e0e1 => ∀ κ, S κ e0e1).

  Hint Constructors has cext prod_val bool_val unit_val.

  Theorem monotone : ∀ ι, Proper (Poset.order ==> Poset.order) (fun τ => has τ ι).
  Proof.
    move=> ι τ0 τ1 τ01 [A R] H.
    dependent destruction H;
    eauto.
  Qed.

  Hint Resolve monotone.
End Connective.

Module Sig.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : M.matrix) : (Tm.t 0 * M.behavior) → Prop :=
  | init :
      ∀ X,
        σ X
        → t σ τ X

  | conn :
      ∀ ι A A0 R,
        A ⇓ A0
        → Connective.has τ ι (A0, R)
        → t σ τ (A, R).

  Instance monotonicity {σ : M.matrix} : Monotone (t σ).
  Proof.
    constructor => τ1 τ2 p [A R].
    case => *.
    + by econstructor.
    + econstructor; try by [eauto];
      apply: Connective.monotone;
      eauto.
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
      → (∀ ι A A0 R, A ⇓ A0 → Connective.has ρ ι (A0, R) → ρ (A, R))
      → ρ Y.
  Proof.
    move=> [A R] σ ρ AcloR init conn.
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

  Local Ltac moves :=
    move=> *.

  Ltac destruct_sig :=
    match goal with
    | H : Sig.t _ _ _ |- _ => dependent destruction H
    end.

  Ltac ind_sig :=
    match goal with
    | H : Sig.t _ _ _ |- _ => dependent induction H
    end.

  Ltac destruct_has :=
    match goal with
    | H : Connective.has _ _ _ |- _ => dependent destruction H
    end.

  Ltac destruct_clo :=
    match goal with
    | H : t _ _ |- _ => rewrite -roll in H; dependent destruction H
    end.


  Theorem connective_not_universe {τ i ι A' A R} {P : Prop} :
    Connective.has τ ι (A', R)
    → A ⇓ A'
    → A ⇓ Tm.univ i
    → P.
  Proof.
    move=> has eval1 eval2.
    dependent destruction has;
    by Term.evals_to_eq.
  Qed.


  Local Ltac cleanup :=
    simpl in *;
    try use_universe_system;
    Term.evals_to_eq;
    T.destruct_eqs;
    auto.

  Theorem extensionality {σ} :
    M.Law.universe_system σ
    → M.Law.extensional σ
    → M.Law.extensional (t σ).
  Proof.
    move=> ? ext ? ?; elim_clo; clear H.
    - move=> [? ?] ? ? ?.
      destruct_clo.
      + by apply: ext.
      + use_universe_system.
        destruct_has; by Term.evals_to_eq.

    - move=> ? ? ? ? ? ?.
      destruct_has => ? ?;
      destruct_clo; try by [cleanup];
      destruct_has; cleanup.
      + rewrite_functionality_ih; eauto.
      + do ? (T.eqcd; moves).
        Later.gather => *; T.destruct_conjs.
        rewrite_functionality_ih; eauto.
      + do ? (T.eqcd; moves).
        T.specialize_hyps.
        rewrite_functionality_ih; eauto.
  Qed.

  Hint Resolve monotonicity extensionality.
End Clo.
