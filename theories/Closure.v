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


  Ltac noconfusion :=
    try by [contradiction];
    rewrite /M.empty;
    move=> *; simpl in *;
    T.destruct_conjs.

  Ltac specialize_functionality_ih :=
    repeat
      match goal with
      | H : ∀ R1 R2 : M.behavior, t _ (?X, _) → t _ (?X, _) → _ = _, H' : t _ (?X, ?R1), H'' : t _ (?X, ?R2) |- _ => specialize (H _ _ H' H''); move: H
  end.


  Theorem monotonicity : ∀ σ1 σ2, (σ1 ⊑ σ2) → t σ1 ⊑ t σ2.
  Proof.
    move=> σ1 σ2 p [A R] AtR.
    destruct AtR as [τ ih]; simpl in *.
    destruct ih as [ih1 ih2].
    apply ih1; auto.
    move=> [A' R'] s.
    rewrite -roll.
    elim s => A'R'.
    + apply: Sig.init; auto.
    + apply: Sig.unit; auto.
    + apply: Sig.bool; auto.
    + apply: Sig.prod; auto.
    + apply: Sig.isect; auto.
    + apply: Sig.later; auto.
  Qed.

  Definition universe_system (σ : M.matrix) :=
    ∀ A R, σ (A, R) → ∃ i, A ⇓ Tm.univ i.


  Theorem unit_functionality : ∀ σ, M.functional (Close.unit σ).
  Proof.
    move=> σ.
    move=> A R1 R2 //= *.
    T.destruct_conjs.
    congruence.
  Qed.

  Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.


  Theorem prod_functionality : ∀ σ, M.functional σ → M.functional (Close.prod σ).
    move=> σ σfn A R1 R2 [B [C [R11 [R12 [evA [BR11 [CR12 spR1]]]]]]] [B' [C' [R11' [R12' [evA' [BR11' [CR12' spR1']]]]]]].
    have: B = B' ∧ C = C'.
    + have: Tm.prod B C = Tm.prod B' C'.
      ++ apply: determinacy; eauto.
      ++ case; eauto.

    + move=> [p q].
      rewrite -p in BR11'.
      rewrite -q in CR12'.
      have : R11 = R11' /\ R12 = R12'.
      ++ split; apply: σfn; eauto.
      ++ move=> [p' q'].
         rewrite -p' in spR1'.
         rewrite q' in spR1.
         congruence.
  Qed.

  Definition uniquely_valued_body (σ : M.matrix) X :=
    ∀ R', σ (fst X, R') → snd X = R'.

  Definition uniquely_valued (σ : M.matrix) :=
    ∀ A R, σ (A, R) → uniquely_valued_body σ (A, R).


  Ltac use_universe_system :=
    match goal with
    | H : universe_system ?σ, H' : ?σ (?A, ?R) |- _ =>
      destruct (H A R H')
    end.

  Ltac discrim_eval :=
    match goal with
    | H1 : ?A ⇓ ?V1, H2 : ?A ⇓ ?V2 |- _ => have: V1 = V2; [apply: determinacy; eauto | discriminate]
    end.



  Theorem functionality
    : ∀ σ,
      universe_system σ
      → uniquely_valued σ
      → uniquely_valued (t σ).
  Proof.
    move=> σ σuni σfn.
    move=> A R1 AtσR1.
    apply: (ind (fun X => uniquely_valued_body (t σ) X) AtσR1).
    + move => [A' R'] A'σR' R'' //= A'tσR''.
      use_universe_system.
      rewrite -roll in A'tσR''.
      case: A'tσR'' => //= H'; first by [apply: σfn; eauto];
      T.destruct_conjs;
      discrim_eval.


    + move=> [A' R'] //= X R'' //= A'tσR''.
      T.destruct_conjs.
      rewrite -roll in A'tσR''.
      case: A'tσR'' => //= H'; T.destruct_conjs; try use_universe_system; try discrim_eval.
      congruence.

    + move=> [A' R'] //= X R'' //= A'tσR''.
      T.destruct_conjs.
      rewrite -roll in A'tσR''.
      case: A'tσR'' => //= H'; T.destruct_conjs; try use_universe_system; try discrim_eval.
      congruence.

    + move=> [A' R']  [B [C [RB [RC [evA' [ihB [ihC spR']]]]]]].
      move=> R'' //= A'tσR''.
      rewrite -roll in A'tσR''.
      case: A'tσR'' => //= X; try by [try use_universe_system; T.destruct_conjs; try discrim_eval].
      case: X =>  [B' [C' [RB' [RC' [evA'' [ihB' [ihC' spR'']]]]]]].
         have : B = B' ∧ C = C' ∧ RB = RB' ∧ RC = RC'.
         +++ have: Tm.prod B C = Tm.prod B' C'.
             ++++ apply: determinacy; eauto.
             ++++ case => p1 p2.
                  split; auto.
                  split; auto.
                  split.
                  +++++ apply: ihB; rewrite p1. auto.
                  +++++ apply: ihC; rewrite p2; auto.
         +++ move=> [p1 [p2 [p3 [p4]]]].
             T.destruct_conjs.
             T.reorient.
             rewrite -p3.
             rewrite -p4.
             T.reorient.
             auto.




  Theorem functionality : M.functional (t M.empty).
  Admitted.

  Theorem idempotence : t (t M.empty) = t M.empty.
  Proof.
  Admitted.
End Clo.
