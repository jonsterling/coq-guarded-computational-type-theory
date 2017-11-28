Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Term.
From gctt Require Import Closure.
From gctt Require Import Tower.
From gctt Require Import Sequent.

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.omega.Omega.


Set Implicit Arguments.

Module Closed.
  Local Ltac simplify :=
    Close.simplify; Spine.simplify; simpl;
    repeat
      (lazymatch goal with
       | |- ?i ≤ ?j => omega
       | |- ?P ∧ ?Q => split
       | |- ∃ (x : ?A), ?P => eexists
       | |- ?P ↔ ?Q => split
       end); eauto.

  (* A tactic to prove a rule by appealing to one of
     the constructors of the refinement matrix closure operator. *)
  Local Ltac prove_rule con :=
    T.destruct_conjs;
    lazymatch goal with
    | |- τ[ ?n ] ⊧ ?A ∼ ?A =>
      eexists; rewrite /Tower.t -Clo.roll; split;
      apply: con; simplify; try reflexivity
    end.


    Theorem unit_formation {n : nat} :
      τ[n] ⊧ Tm.unit ∼ Tm.unit.
    Proof.
      prove_rule Sig.unit.
    Qed.

    Lemma univ_formation_S {n : nat} :
      τ[S n] ⊧ (Tm.univ n) ∼ (Tm.univ n).
    Proof.
      prove_rule Sig.init.
    Qed.

    Theorem univ_formation {n i : nat} :
      i < n
      → τ[n] ⊧ (Tm.univ i) ∼ (Tm.univ i).
    Proof.
      case => [| j q ].
      + apply: univ_formation_S.
      + eexists.
        rewrite /Tower.t -Clo.roll; split;
        apply: Sig.init;
        Spine.simplify;
        exists i; repeat split;
        [omega | eauto | omega | eauto].
    Qed.


    Theorem prod_formation {n : nat} :
      ∀ A B,
        τ[n] ⊧ A ∼ A
        → τ[n] ⊧ B ∼ B
        → τ[n] ⊧ (Tm.prod A B) ∼ (Tm.prod A B).
    Proof.
      move=> A B D E.
      rewrite /Tower.t /atomic_eq_ty in D E.
      prove_rule Sig.prod.
    Qed.

    Lemma TowerChoice {n : nat} {A1 A2 : CLK → Tm.t 0} :
      (∀ κ, ∃ Rκ, τ[n] (A1 κ, Rκ) ∧ τ[n] (A2 κ, Rκ))
      → ∃ S, ∀ κ, τ[n] (A1 κ, S κ) ∧ τ[n] (A2 κ, S κ).
    Proof.
      move=> X.
      apply: (unique_choice (fun κ R => τ[n] (A1 κ, R) ∧ τ[n] (A2 κ, R))) => κ.
      case: (X κ) => S T.
      eexists; split; eauto => S' T';
      apply: Tower.extensionality; eauto;
      T.destruct_conjs; eauto.
    Qed.

    Theorem isect_formation {n : nat} :
      forall B,
        (∀ κ, τ[n] ⊧ (B κ) ∼ (B κ))
        → τ[n] ⊧ (Tm.isect B) ∼ (Tm.isect B).
    Proof.
      move=> B D.
      rewrite /Tower.t /atomic_eq_ty in D.
      case: (TowerChoice D) => S E'.
      prove_rule Sig.isect => κ;
      specialize (E' κ);
      rewrite /Tower.t in E';
      T.destruct_conjs;
      eauto.
    Qed.


    Theorem isect_irrelevance :
      forall A B,
        τω ⊧ A ∼ B
        → τω ⊧ A ∼ (Tm.isect (fun _ => B)).
    Proof.
      rewrite /τω.
      move=> A B [R ?].
      T.destruct_conjs.
      rewrite /atomic_eq_ty.
      repeat T.split; eauto.
      rewrite /Tower.t -Clo.roll; apply: Sig.isect.
      do 2 eexists (fun _ => _).
      repeat T.split; eauto.
      T.eqcd => *.
      case: LocalClock => ? _.
      apply: propositional_extensionality.
      T.split; auto.
    Qed.


    Theorem eq_ty_from_level :
      ∀ n A B,
        τ[n] ⊧ A ∼ B
        → τω ⊧ A ∼ B.
    Proof.
      move=> n A B [R [TA TB]].
      eexists.
      split.
      + eexists; eauto.
      + eexists; eauto.
    Qed.

    Hint Resolve unit_formation univ_formation eq_ty_from_level prod_formation isect_formation isect_irrelevance.

  Theorem test : τω ⊧ (Tm.prod Tm.unit (Tm.univ 0)) ∼ (Tm.prod Tm.unit (Tm.univ 0)).
  Proof.
    eauto.
  Qed.

  Theorem test2 : τω ⊧ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)).
    eauto.
  Qed.

End Closed.