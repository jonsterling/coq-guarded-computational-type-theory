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

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.omega.Omega.


Set Implicit Arguments.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Module Univ.
  Local Obligation Tactic := firstorder.

  Definition Towerω : M.matrix :=
    fun X => ∃ n, Tower.t n X.

  (* To show that the maximal refinement matrix is functional, we need
      to deal with type-behavior assignments at different levels.
      However, we can take the maximum of these levels, by
      monotonicity bring the assignments up to a common level. *)
  Theorem Towerω_extensionality : M.Law.extensional Towerω.
  Proof.
    move=> A R.
    rewrite /Towerω.
    move=> [n1 AR] R' //= [n2 AR'].
    apply: Tower.extensionality.
    + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
      omega.
    + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
      omega.
  Qed.


  Notation "n ⊩ A type" := (∃ R, Tower.t n (A, R)) (at level 0, A at level 0, only parsing).
  Notation "n ⊩ A ∼ B" := (∃ R, Tower.t n (A, R) ∧ Tower.t n (B, R)) (at level 0, A at level 0, B at level 0, only parsing).
  Notation "⊧ A type" := (∃ R, Towerω (A, R)) (at level 0, A at level 0, only parsing).
  Notation "⊧ A ∼ B" := (∃ R, Towerω (A, R) ∧ Towerω (B, R)) (at level 0, A at level 0, only parsing).

  Module ClosedRules.
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
      move=> *; T.destruct_conjs;
      match goal with
      | |- ?n ⊩ ?A type => eexists; rewrite /Tower.t -Clo.roll; apply: con; simplify; try reflexivity
      end.

    Theorem unit_formation {n : nat} : n ⊩ Tm.unit type.
    Proof.
      prove_rule Sig.unit.
    Qed.

    Lemma univ_formation_S {n : nat}
      : (S n) ⊩ (Tm.univ n) type.
    Proof.
      prove_rule Sig.init.
    Qed.

    Theorem univ_formation {n i : nat} :
      i < n
      → n ⊩ (Tm.univ i) type.
    Proof.
      case => [| j q ].
      + apply: univ_formation_S.
      + eexists.
        rewrite /Tower.t -Clo.roll.
        apply: Sig.init.
        Spine.simplify.
        exists i. repeat split.
        ++ omega.
        ++ eauto.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      prove_rule Sig.prod.
    Qed.

    Lemma TowerChoice {n : nat} {A : CLK → Tm.t 0} :
      (∀ κ, ∃ Rκ, Tower.t n (A κ, Rκ))
      → ∃ S, ∀ κ, Tower.t n (A κ, S κ).
    Proof.
      move=> X.
      apply: (unique_choice (fun κ R => Tower.t n (A κ, R))) => κ.
      case: (X κ) => S T.
      eexists; split; eauto => S' T'.
      apply: Tower.extensionality; eauto.
    Qed.

    Theorem isect_formation {n : nat} :
      forall B,
        (∀ κ, n ⊩ (B κ) type)
        → n ⊩ (Tm.isect B) type.
    Proof.
      move=> B Q.
      case: (TowerChoice Q) => S Q'.
      prove_rule Sig.isect.
    Qed.

    Theorem isect_irrelevance :
      forall A,
        ⊧ A type
        → ⊧ A ∼ (Tm.isect (fun _ => A)).
    Proof.
      rewrite /Towerω.
      move=> A [R ?].
      T.destruct_conjs.
      repeat T.split; eauto.
      rewrite /Tower.t -Clo.roll; apply: Sig.isect.
      do 2 eexists (fun _ => _).
      repeat T.split; eauto.
      T.eqcd => *.
      case: LocalClock => ? _.
      apply: propositional_extensionality.
      split; auto.
    Qed.

    Theorem eq_ty_from_level :
      ∀ n A B,
        n ⊩ A ∼ B
        → ⊧ A ∼ B.
    Proof.
      move=> n A B [R [TA TB]].
      eexists.
      split.
      + eexists; eauto.
      + eexists; eauto.
    Qed.

    Theorem ty_from_level :
      ∀ n A,
        n ⊩ A type
        → ⊧ A type.
    Proof.
      move=> n A [R TA].
      eexists.
      eexists; eauto.
    Qed.



    Hint Resolve unit_formation univ_formation eq_ty_from_level ty_from_level prod_formation isect_formation isect_irrelevance.
  End ClosedRules.



  Theorem test : ∃ n, n ⊩ (Tm.prod Tm.unit (Tm.univ 0)) type.
  Proof.
    eauto.
  Qed.

  Theorem test2 : ⊧ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)).
    eauto.
  Qed.

End Univ.
