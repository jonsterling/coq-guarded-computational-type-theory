Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.
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
    fun X => ∃ n, Tower n X.


  (* TODO: move to a general location *)
  Theorem nat_max_leq :
    ∀ i j,
      i ≤ max i j.
  Proof.
    case => j.
    + omega.
    + case; firstorder.
  Qed.

  Theorem nat_max_commutative :
    ∀ i j,
      max i j = max j i.
  Proof.
    elim.
    + case; auto.
    + move=> n IH; elim.
      ++ auto.
      ++ move=> n' p.
         simpl.
         rewrite IH.
         auto.
  Qed.

  (* To show that the maximal refinement matrix is functional, we need
      to deal with type-behavior assignments at different levels.
      However, we can take the maximum of these levels, by
      monotonicity bring the assignments up to a common level. *)
  Theorem Towerω_functional : M.functional Towerω.
  Proof.
    move=> A R1 R2 [n1 AR1] [n2 AR2].
    apply: Tower.functionality.
    + apply: Tower.Monotone.tower;
      first (apply: nat_max_leq; shelve);
      eauto.
    + apply: Tower.Monotone.tower;
      first (rewrite nat_max_commutative; apply: nat_max_leq);
      eauto.
  Qed.


  Notation "n ⊩ A type" := (∃ R, Tower n (A, R)) (at level 0, A at level 0, only parsing).
  Notation "n ⊩ A ∼ B type" := (∃ R, Tower n (A, R) ∧ Tower n (B, R)) (at level 0, A at level 0, B at level 0, only parsing).
  Notation "ω⊩ A type" := (∃ R, Towerω (A, R)) (at level 0, A at level 0, only parsing).

  Module ClosedRules.

    (* A nice hack from Adam Chlipala Theory, to force the resolution of *)
(*        some existential variables. *)
    Ltac equate M N :=
      let r := constr:(eq_refl M : M = N)
      in idtac.

    Ltac simplify :=
      simpl; Spine.simplify; simpl;
      repeat
        (match goal with
         | |- ∃ (R : M.behavior), Tower ?n ?X => eexists; rewrite -Tower.roll
         | |- ?i ≤ ?j => omega
         | |- ∃ (x : ?A), ?P => eexists
         | |- ?P ∧ ?Q => split
         | |- ?P ↔ ?Q => split
         end); eauto.

    (* A tactic to prove a rule by appealing to one of the *)
(*        constructors of the refinement matrix closure operator. *)
    Ltac prove_rule con :=
      match goal with
      | |- ?n ⊩ ?A type => eexists; rewrite -Tower.roll; apply: con; simplify; try reflexivity
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
        rewrite -Tower.roll.
        apply: Sig.init.
        Spine.simplify.
        exists i. repeat split.
        ++ omega.
        ++ constructor.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      move=> A B [R1 D] [R2 E].
      prove_rule Sig.prod.
    Qed.

    Lemma TowerChoice {n : nat} {A : CLK → Tm.t 0} :
      (∀ κ, ∃ Rκ, Tower n (A κ, Rκ))
      → ∃ S, ∀ κ, Tower n (A κ, S κ).
    Proof.
      move=> X.
      apply: (unique_choice (fun κ R => Tower n (A κ, R))) => κ.
      case: (X κ) => S T.
      eexists; split; eauto => S' T'.
      apply: Tower.functionality; eauto.
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
      forall n A,
        n ⊩ A type
        → n ⊩ A ∼ (Tm.isect (fun _ => A)) type.
    Proof.
      move=> n A [R AR].
      eexists; split; eauto.
      rewrite -Tower.roll; apply: Sig.isect.
      exists (fun _ => A), (fun _ => R).
      repeat T.split; eauto.
      T.eqcd => *.
      case: LocalClock => ? _.
      apply: propositional_extensionality.
      split; auto.
    Qed.

    Hint Resolve unit_formation univ_formation prod_formation isect_formation isect_irrelevance.
  End ClosedRules.

  Theorem test : ∃ n, n ⊩ (Tm.prod Tm.unit (Tm.univ 0)) type.
  Proof.
    eauto.
  Qed.

  Theorem test2 : ∃ n, n ⊩ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)) type.
    eauto.
  Qed.

End Univ.
