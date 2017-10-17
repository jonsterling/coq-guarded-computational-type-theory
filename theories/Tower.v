Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.
From gctt Require Import Closure.

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


Set Implicit Arguments.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Module Spine.
  Local Obligation Tactic := firstorder.
  Program Fixpoint t (n : nat) {measure n (lt)} : M.matrix :=
    match n with
    | 0 => Clo.t M.empty
    | S n =>
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Tm.univ j
          ∧ snd X = fun es =>
                      ∃ S, Clo.t (@t j _) (fst es, S) ∧ Clo.t (@t j _) (snd es, S)
    end.

  Theorem unfold_S :
    ∀ X n,
      t (S n) X =
      ∃ (j : nat) (p : j ≤ n),
        fst X ⇓ Tm.univ j
        ∧ snd X =
          fun es =>
            ∃ S, Clo.t (t j) (fst es, S) ∧ Clo.t (t j) (snd es, S).
  Proof.
    move=> X n.
    by [Wf.WfExtensionality.unfold_sub t (t (S n) X)].
  Qed.

  Theorem unfold_0 :
    ∀ X, t 0 X = Clo.t M.empty X.
  Proof.
    move=> X.
      by [Wf.WfExtensionality.unfold_sub t (t 0 X)].
  Qed.

  Ltac simplify :=
    repeat match goal with
    | X : t 0 _ |- _ => rewrite unfold_0 in X
    | X : t (S _) _ |- _ => rewrite unfold_S in X
    | _ => rewrite unfold_S || rewrite unfold_0
    end.
End Spine.

Definition Tower (i : nat) : M.matrix :=
  Clo.t (Spine.t i).

Theorem functionality : ∀ i, M.functional (Tower i).
Proof.
  case => *.
  + rewrite /Tower //= Clo.idempotence.
    apply: Clo.functionality; eauto.
  + admit.
Admitted.


Theorem roll {i : nat} : Sig.t (Spine.t i) (Tower i) = Tower i.
Proof.
  apply: binrel_extensionality => A R.
  split => H.
  + rewrite /Tower /Clo.t.
    match goal with
    | |- lfp ?m ?x =>
      case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x)
    end.
    auto.
  + rewrite /Tower /Clo.t in H.
    match goal with
    | H : lfp ?m ?x |- _ =>
      case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x) => _
    end.
    apply.
    auto.
Qed.

Module Monotone.
  Definition Monotone (i j : nat) (A : Tm.t 0) : Prop :=
    ∀ R,
      i ≤ j
      → Tower i (A, R)
      → Tower j (A, R).


  Theorem tower :
    ∀ A i j, Monotone i j A.
  Proof.
    admit.
  Admitted.

End Monotone.