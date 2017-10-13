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
  + elim; rewrite /M.based_functional /Tower;
    move=> *; Clo.destruct_clos;
    Spine.simplify; Clo.noconfusion.
    ++ congruence.
    ++ congruence.
    ++ T.reorient.
       Clo.specialize_functionality_ih => p q.
       rewrite p q.
       congruence.
    ++ T.reorient.
       repeat T.eqcd => *.
       Later.gather => *; destruct_conjs.
       Clo.specialize_functionality_ih.
       congruence.
    ++ T.reorient.
       repeat T.eqcd => *.
       T.specialize_hyps; Clo.specialize_functionality_ih.
       congruence.
    ++ congruence.
Qed.


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

  Theorem unit : ∀ i j, Monotone i j Tm.unit.
  Proof.
    move=> i j R p; rewrite /Tower; Clo.destruct_clo; Clo.noconfusion; rewrite -Clo.roll.
    + induction i as [|i' ih].
      ++ apply: Sig.unit.
         Spine.simplify.
         Clo.destruct_clos; Clo.noconfusion.
      ++ apply: ih; first omega.
         Spine.simplify.
         Clo.noconfusion.
    + by [apply: Sig.unit].
  Qed.

  Theorem bool : ∀ i j, Monotone i j Tm.bool.
  Proof.
    move=> i j R p; rewrite /Tower;
    Clo.destruct_clo => //= *.
    + induction i as [| i' ih].
      ++ rewrite -Clo.roll; apply: Sig.bool.
         Spine.simplify.
         Clo.destruct_clos.
      ++ apply: ih; first omega.
         Spine.simplify.
         Clo.noconfusion.

    + rewrite -Clo.roll.
      induction i as [| i' ih ].
      ++ by [apply: Sig.bool].
      ++ apply: ih.
         omega.
  Qed.



  Theorem prod :
    ∀ i j A B,
      Monotone i j A
      → Monotone i j B
      → Monotone i j (Tm.prod A B).
  Proof.
    move=> i j A B ihA ihB R p; rewrite /Tower => *.
    rewrite -Clo.roll.
    apply: Sig.prod.
    Clo.destruct_clos; Clo.noconfusion.
    + induction i; Clo.noconfusion; Spine.simplify;
      Clo.destruct_clos; Clo.noconfusion; Spine.simplify;
      repeat T.split; eauto.
      ++ apply: ihA; auto.
         rewrite /Tower Clo.idempotence; eauto.
      ++ apply: ihB; auto.
         rewrite /Tower Clo.idempotence; eauto.
    + repeat T.split; eauto.
      ++ by [apply: ihA].
      ++ by [apply: ihB].
  Qed.


  Theorem ltr :
    ∀ i j κ A,
      Monotone i j A
      → Monotone i j (Tm.ltr κ A).
  Proof.
    move=> i ? ? ? ihA ? ?; rewrite /Tower => ?; rewrite -Clo.roll.
    apply: Sig.later.
    Clo.destruct_clos; Clo.noconfusion; Spine.simplify.
    + induction i; Clo.noconfusion; Spine.simplify;
      Clo.destruct_clos; Clo.noconfusion; Spine.simplify.
      repeat T.split; eauto.
      apply: Later.map => [X|]; last eauto.
      apply: ihA; eauto.
      rewrite /Tower Clo.idempotence.
      eauto.
    + repeat T.split; eauto.
      apply: Later.map => *; last eauto.
      by [apply: ihA].
  Qed.


  Theorem isect :
    ∀ i j A,
      (∀ κ, Monotone i j (A κ))
      → Monotone i j (Tm.isect A).
  Proof.
    move=> i ? ? ihA ? ?; rewrite /Tower => *.
    rewrite -Clo.roll.
    apply: Sig.isect.
    Clo.destruct_clos; Clo.noconfusion; Spine.simplify.
    + induction i; Clo.noconfusion; Spine.simplify;
      Clo.destruct_clos; Clo.noconfusion;
      repeat T.split; eauto => *.
      T.specialize_hyps.
      apply: ihA; auto.
      rewrite /Tower Clo.idempotence.
      eauto.

    + repeat T.split; eauto => *.
      T.specialize_hyps.
      by [apply: ihA].
  Qed.


  Theorem tower :
    ∀ A i j, Monotone i j A.
  Proof.
    elim.
    + intros.
      omega.
    + apply: unit.
    + apply: bool.

    + move=> i j R; rewrite /Monotone /Tower => *.
      Clo.destruct_clos; induction i; Spine.simplify => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + move=> i j R; rewrite /Monotone /Tower => *.
      Clo.destruct_clos; induction i; Spine.simplify => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + move=> i j R; rewrite /Monotone /Tower => *.
      Clo.destruct_clos; induction i; Spine.simplify => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + intros; apply: prod; eauto.

    + rewrite /Monotone /Tower => ? ? ? ? i *.
      Clo.destruct_clos; Clo.noconfusion.
      induction i; Spine.simplify; Clo.destruct_clos; Clo.noconfusion.

    + rewrite /Monotone /Tower => ? ? ? ? i *.
      Clo.destruct_clos; Clo.noconfusion.
      induction i; Spine.simplify; Clo.destruct_clos; Clo.noconfusion.

    + move=> *; apply: ltr; eauto.
    + move=> *; apply: isect; eauto.
    + move=> n i j; rewrite /Monotone /Tower => R p.
      Clo.destruct_clo => *.
      induction i.
      ++ Spine.simplify.
         Clo.destruct_clos.
      ++ Spine.simplify.
         T.destruct_conjs.
         T.destruct_evals.

         have: ∃ j', j = S j'.
         +++ induction j.
             ++++ omega.
             ++++ eauto.
         +++ move=> [j' q].
             rewrite q -Clo.roll.
             apply: Sig.init.
             Spine.simplify.
             simpl.
             repeat T.split; [idtac | constructor | idtac].
             ++++ omega.
             ++++ eauto.
  Qed.
End Monotone.