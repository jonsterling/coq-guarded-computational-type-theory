Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Term.
From gctt Require Import Closure.

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.Setoids.Setoid.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


Set Implicit Arguments.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Module Spine.
  Local Obligation Tactic := firstorder.
  Program Fixpoint t (n : nat) {measure n} : M.matrix :=
    match n with
    | 0 => M.empty
    | S n =>
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Tm.univ j
          ∧ snd X = fun es =>
                      ∃ S, Clo.t (@t j _) (fst es, S) ∧ Clo.t (@t j _) (snd es, S)
    end.

  Theorem unfold_S :
    ∀ n,
      t (S n) =
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Tm.univ j
          ∧ snd X =
            fun es =>
              ∃ S, Clo.t (t j) (fst es, S) ∧ Clo.t (t j) (snd es, S).
  Proof.
    move=> n.
    T.eqcd => X.
    by [Wf.WfExtensionality.unfold_sub t (t (S n) X)].
  Qed.

  Theorem unfold_0 :
    t 0 = M.empty.
  Proof.
    T.eqcd => X.
    by [Wf.WfExtensionality.unfold_sub t (t 0 X)].
  Qed.

  Ltac simplify :=
    repeat match goal with
    | X : t 0 _ |- _ => rewrite unfold_0 in X
    | X : t (S _) _ |- _ => rewrite unfold_S in X
    | _ => rewrite unfold_S || rewrite unfold_0
    end.

  Theorem universe_system : ∀ i, M.Law.universe_system (t i).
  Proof.
    case.
    + simplify; by [firstorder].
    + move=> ? ? ?.
      simplify.
      T.destruct_conjs.
      eauto.
  Qed.

  Theorem extensionality : ∀ i, M.Law.extensional (t i).
  Proof.
    case.
    + simplify; by [firstorder].
    + move=> ? ? ? ? ? ?.
      simplify.
      T.destruct_conjs; simpl in *.
      Term.evals_to_eq; T.destruct_eqs.
      auto.
  Qed.

  Theorem monotonicity : ∀ i j, i ≤ j → t i ⊑ t j.
  Proof.
    move=> i j p [A R] T.
    induction i; simplify.
    + contradiction.
    + case: T => [j' [p' //= [evA spR]]].
      induction p; Spine.simplify; exists j'; eauto.
      esplit; [omega | eauto].
  Qed.

  Theorem per_valued : ∀ i, M.Law.per_valued (t i).
  Proof.
    move=> i.
    induction i.
    - constructor; contradiction.
    - constructor; Spine.simplify.
      + move=> e0 e1 e0e1.
        case: H => //= [j [? [? Rspec]]].
        rewrite Rspec in e0e1.
        rewrite Rspec.
        case: e0e1 => [S [H1 H2]].
        eauto.
      + move=> e0 e1 e2 e0e1 e1e2.
        case: H => //= [j [? [? Rspec]]].
        rewrite Rspec in e0e1 e1e2.
        rewrite Rspec.
        case: e0e1 => //= [S [H1 H2]].
        case: e1e2 => //= [S' [H1' H2']].
        exists S; T.split.
        * eauto.
        * replace S with S'; auto.
          apply: Clo.extensionality.
          ** apply: universe_system j.
          ** apply: extensionality.
          ** exact H1'.
          ** exact H2.
  Qed.

  Ltac spine_contradiction :=
    lazymatch goal with
    | H : Spine.t _ (Tm.univ _, _) |- _ => fail "This is a universe!"
    | H : Spine.t ?n (_, _) |- _ =>
      induction n; Spine.simplify;
      [contradiction | T.destruct_conjs; Term.destruct_evals]
    end.

  Hint Resolve universe_system extensionality monotonicity.
End Spine.

Module Tower.

  Definition t (i : nat) : M.matrix :=
    Clo.t (Spine.t i).

  Theorem extensionality : ∀ i, M.Law.extensional (t i).
  Proof.
    rewrite /t => *.
    eauto.
  Qed.

  Local Hint Constructors Sig.t.

  Theorem monotonicity : ∀ i j, i ≤ j → t i ⊑ t j.
  Proof.
    move=> ? ? ? [A R]; Clo.elim_clo => ? ?; rewrite /t -Clo.roll;
    first (apply: Sig.init; apply: Spine.monotonicity); eauto.
    by [econstructor; eauto; rewrite -Clo.roll; eauto].
  Qed.

  Ltac destruct_tower :=
    lazymatch goal with
    | H : t ?n _ |- _ =>
      rewrite /t in H; Clo.destruct_clo; try by [Spine.spine_contradiction];
      try (Clo.destruct_has; Term.destruct_evals)
    end.

  Hint Resolve extensionality monotonicity.

  Theorem per_valued : ∀ i, M.Law.per_valued (t i).
  Proof.
    move=> i A R H.
    apply: Clo.per_valued.
    - apply: Spine.per_valued; eauto.
    - eauto.
  Qed.
End Tower.


Definition τω : M.matrix :=
  fun X =>
    ∃ n, Tower.t n X.

Notation "'τ[' n ']'" := (Tower.t n).

Theorem Towerω_extensionality : M.Law.extensional τω.
Proof.
  move=> A R.
  rewrite /τω.
  move=> [n1 AR] R' //= [n2 AR'].
  apply: Tower.extensionality.
  + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
    omega.
  + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
    omega.
Qed.

Theorem Towerω_per_valued : M.Law.per_valued τω.
Proof.
  move=> A R.
  rewrite /τω.
  move=> [nH H].
  constructor.

  - move=> e0 e1 e0e1.
    edestruct (@Tower.per_valued nH);
    eauto.


  - move=> e0 e1 e2 e0e1 e1e2.
    edestruct (@Tower.per_valued nH);
    eauto.
Qed.
