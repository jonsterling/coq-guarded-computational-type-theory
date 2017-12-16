Require Import Unicode.Utf8 Program.Equality Program.Tactics Setoids.Setoid omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory Axioms Term Closure TypeSystem.
From gctt Require Tactic.

Module T := Tactic.

Set Implicit Arguments.

Module Spine.
  Local Obligation Tactic := firstorder.
  Program Fixpoint t (n : nat) {measure n} : cts :=
    match n with
    | 0 => empty
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
    t 0 = empty.
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

  Theorem universe_system : ∀ i, TS.universe_system (t i).
  Proof.
    case.
    + simplify; by [firstorder].
    + move=> ? ? ?.
      simplify.
      T.destruct_conjs.
      eauto.
  Qed.

  Theorem extensionality : ∀ i, TS.extensional (t i).
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

  Theorem type_computational : ∀ i, TS.type_computational (t i).
    move=> i.
    induction i.
    - move=> ? ? ?.
      contradiction.
    - Spine.simplify.
      move=> //= ? ? [j [p [? Rspec]]].
      simpl in *.
      move=> //= A1 A01.
      exists j; exists p.
      T.split.
      * by apply: A01.
      * eauto.
  Qed.

  Theorem cper_valued : ∀ i, TS.cper_valued (t i).
  Proof.
    move=> i.
    induction i.
    - constructor; contradiction.
    - constructor; Spine.simplify.
      + constructor.
        * move=> e0 e1 e0e1.
          case: H => //= [j [? [? Rspec]]].
          rewrite Rspec in e0e1.
          rewrite Rspec.
          case: e0e1 => [S [H1 H2]].
          eauto.
        * move=> e0 e1 e2 e0e1 e1e2.
          case: H => //= [j [? [? Rspec]]].
          rewrite Rspec in e0e1 e1e2.
          rewrite Rspec.
          case: e0e1 => //= [S [H1 H2]].
          case: e1e2 => //= [S' [H1' H2']].
          exists S; T.split; first by [eauto].
          replace S with S'; auto.
          apply: Clo.extensionality.
          ** apply: universe_system j.
          ** apply: extensionality.
          ** exact H1'.
          ** exact H2.
      + move=> ? ? ? ? H'.
        case: H => //= [j [? [? Rspec]]].
        rewrite Rspec.
        rewrite Rspec in H'.
        simpl in *.
        T.destruct_conjs.
        eauto.
        esplit; split; eauto.
        apply: Clo.type_computational; [apply: type_computational | idtac | eauto].
        eauto.
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

  Definition t (i : nat) : cts :=
    Clo.t (Spine.t i).

  Theorem extensionality : ∀ i, TS.extensional (t i).
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

  Theorem cper_valued : ∀ i, TS.cper_valued (t i).
  Proof.
    move=> i A R H.
    apply: Clo.cper_valued.
    - apply: Spine.cper_valued; eauto.
    - eauto.
  Qed.
End Tower.


Definition τω : cts :=
  fun X =>
    ∃ n, Tower.t n X.

Notation "'τ[' n ']'" := (Tower.t n).

Theorem τω_extensionality : TS.extensional τω.
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

Theorem τω_per_valued : TS.cper_valued τω.
Proof.
  move=> A R.
  rewrite /τω.
  move=> [nH H].
  constructor.

  - constructor.
    + move=> e0 e1 e0e1.
      edestruct (@Tower.cper_valued nH); eauto.
      destruct per.
      eauto.

    + move=> e0 e1 e2 e0e1 e1e2.
      edestruct (@Tower.cper_valued nH); eauto.
      destruct per.
      eauto.

  - move=> ? ? ? ? ?.
    edestruct (@Tower.cper_valued nH); eauto.
Qed.
