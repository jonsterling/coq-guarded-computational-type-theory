Require Import Unicode.Utf8 Program.Equality Program.Tactics Setoids.Setoid omega.Omega.

Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From ctt Require Import OrderTheory Axioms Program OpSem Closure TypeSystem.
From ctt Require Tactic.

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
          fst X ⇓ Prog.univ j
          ∧ snd X = fun es =>
                      ∃ S, Clo.t (@t j _) (fst es, S) ∧ Clo.t (@t j _) (snd es, S)
    end.

  Theorem unfold_S :
    ∀ n,
      t (S n) =
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Prog.univ j
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

  Instance universe_system : ∀ i, TS.universe_system (t i).
  Proof.
    case.
    + simplify; by [firstorder].
    + move=> ?; constructor=> ? ?.
      simplify.
      T.destruct_conjs.
      eauto.
  Qed.

  Instance extensionality : ∀ i, TS.extensional (t i).
  Proof.
    case.
    + simplify; by [firstorder].
    + move=> ?; constructor=> ? ? ? ? ?.
      simplify.
      T.destruct_conjs; simpl in *.
      OpSem.evals_to_eq; T.destruct_eqs.
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

  Instance type_computational : ∀ i, TS.type_computational (t i).
    move=> i.
    induction i; constructor.
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

  Instance cper_valued : ∀ i, TS.cper_valued (t i).
  Proof.
    move=> i.
    induction i; constructor.
    - constructor; contradiction.
    - constructor; Spine.simplify.
      + constructor.
        * move=> M0 M1 M0M1.
          case: H => //= [j [? [? Rspec]]].
          rewrite Rspec in M0M1.
          rewrite Rspec.
          case: M0M1 => [S [H1 H2]].
          eauto.
        * move=> M0 M1 M2 M0M1 M1M2.
          case: H => //= [j [? [? Rspec]]].
          rewrite Rspec in M0M1 M1M2.
          rewrite Rspec.
          case: M0M1 => //= [S [H1 H2]].
          case: M1M2 => //= [S' [H1' H2']].
          exists S; T.split; first by [eauto].
          replace S with S'; auto.
          apply: (TS.is_extensional _ _ _ H1' _ H2).

      + move=> ? ? ? ? H'.
        case: H => //= [j [? [? Rspec]]].
        rewrite Rspec.
        rewrite Rspec in H'.
        simpl in *.
        T.destruct_conjs.
        eauto.
        esplit; split; eauto.

        apply: TS.is_type_computational; last by [eauto].
        eauto.
  Qed.

  Ltac spine_contradiction :=
    lazymatch goal with
    | H : Spine.t _ (Prog.univ _, _) |- _ => fail "This is a universe!"
    | H : Spine.t ?n (_, _) |- _ =>
      induction n; Spine.simplify;
      [contradiction | T.destruct_conjs; OpSem.destruct_evals]
    end.

  Hint Resolve monotonicity.
End Spine.

Module Tower.

  Definition t (i : nat) : cts :=
    Clo.t (Spine.t i).

  Instance extensionality {i} : TS.extensional (t i).
  Proof.
    typeclasses eauto.
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
      try (Clo.destruct_has; OpSem.destruct_evals)
    | H : Clo.t (Spine.t ?i) _ |- _ =>
      rewrite /t in H; Clo.destruct_clo; try by [Spine.spine_contradiction];
      try (Clo.destruct_has; OpSem.destruct_evals)
    end.


  Instance cper_valued {i} : TS.cper_valued (t i).
  Proof.
    typeclasses eauto.
  Qed.

  Instance type_computational {i} : TS.type_computational (t i).
  Proof.
    typeclasses eauto.
  Qed.

  Hint Resolve monotonicity.
End Tower.


Definition τω : cts :=
  fun X =>
    ∃ n, Tower.t n X.

Notation "'τ[' n ']'" := (Tower.t n).

Instance τω_extensionality : TS.extensional τω.
Proof.
  constructor=> A R.
  rewrite /τω.
  move=> [n1 AR] R' //= [n2 AR'].
  apply: TS.is_extensional.
  + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
    omega.
  + apply: (@Tower.monotonicity _ (n1 + n2)); last eauto.
    omega.
Qed.

Instance τω_type_computational : TS.type_computational τω.
Proof.
  constructor=> A0 R [nH H] A1 //= A01.
  eexists; apply: TS.is_type_computational; eauto.
Qed.

Instance τω_cper_valued : TS.cper_valued τω.
Proof.
  constructor=> A R.
  rewrite /τω.
  move=> [nH H].
  constructor.

  - split => *;
    [apply: symmetric | apply: transitive]; eauto;
    apply: per;
    apply: TS.is_cper_valued;
    eauto.
  - move=> *.
    apply: crel; eauto.
    apply: TS.is_cper_valued; eauto.
Qed.