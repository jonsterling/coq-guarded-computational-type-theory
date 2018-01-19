Require Import Unicode.Utf8 Program.Equality Program.Tactics Setoids.Setoid omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory Axioms Term OpSem Closure TypeSystem.
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
    | H : Spine.t _ (Tm.univ _, _) |- _ => fail "This is a universe!"
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

Definition extensional_core (τ : cts) : cts :=
  fun X =>
    τ X ∧ TS.extensional_at τ X.

Definition extensional_core_extensional : ∀ τ, TS.extensional (extensional_core τ).
Proof.
  move=> τ; split => A R1 [𝒟1 ℰ1] R2 //= [𝒟2 ℰ2].
  apply: ℰ1; auto.
Qed.

Program Definition cts_succ {κ} (τ : ▶[κ] cts) : cts :=
  fun X => LaterT.succ (LaterT.map (fun τ' => τ' X) τ).

Program Definition τ_infty (κ : 𝕂) : cts :=
  LaterT.loeb (fun τ : ▶[κ] cts => Clo.t (extensional_core (cts_succ τ))).

Notation "'τ∞'" := τ_infty.

Instance τ_infty_extensionality : ∀ κ, TS.extensional (τ∞ κ).
Proof.
  move=> κ.
(*  eapply (@Later.loeb κ) => IH.*)
  constructor => ? R1.
  move=> 𝒟; rewrite /τ∞ LaterT.loeb_spec in 𝒟; move: 𝒟.
  Clo.elim_clo; clear H.
  - move=> [A R] [𝒟1 𝒟2] R' //= ℰ.
    rewrite /cts_succ LaterT.map_spec -LaterT.succ_spec in 𝒟1.
    rewrite /τ∞ LaterT.loeb_spec in ℰ.
    Clo.destruct_clo.
    + destruct H.
      rewrite /cts_succ LaterT.map_spec -LaterT.succ_spec in H.
      apply: 𝒟2.
      rewrite /cts_succ LaterT.map_spec -LaterT.succ_spec.
      auto.
    + apply: 𝒟2.
      rewrite /cts_succ LaterT.map_spec -LaterT.succ_spec //=.
      apply: Later.next.
      rewrite LaterT.loeb_spec.
      rewrite -Clo.roll.
      apply: Sig.conn; eauto.
  -
Abort.




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