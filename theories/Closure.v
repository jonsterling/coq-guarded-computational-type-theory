Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect.

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.



From gctt Require Tactic.
Module T := Tactic.
Module M := Matrix.


Set Implicit Arguments.



Ltac specialize_clocks κ :=
  repeat match goal with
  | X : ∀ (κ : CLK), ?P |- _ => specialize (X κ)
  end.


Ltac destruct_evals :=
  repeat
    match goal with
      | H : ?A ⇓ ?B |- _ => dependent destruction H
    end.


Ltac destruct_eval :=
  match goal with
  | |- _ ⇓ _ → _ => let x := fresh in move=> x; dependent destruction x
  end.

Ltac backthruhyp :=
  let H := fresh in
  match goal with
  | H : _ → ?P |- ?P => apply H
  end.

Ltac specialize_hyps :=
  repeat
    match goal with
    | H : ∀ κ : CLK, ?P, κ : CLK |- _ => specialize (H κ)
    | H : ?R (?e1, ?e2) -> ?P, H' : ?R (?e1, ?e2) |- _ => specialize (H H')
    end.


Theorem universal_extensionality :
  ∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x = Q x)
    → (∀ x, P x) = (∀ x, Q x).
Proof.
  move=> A P Q E.
  apply: propositional_extensionality; T.split => *.
  ++ rewrite -E. auto.
  ++ rewrite E. auto.
Qed.

Theorem later_extensionality :
  ∀ κ (P Q : Prop),
    (▷[κ] (P = Q))
    → (▷[κ] P) = (▷[κ] Q).
Proof.
  move=> κ P Q E.
  apply: propositional_extensionality.
  T.split => *; Later.gather; move=> [X Y].
  ++ rewrite -X; auto.
  ++ rewrite X; auto.
Qed.


Ltac reorient :=
  match goal with
  | H : ?Y = _ |- ?X = ?Y => symmetry; etransitivity; first eassumption
  end.

Ltac eqcd :=
  apply: universal_extensionality
  || apply: later_extensionality
  || apply: functional_extensionality.





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
    ∀ (σ : M.matrix) (X : Tm.t 0 * M.behavior) (P : Prop),
      t σ X
      → (σ X → P)
      → (Close.unit (t σ) X → P)
      → (Close.bool (t σ) X → P)
      → (Close.prod (t σ) X → P)
      → (Close.isect (t σ) X → P)
      → (Close.later (t σ) X → P)
      → P.
  Proof.
    move=> σ [A R] P C init unit bool prod isect later.
    rewrite -roll in C.
    case: C; auto.
  Qed.


  Ltac noconfusion :=
    try by [contradiction];
    rewrite /M.empty;
    move=> *; simpl in *;
          T.destruct_conjs;
          destruct_evals.


  Ltac destruct_clo :=
    let x := fresh in move=> x; apply: (ind x); clear x;
    try by [noconfusion].

  Ltac destruct_clos :=
    repeat
      match goal with
      | T : Clo.t _ _ |- _ =>
        move: T;
        destruct_clo
      end.

  Ltac specialize_functionality_ih :=
    repeat
      match goal with
      | H : ∀ R1 R2 : M.behavior, t _ (?X, _) → t _ (?X, _) → _ = _, H' : t _ (?X, ?R1), H'' : t _ (?X, ?R2) |- _ => specialize (H _ _ H' H''); move: H
  end.


  Theorem functionality : M.functional (t M.empty).
  Proof.
    elim; rewrite /M.based_functional;
    move=> *; try by [destruct_clos => //= *; noconfusion];
    destruct_clos => *; noconfusion.
    + congruence.
    + congruence.
    + specialize_functionality_ih => p1 p2.
      rewrite p1 p2.
      congruence.
    + reorient.
      repeat eqcd => *.
      Later.gather => *; T.destruct_conjs.
      specialize_functionality_ih => p;
      congruence.
    + reorient.
      repeat eqcd => *.
      specialize_hyps.
      specialize_functionality_ih => *.
      congruence.
  Qed.


  Theorem idempotence : t (t M.empty) = t M.empty.
  Proof.
    apply: functional_extensionality.
    case; elim; try by [move=> *; apply: propositional_extensionality; T.split; destruct_clo];

    move=> *; apply: propositional_extensionality.

    + T.split; destruct_clo => *; rewrite -roll;
      apply: Sig.unit; by [Clo.noconfusion].

    + T.split; destruct_clo => *; rewrite -roll;
      apply: Sig.bool; by [Clo.noconfusion].


    + T.split; destruct_clo => //= *;
      T.destruct_conjs; rewrite -roll; apply: Sig.prod;
      repeat T.split; eauto; destruct_evals;
      by [congruence].

    + T.split; destruct_clo => //= *;
      T.destruct_conjs; rewrite -roll;
      apply: Sig.later;
      repeat T.split; destruct_evals; eauto.
      ++ by [congruence].
      ++ by [congruence].

    + T.split; destruct_clo => //= *;
      T.destruct_conjs; rewrite -roll;
      apply: Sig.isect;
      repeat T.split; auto; destruct_evals; eauto => *;
      specialize_hyps; by [congruence].
  Qed.

End Clo.
