Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Import Axioms.
From gctt Require Import Terms.

Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.omega.Omega.


Set Implicit Arguments.



Hint Resolve Later.map.

(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := ℘ (Tm.t 0 * Tm.t 0).

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := ℘ (Tm.t 0 * behavior).


Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Ltac morphism_monotone :=
  match goal with
  | |- @mon_func _ _ _ _ ?m _ _ =>
    apply: (@mon_prop _ _ _ _ m);
    eauto
  end.

Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 ∧ e2 ⇓ e3) (at level 0).

  Ltac prove_monotone :=
    simpl; intros; destruct_conjs;
    repeat
      match goal with
      | |- ?P ∧ ?Q => split
      | |- ∃ (x : ?A), ?P => esplit
      end;
    eauto.

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ ∀ e1 e2,
            R (e1, e2) ↔ [e1, e2] ⇓ Tm.ax).
    + prove_monotone.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ ∀ e1 e2,
           R (e1, e2) ↔ ([e1, e2] ⇓ Tm.tt ∨ [e1, e2] ⇓ Tm.ff)).
    + prove_monotone.
  Defined.

  Definition later : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ κ B,
            A ⇓ Tm.ltr κ B
            ∧ ▷[ κ ] (τ (B, R))).
    + prove_monotone.
  Defined.

  Definition prod : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B C R1 R2,
            A ⇓ Tm.prod B C
            ∧ τ (B, R1)
            ∧ τ (C, R2)
            ∧ ∀ e1 e2,
                R (e1, e2) ↔ ∃ e11 e12 e21 e22,
                  (e1 ⇓ Tm.pair e11 e12)
                  ∧ (e2 ⇓ Tm.pair e21 e22)
                  ∧ R1 (e11, e21)
                  ∧ R2 (e12, e22)).
    + prove_monotone.
  Defined.

  Definition isect : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B S,
            A ⇓ Tm.isect B
            ∧ (∀ κ, τ (B κ, S κ))
            ∧ ∀ e1 e2, R (e1, e2) ↔ ∀ κ, S κ (e1, e2)).
    + prove_monotone.
  Defined.
End Close.

Module TyF.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : matrix) (X : Tm.t 0 * behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
  | isect of Close.isect τ X
  | later of Close.later τ X.

  (* The map defined above really is monotone. *)
  Definition mono (σ : matrix) : monotone matrix matrix.
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
End TyF.

(* Because the map is monotone, we can take its least fixed point to
   get a closure operator on refinement matrices.*)
Definition CTyF (σ : matrix) := lfp (TyF.mono σ).

Theorem CTyFUnroll (σ : matrix) : CTyF σ == TyF.mono σ (CTyF σ).
  rewrite /CTyF.
  symmetry.
  refine (lfp_fixed_point matrix _ (TyF.mono σ)).
Qed.


Module Univ.
  Definition Empty : matrix :=
    fun _ => False.

  Definition Spine (i : nat) : matrix.
  Proof.
    elim: i => [|i'].
    + exact (CTyF Empty).
    + move=> τ [A R].
      exact
        (∃ j,
            j <= i'
            ∧ A ⇓ Tm.univ j
            ∧ ∀ e1 e2,
                R (e1, e2) ↔
                  ∃ S, CTyF τ (e1, S) ∧ CTyF τ (e2, S)).
  Defined.

  Definition Nuprl (i : nat) : matrix :=
    CTyF (Spine i).

  Definition Nuprlω : matrix :=
    fun X => ∃ n, Nuprl n X.


  Notation "n ⊩ A type" := (∃ R, Nuprl n (A, R)) (at level 0, A at level 0, only parsing).
  Notation "ω⊩ A type" := (∃ R, Nuprlω (A, R)) (at level 0, A at level 0, only parsing).

  Theorem Roll {i : nat} :
    ∀ A R,
      TyF.t (Spine i) (Nuprl i) (A, R)
      → Nuprl i (A, R).
  Proof.
    move=> A R X.
    rewrite /Nuprl /CTyF.
    match goal with
    | |- lfp ?m ?x =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
    end.
    eauto.
  Qed.

  Theorem Unroll {i : nat} :
    ∀ A R,
      Nuprl i (A, R)
      → TyF.t (Spine i) (Nuprl i) (A, R).
  Proof.
    move=> A R X.
    rewrite /Nuprl /CTyF in X.
    match goal with
    | H : lfp ?m ?x |- _ =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ Q'
    end.
    apply: Q'.
    eauto.
  Qed.



  Module ClosedRules.

    (* A nice hack from Adam Chlipala Theory, to force the resolution of
       some existential variables. *)
    Ltac equate M N :=
      let r := constr:(eq_refl M : M = N)
      in idtac.

    Ltac simplify :=
      simpl;
      repeat
        (match goal with
         | |- ∃ (R : behavior), Nuprl ?n ?X => eexists; apply: Roll
         | |- ?i ≤ ?j => omega
         | |- ∃ (x : ?A), ?P => eexists
         | |- ?P ∧ ?Q => split

         (* We will often encounter a semantic specification for a relation
            before we have even filled it in (i.e. it is an existential variable).
            So, we can force it to be instantiated to exactly the right thing. *)
         | |- ∀ e1 e2, ?R (e1, e2) ↔ @?S e1 e2 =>
           equate R (fun e12 => S (fst e12) (snd e12));
           intros

         | |- ?P ↔ ?Q => split
         end); eauto.

    (* A tactic to prove a rule by appealing to one of the
       constructors of the refinement matrix closure operator. *)
    Ltac prove_rule con :=
      match goal with
      | |- ?n ⊩ ?A type => eexists; apply: Roll; apply: con; simplify
      end.

    Theorem unit_formation {n : nat} : n ⊩ Tm.unit type.
    Proof.
      prove_rule TyF.unit.
    Qed.

    Lemma univ_formation_S {n : nat}
      : (S n) ⊩ (Tm.univ n) type.
    Proof.
      prove_rule TyF.init.
    Qed.

    Theorem univ_formation {n i : nat} :
      i < n
      → n ⊩ (Tm.univ i) type.
    Proof.
      move=> p.
      elim: p => [| j q [R N]].
      + apply: univ_formation_S.
      + eexists.
        apply: Roll.
        apply: TyF.init.
        exists i.
        simplify.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      move=> A B [R1 D] [R2 E].
      prove_rule TyF.prod.
    Qed.


    (* TODO: This is certainly true, assuming propositional extensionality. *)
    Axiom NuprlFunctional :
      ∀ n A S S',
        Nuprl n (A, S)
        -> Nuprl n (A, S')
        → S = S'.

    (* TODO: this should follow from the fact that the Nuprl type system is functional,
     i.e. that unique behaviors are assigned to type codes. *)
    Lemma Choice {n : nat} {A : CLK → Tm.t 0} :
      (∀ κ, ∃ Rκ, Nuprl n (A κ, Rκ))
      → ∃ S, ∀ κ, Nuprl n (A κ, S κ).
    Proof.
      move=> X.
      apply: (unique_choice (fun κ R => Nuprl n (A κ, R))).
      move=> κ.
      case: (X κ) => S T.
      exists S.
      split; auto.
      move=> S' T'.
      apply: NuprlFunctional; eauto.
    Qed.

    Theorem isect_formation {n : nat} :
      forall B,
        (∀ κ, n ⊩ (B κ) type)
        → n ⊩ (Tm.isect B) type.
    Proof.
      move=> B Q.
      case: (Choice Q) => S Q'.
      prove_rule TyF.isect.
    Qed.

    Hint Resolve unit_formation univ_formation prod_formation isect_formation.
  End ClosedRules.


  Lemma CommuteExists {A B : Type} {P : A → B → Prop}
    : (∃ (a : A) (b : B), P a b)
      → ∃ (b : B) (a : A), P a b.
    firstorder.
  Qed.


  Theorem test : ω⊩ (Tm.prod Tm.unit (Tm.univ 0)) type.
  Proof.
    apply: CommuteExists.
    eauto.
  Qed.

End Univ.