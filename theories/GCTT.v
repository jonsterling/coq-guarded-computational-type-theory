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
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


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

Definition matrix_functional (σ : matrix) : Prop :=
  ∀ A R1 R2,
    σ (A, R1)
    → σ (A, R2)
    → R1 = R2.

Axiom propositional_extensionality :
  ∀ (P Q : Prop),
    (P ↔ Q)
    -> P = Q.

Theorem CTyF_Roll:
  ∀ σ,
    TyF.t σ (CTyF σ)
    = CTyF σ.
Proof.
  move=> σ.
  apply: functional_extensionality.
  move=> [A R].
  apply: propositional_extensionality.
  split => [X | X].
  + rewrite /CTyF.
    match goal with
    | |- lfp ?m ?x =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
    end.
    auto.
  + rewrite /CTyF in X.
    match goal with
    | H : lfp ?m ?x |- _ =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ Q'
    end.
    apply: Q'.
    auto.
Qed.


Definition Empty : matrix :=
  fun _ => False.

(* This proof would be routine, but because we formed the inductive definition using
   a semantic least fixed point, Coq doesn't automatically have the induction principle.
   So, I would have to prove this induction principle myself to make the inductive cases
   go through. *)
Theorem CTyF_Empty_functional : matrix_functional (CTyF (Empty)).
Proof.
  move=> A R1 R2 AR1 AR2.
  rewrite -CTyF_Roll in AR1, AR2.
  (elim: AR1; elim: AR2) => H1 H2;
    simpl in H1, H2;
    try contradiction;
    apply: functional_extensionality => es;
    apply: propositional_extensionality;
    destruct_conjs;
    split => esH;
    repeat progress match goal with
    | H : ∀ x1 x2 : Tm.t 0, ?R (x1, x2) ↔ @?Q x1 x2 |- ?R (?e1, ?e2) =>
      case (H e1 e2); clear H
    | H : ?A ⇓ ?B |- _ => dependent destruction H
    end; eauto.
  + firstorder.
  + firstorder.
  + move=> _; apply.
    destruct (H7 t t0).
    destruct (H esH).
    destruct_conjs.
    repeat esplit; eauto.
    ++ admit. (* need IH *)
    ++ admit. (* need IH *)
  + admit.
  + admit.
  + admit.
Admitted.



Module Univ.

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
  Notation "n ⊩ A ~ B type" := (∃ R, Nuprl n (A, R) ∧ Nuprl n (B, R)) (at level 0, A at level 0, B at level 0, only parsing).
  Notation "ω⊩ A type" := (∃ R, Nuprlω (A, R)) (at level 0, A at level 0, only parsing).

  Theorem Roll {i : nat} : TyF.t (Spine i) (Nuprl i) = Nuprl i.
  Proof.
    apply: functional_extensionality => X.
    apply: propositional_extensionality.
    split => H.
    + rewrite /Nuprl /CTyF.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
      end.
      auto.
    + rewrite /Nuprl /CTyF in H.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ Q'
      end.
      apply: Q'.
      auto.
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
         | |- ∃ (R : behavior), Nuprl ?n ?X => eexists; rewrite -Roll
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
      | |- ?n ⊩ ?A type => eexists; rewrite -Roll; apply: con; simplify
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
        rewrite -Roll.
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

    Theorem isect_irrelevance :
      forall n A,
        n ⊩ A type
        → n ⊩ A ~ (Tm.isect (fun _ => A)) type.
    Proof.
      move=> n A [R AR].
      exists R; split; auto.
      rewrite -Roll; apply TyF.isect.
      exists (fun _ => A), (fun _ => R).
      repeat split; auto.
      case: LocalClock; auto.
    Qed.

    Hint Resolve unit_formation univ_formation prod_formation isect_formation isect_irrelevance.
  End ClosedRules.

  Theorem test : ∃ n, n ⊩ (Tm.prod Tm.unit (Tm.univ 0)) type.
  Proof.
    eauto.
  Qed.

  Theorem test2 : exists n, n ⊩ (Tm.univ 0) ~ (Tm.isect (fun _ => Tm.univ 0)) type.
    eauto.
  Qed.

End Univ.