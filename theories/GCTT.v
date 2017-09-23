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

Definition based_matrix_functional (σ : matrix) (A : Tm.t 0) : Prop :=
  ∀ R1 R2,
    σ (A, R1)
    → σ (A, R2)
    → R1 = R2.

Definition matrix_functional (σ : matrix) : Prop :=
  ∀ A, based_matrix_functional σ A.


Axiom propositional_extensionality :
  ∀ (P Q : Prop),
    (P ↔ Q)
    -> P = Q.

Theorem binrel_extensionality : 
  ∀ (T1 T2 : Type) (R1 R2 : T1 * T2 → Prop),
    (∀ x y, R1 (x, y) ↔ R2 (x, y))
    → R1 = R2.
Proof.
  move=> T1 T2 R1 R2 F.
  apply: functional_extensionality.
  move=> [x y].
  apply: propositional_extensionality.
  eauto.
Qed.


Theorem CTyF_Roll:
  ∀ σ,
    TyF.t σ (CTyF σ)
    = CTyF σ.
Proof.
  move=> σ.
  apply: binrel_extensionality => [A R].
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


Theorem CTyF_ind :
  ∀ (σ : matrix) (X : Tm.t 0 * behavior) (P : Prop),
    CTyF σ X
    → (σ X → P)
    → (Close.unit (CTyF σ) X → P)
    → (Close.bool (CTyF σ) X → P)
    → (Close.prod (CTyF σ) X → P)
    → (Close.isect (CTyF σ) X → P)
    → (Close.later (CTyF σ) X → P)
    → P.
Proof.
  move=> σ [A R] P C init unit bool prod isect later.
  rewrite -CTyF_Roll in C.
  case: C; auto.
Qed.


Definition Empty : matrix :=
  fun _ => False.

Ltac destruct_CTyF :=
  repeat match goal with
  | T : CTyF _ _ |- _ =>
    apply: (CTyF_ind T); clear T
  end.

Ltac destruct_evals :=
  repeat
    match goal with
      | H : ?A ⇓ ?B |- _ => dependent destruction H
    end.

Ltac noconfusion :=
  try by [contradiction];
  intros; simpl in *;
  destruct_conjs;
  destruct_evals.


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

Ltac use_matrix_functionality_ih := 
  match goal with
  | IH : ∀ R1 R2 : behavior, CTyF _ (?A, R1) → CTyF _ (?A, R2) → R1 = R2, U : ?R' (?e1, ?e2) |- ?R (?e1, ?e2) =>
      by rewrite (IH R R'); auto
  end.

Theorem CTyF_Empty_functional : matrix_functional (CTyF Empty).
Proof.
  move=> A; elim: A;
  unfold based_matrix_functional; intros;
  destruct_CTyF; intros;
  noconfusion;
  apply: binrel_extensionality; intros;
  split; intros;
  
  repeat
    match goal with
    | H : ∀ (e1 e2 : Tm.t 0), ?P |- ?R (?e1, ?e2) => specialize (H e1 e2); destruct H
    end;

  first by [firstorder];
  first by [firstorder]; 

  backthruhyp; intros;
  specialize_hyps;
  destruct_conjs;
  repeat esplit; eauto;
  use_matrix_functionality_ih.
Qed.

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

  Theorem CTyF_idempotent : CTyF (CTyF Empty) = CTyF Empty.
  Proof.
    apply: functional_extensionality.
    move=> [A R].
    move: R.
    elim: A; intros;
    apply: propositional_extensionality;
    split => AR; destruct_CTyF; noconfusion; auto;
    rewrite -CTyF_Roll;

    match goal with
    | |- TyF.t _ _ (?A, _) => 
      match A with
      | Tm.unit =>
        apply: TyF.unit;
        split; auto
      | Tm.prod _ _ =>
        apply: TyF.prod;
        do 4 esplit; repeat split; eauto
      | Tm.isect _ =>
        apply: TyF.isect;
        do 2 esplit; repeat split; eauto;
        intros
      end
    end;

    repeat match goal with 
    | H1 : (∀ R : behavior, ?A = ?B), H2 : CTyF _ _ |- _ => (rewrite H1 in H2 || rewrite -H1 in H2); clear H1
    | H : ∀ e1 e2 : Tm.t 0, ?P |- _ => specialize (H e1 e2); destruct H
    | κ : CLK, H : ∀ κ : CLK, ?P |- _ => specialize (H κ)
    end;
    eauto.
  Qed.

  Theorem Nuprl_functional : ∀ i, matrix_functional (Nuprl i).
  Proof.
    case.
    + move=> A.
      rewrite /Nuprl /Spine //=.
      unfold based_matrix_functional; intros.
      rewrite CTyF_idempotent in H, H0.
      apply: CTyF_Empty_functional; eauto.
    + move=> n A;
      elim: A;
      unfold based_matrix_functional, Nuprl; intros;
      destruct_CTyF => C1 C2;
      noconfusion;
      apply: binrel_extensionality => e1 e2;
      repeat
        match goal with
        | H : ∀ (e1 e2 : Tm.t 0), ?P |- _ => specialize (H e1 e2); destruct H
        end;

      intros;
      split; intros;
      backthruhyp;
      specialize_hyps; eauto.

      ++ destruct_conjs;
         repeat esplit; eauto;
         use_matrix_functionality_ih.

      ++ destruct_conjs;
         repeat esplit; eauto;
         use_matrix_functionality_ih.

      ++ intros.
         specialize_hyps.
         use_matrix_functionality_ih.

      ++ intros.
         specialize_hyps.
         use_matrix_functionality_ih.
  Qed.

  Definition Nuprlω : matrix :=
    fun X => ∃ n, Nuprl n X.


  Notation "n ⊩ A type" := (∃ R, Nuprl n (A, R)) (at level 0, A at level 0, only parsing).
  Notation "n ⊩ A ∼ B type" := (∃ R, Nuprl n (A, R) ∧ Nuprl n (B, R)) (at level 0, A at level 0, B at level 0, only parsing).
  Notation "ω⊩ A type" := (∃ R, Nuprlω (A, R)) (at level 0, A at level 0, only parsing).

  Theorem Roll {i : nat} : TyF.t (Spine i) (Nuprl i) = Nuprl i.
  Proof.
    apply: binrel_extensionality => A R.
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
      apply: Nuprl_functional; eauto.
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
        → n ⊩ A ∼ (Tm.isect (fun _ => A)) type.
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

  Theorem test2 : exists n, n ⊩ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)) type.
    eauto.
  Qed.

End Univ.
