Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

From gctt Require Import Matrix.
From gctt Require Import Term.
From gctt Require Var.

Set Implicit Arguments.
Local Open Scope program_scope.

Inductive Prectx : Var.Ctx → Type :=
| nil : Prectx 0
| snoc : ∀ {Ψ}, Prectx Ψ → Tm.t Ψ → Prectx (S Ψ).

Notation "⋄" := nil.
Infix ";" := (snoc) (at level 50, left associativity).

Definition atomic_eq_ty (τ : matrix) (A B : Tm.t 0) :=
  ∃ R, τ (A, R) ∧ τ (B, R).

Definition atomic_eq_mem (τ : matrix) (A e1 e2 : Tm.t 0) :=
  ∃ R, τ (A, R) ∧ R (e1, e2).


Notation "τ ⊧ A ∼ B" := (atomic_eq_ty τ A B) (at level 10).
Notation "τ ⊧ A ∋ e1 ∼ e2" := (atomic_eq_mem τ A e1 e2) (at level 10).
Reserved Notation "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" (at level 10).

Program Fixpoint atomic_eq_env {Ψ} (τ : matrix) (Γ : Prectx Ψ) (γ1 γ2 : Tm.Sub.t Ψ 0) : Prop :=
  match Γ with
  | ⋄ => True
  | Γ ; A =>
    τ ⊧ Γ ∋⋆ (γ1 ∘ Fin.FS) ∼ (γ2 ∘ Fin.FS)
    ∧ τ ⊧ (Tm.subst (γ1 ∘ Fin.FS) A) ∼ (Tm.subst (γ2 ∘ Fin.FS) A)
  end
where "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" := (atomic_eq_env τ Γ γ1 γ2).


Reserved Notation "τ ⊧ Γ 'ctx'" (at level 10).
Reserved Notation "τ ⊧ Γ ≫ A ∼ B" (at level 10).

Program Fixpoint is_ctx {Ψ} (τ : matrix) (Γ : Prectx Ψ) : Prop :=
  match Γ with
  | ⋄ => True
  | Γ ; A => τ ⊧ Γ ctx ∧ τ ⊧ Γ ≫ A ∼ A
  end

with
seq_eq_ty {Ψ} (τ : matrix) (Γ : Prectx Ψ) (A B : Tm.t Ψ) : Prop :=
  ∀ γ1 γ2 : Tm.Sub.t Ψ 0,
    τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ (Tm.subst γ1 A) ∼ (Tm.subst γ2 B)
where "τ ⊧ Γ 'ctx'" := (is_ctx τ Γ)
and "τ ⊧ Γ ≫ A ∼ B" := (seq_eq_ty τ Γ A B).