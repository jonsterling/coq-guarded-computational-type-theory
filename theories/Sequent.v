From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8 Program.Equality Program.Basics.

From gctt Require Import Notation TypeSystem Term Axioms.
From gctt Require Var.

(*Set Implicit Arguments. *)
Local Open Scope program_scope.

Inductive Prectx : Var.Ctx → Type :=
| nil : Prectx 0
| snoc : ∀ {Ψ}, Prectx Ψ → Tm.t Ψ → Prectx (S Ψ).

Delimit Scope ctx_scope with ictx.
Arguments snoc [Ψ] Γ%ictx A%tm.

Notation "⋄" := nil : ctx_scope.
Infix ";" := (snoc) (at level 50, left associativity) : ctx_scope.


Definition atomic_eq_ty (τ : cts) (A B : Tm.t 0) :=
  ∃ R, τ (A, R) ∧ τ (B, R).

Definition atomic_eq_mem (τ : cts) (A e1 e2 : Tm.t 0) :=
  ∃ R, τ (A, R) ∧ R (e1, e2).

Arguments atomic_eq_ty τ A%tm B%tm.
Arguments atomic_eq_mem τ A%tm e1%tm e2%tm.

Notation "τ ⊧ A ∼ B" := (atomic_eq_ty τ A B) (at level 10).
Notation "τ ⊧ A ∋ e1 ∼ e2" := (atomic_eq_mem τ A e1 e2) (at level 10).
Reserved Notation "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" (at level 10).

Program Fixpoint atomic_eq_env {Ψ} τ Γ (γ1 γ2 : Tm.Sub.t Ψ 0) : Ω :=
  match Γ with
  | ⋄%ictx => ⊤
  | (Γ ; A)%ictx =>
    τ ⊧ Γ ∋⋆ (γ1 ∘ Fin.FS) ∼ (γ2 ∘ Fin.FS)
    ∧ τ ⊧ (A ⫽ (γ1 ∘ Fin.FS)) ∋ (γ1 Fin.F1) ∼ (γ2 Fin.F1)
  end
where "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" := (atomic_eq_env τ Γ%ictx γ1 γ2).

Solve All Obligations with auto.

Definition seq_eq_ty {Ψ} τ Γ (A B : Tm.t Ψ) : Ω :=
  ∀ γ1 γ2,
    τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ (A ⫽ γ1) ∼ (B ⫽ γ2).

Definition seq_eq_mem {Ψ} τ Γ (A e1 e2 : Tm.t Ψ) :=
  ∀ γ1 γ2,
    τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ (A ⫽ γ1) ∋ (e1 ⫽ γ1) ∼ (e2 ⫽ γ2).

Arguments seq_eq_ty [Ψ] τ Γ%ictx A%tm B%tm.
Arguments seq_eq_mem [Ψ] τ Γ%ictx A%tm e1%tm e2%tm.

Reserved Notation "τ ⊧ Γ 'ctx'" (at level 10).
Notation "τ ⊧ Γ ≫ A ∼ B" := (seq_eq_ty τ Γ A B) (at level 10).
Notation "τ ⊧ Γ ≫ A ∋ e1 ∼ e2" := (seq_eq_mem τ Γ A e1 e2) (at level 10).

Program Fixpoint is_ctx {Ψ} (τ : cts) (Γ : Prectx Ψ) : Ω :=
  match Γ with
  | ⋄%ictx => ⊤
  | (Γ; A)%ictx => τ ⊧ Γ ctx ∧ τ ⊧ Γ ≫ A ∼ A
  end
where "τ ⊧ Γ 'ctx'" := (is_ctx τ Γ).

Arguments is_ctx [Ψ] τ Γ%ictx.


Definition open_approx {Ψ} (e1 e2 : Tm.t Ψ) : Ω :=
  ∀ γ v, e1 ⫽ γ ⇓ v → e2 ⫽ γ ⇓ v.

Definition open_equiv {Ψ} (e1 e2 : Tm.t Ψ) : Ω :=
  ∀ γ v, e1 ⫽ γ ⇓ v ↔ e2 ⫽ γ ⇓ v.

Arguments open_approx [Ψ] e1%tm e2%tm.
Arguments open_equiv [Ψ] e1%tm e2%tm.

Infix "≼" := open_approx (at level 30).
Infix "≈" := open_equiv (at level 30).
