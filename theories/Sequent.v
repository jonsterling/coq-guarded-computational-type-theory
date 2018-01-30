Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8 Program.Equality Program.Basics.

From gctt Require Import Notation TypeSystem Program OpSem Axioms.
From gctt Require Var.

(*Set Implicit Arguments. *)
Local Open Scope program_scope.

Inductive Prectx : Var.Ctx → Type :=
| nil : Prectx 0
| snoc : ∀ {Ψ}, Prectx Ψ → Prog.t Ψ → Prectx (S Ψ).

Delimit Scope ctx_scope with ictx.
Arguments snoc [Ψ] Γ%ictx A%prog.

Notation "⋄" := nil : ctx_scope.
Infix "∙" := (snoc) (at level 50, left associativity) : ctx_scope.


Definition atomic_eq_ty (τ : cts) (A B : Prog.t 0) :=
  ∃ R, τ (A, R) ∧ τ (B, R).

Definition atomic_eq_mem (τ : cts) (A M1 M2 : Prog.t 0) :=
  ∃ R, τ (A, R) ∧ R (M1, M2).

Arguments atomic_eq_ty τ A%prog B%prog.
Arguments atomic_eq_mem τ A%prog M1%prog M2%prog.

Notation "τ ⊧ A ∼ B" := (atomic_eq_ty τ A%prog B%prog) (at level 10).
Notation "τ ⊧ A ∋ M1 ∼ M2" := (atomic_eq_mem τ A%prog M1%prog M2%prog) (at level 10).
Reserved Notation "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" (at level 10).

Program Fixpoint atomic_eq_env {Ψ} τ Γ (γ1 γ2 : Var.Sub.t Ψ 0) : Ω :=
  match Γ with
  | ⋄%ictx => ⊤
  | (Γ ∙ A)%ictx =>
    τ ⊧ Γ ∋⋆ (γ1 ∘ Fin.FS) ∼ (γ2 ∘ Fin.FS)
    ∧ τ ⊧ (A ⫽ (γ1 ∘ Fin.FS)) ∋ (γ1 Fin.F1) ∼ (γ2 Fin.F1)
  end
where "τ ⊧ Γ ∋⋆ γ1 ∼ γ2" := (atomic_eq_env τ Γ%ictx γ1 γ2).

Solve All Obligations with auto.

Definition seq_eq_ty {Ψ} τ Γ (A B : Prog.t Ψ) : Ω :=
  ∀ γ1 γ2,
    τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ (A ⫽ γ1) ∼ (B ⫽ γ2).

Definition seq_eq_mem {Ψ} τ Γ (A M1 M2 : Prog.t Ψ) :=
  ∀ γ1 γ2,
    τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ (A ⫽ γ1) ∋ (M1 ⫽ γ1) ∼ (M2 ⫽ γ2).

Arguments seq_eq_ty [Ψ] τ Γ%ictx A%prog B%prog.
Arguments seq_eq_mem [Ψ] τ Γ%ictx A%prog M1%prog M2%prog.

Reserved Notation "τ ⊧ Γ 'ctx'" (at level 10).
Notation "τ ⊧ Γ ≫ A ∼ B" := (seq_eq_ty τ Γ%ictx A%prog B%prog) (at level 10).
Notation "τ ⊧ Γ ≫ A ∋ M1 ∼ M2" := (seq_eq_mem τ Γ%ictx A%prog M1%prog M2%prog) (at level 10).

Program Fixpoint is_ctx {Ψ} (τ : cts) (Γ : Prectx Ψ) : Ω :=
  match Γ with
  | ⋄%ictx => ⊤
  | (Γ∙A)%ictx => τ ⊧ Γ ctx ∧ τ ⊧ Γ ≫ A ∼ A
  end
where "τ ⊧ Γ 'ctx'" := (is_ctx τ Γ%ictx).

Arguments is_ctx [Ψ] τ Γ%ictx.


Definition open_approx {Ψ} (M1 M2 : Prog.t Ψ) : Ω :=
  ∀ γ V, M1 ⫽ γ ⇓ V → M2 ⫽ γ ⇓ V.

Definition open_equiv {Ψ} (M1 M2 : Prog.t Ψ) : Ω :=
  ∀ γ V, M1 ⫽ γ ⇓ V ↔ M2 ⫽ γ ⇓ V.

Arguments open_approx [Ψ] M1%prog M2%prog.
Arguments open_equiv [Ψ] M1%prog M2%prog.

Notation "M0 ≼ M1" := (open_approx M0%prog M1%prog) (at level 30) : type_scope.
Notation "M0 ≈ M1" := (open_equiv M0%prog M1%prog) (at level 30) : type_scope.

Theorem open_equiv_closed : @open_equiv 0 = closed_equiv.
Proof.
  T.eqcd => M0.
  T.eqcd => M1.
  apply: propositional_extensionality.
  split => 𝒟.
  - move=> V.
    move: (𝒟 (@Prog.var 0) V).
    by rewrite ! Prog.subst_closed.
  - move=> γ V.
    move: (𝒟 V).
    by rewrite ! Prog.subst_closed.
Qed.