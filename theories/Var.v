Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".


Require Import Unicode.Utf8 Vectors.Fin Program.Equality Program.Basics.
From ctt Require Tactic.
Module T := Tactic.

Set Implicit Arguments.

Definition Ctx := nat.
Definition Var := Fin.t.

Module Ren.
  Definition t (Ψ1 Ψ2 : Ctx) : Type :=
    Var Ψ1 → Var Ψ2.

  Program Definition cong {Ψ1 Ψ2} (ρ : t Ψ1 Ψ2) : t (S Ψ1) (S Ψ2) :=
    fun x =>
      match x with
      | Fin.F1 => Fin.F1
      | Fin.FS y => Fin.FS (ρ y)
      end.

  Theorem cong_id {Ψ} : @cong Ψ Ψ (fun x => x) = id.
  Proof.
    T.eqcd => x.
    dependent induction x; auto.
  Qed.

  Program Fixpoint weak {Ψ1} Ψ2 : t Ψ1 (Ψ2 + Ψ1) :=
    match Ψ2 with
    | 0 => fun x => x
    | S n => fun x => weak n (Fin.FS x)
    end.

  Program Definition inst0 {Ψ} (z : Var Ψ) : t (S Ψ) Ψ :=
    fun x =>
      match x with
      | Fin.F1 => z
      | Fin.FS y => y
      end.

End Ren.

Module Sub.
  Local Open Scope program_scope.

  Class syn_struct (𝒯 : Ctx → Type) : Type :=
    { var : ∀ {Ψ}, Var Ψ → 𝒯 Ψ;
      map : ∀ {Ψ1 Ψ2}, Ren.t Ψ1 Ψ2 → 𝒯 Ψ1 → 𝒯 Ψ2;
      map_id : ∀ {Ψ} (M : 𝒯 Ψ), map id M = M
    }.

  Section Sub.
    Context `{𝒯 : Ctx → Type}.
    Context `{𝔐 : syn_struct 𝒯}.

    Definition t (Ψ1 Ψ2 : Ctx) := Var Ψ1 → 𝒯 Ψ2.

    Program Definition ren {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) : t Ψ1 Ψ2 :=
      fun x =>
        var (ρ x).

    Program Definition cong {Ψ1 Ψ2} (σ : t Ψ1 Ψ2) : t (S Ψ1) (S Ψ2) :=
      fun x =>
        match x with
        | Fin.F1 => var Fin.F1
        | Fin.FS y => map Fin.FS (σ y)
        end.

    Program Definition inst0 {Ψ} (M : 𝒯 Ψ) : t (S Ψ) Ψ :=
      fun x =>
        match x with
        | Fin.F1 => M
        | Fin.FS y => @var _ 𝔐 _ y
        end.

    Theorem cong_coh {Ψ1 Ψ2 Ψ3} (ρ : Ren.t Ψ1 Ψ2) (σ : Sub.t Ψ2 Ψ3) :
      Sub.cong (σ ∘ ρ) = Sub.cong σ ∘ Ren.cong ρ.
    Proof.
      T.eqcd => x.
      dependent destruction x; auto.
    Qed.

    Theorem cong_coh_ptwise {Ψ1 Ψ2 Ψ3} (ρ : Ren.t Ψ1 Ψ2) (σ : Sub.t Ψ2 Ψ3) :
      ∀ x,
        Sub.cong (σ ∘ ρ) x = Sub.cong σ (Ren.cong ρ x).
    Proof.
      move=> x.
      dependent destruction x; auto.
    Qed.
  End Sub.
End Sub.

Delimit Scope ren_scope with ren.
Notation "^ n" := (Ren.weak n) (at level 50) : ren_scope.
