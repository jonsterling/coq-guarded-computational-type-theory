Require Import Unicode.Utf8 Vectors.Fin Program.Equality.
From gctt Require Tactic.
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
      | Fin.F1 _ => Fin.F1
      | Fin.FS _ y => Fin.FS (ρ y)
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

End Ren.

Module Sub.
  Class syn_struct (𝒯 : Ctx → Type) : Type :=
    { var : ∀ {Ψ}, Var Ψ → 𝒯 Ψ;
      map : ∀ {Ψ1 Ψ2}, Ren.t Ψ1 Ψ2 → 𝒯 Ψ1 → 𝒯 Ψ2
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
        | Fin.F1 _ => var Fin.F1
        | Fin.FS _ y => map Fin.FS (σ y)
        end.

    Program Definition inst0 {Ψ} (e : 𝒯 Ψ) : t (S Ψ) Ψ :=
      fun x =>
        match x with
        | Fin.F1 _ => e
        | Fin.FS _ y => @var _ 𝔐 _ y
        end.
  End Sub.
End Sub.

Delimit Scope ren_scope with ren.
Notation "^ n" := (Ren.weak n) (at level 50) : ren_scope.
