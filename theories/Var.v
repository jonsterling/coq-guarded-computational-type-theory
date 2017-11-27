Require Import Unicode.Utf8.
Require Import Vectors.Fin.
Require Import Coq.Program.Equality.

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

  Program Fixpoint weak {Ψ1} Ψ2 : t Ψ1 (Ψ2 + Ψ1) :=
    match Ψ2 with
    | 0 => fun x => x
    | S n => fun x => weak n (Fin.FS x)
    end.

End Ren.