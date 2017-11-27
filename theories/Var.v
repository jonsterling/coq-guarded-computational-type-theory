Require Import Unicode.Utf8.
Require Import Vectors.Fin.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Definition Ctx := nat.
Definition Var := Fin.t.

Module Ren.
  Definition t (ψ1 ψ2 : Ctx) : Type :=
    Var ψ1 → Var ψ2.

  Program Definition cong {ψ1 ψ2} (ρ : t ψ1 ψ2) : t (S ψ1) (S ψ2) :=
    fun x =>
      match x with
      | Fin.F1 => Fin.F1
      | Fin.FS y => Fin.FS (ρ y)
      end.

  Program Fixpoint weak {ψ1} ψ2 : t ψ1 (ψ2 + ψ1) :=
    match ψ2 with
    | 0 => fun x => x
    | S n => fun x => weak n (Fin.FS x)
    end.

End Ren.