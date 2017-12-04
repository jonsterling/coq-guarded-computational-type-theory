Require Import Unicode.Utf8.
Require Import Vectors.Fin.
Require Import Coq.Program.Equality.
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