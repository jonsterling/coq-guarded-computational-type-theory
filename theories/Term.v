From gctt Require Import Axioms.
From gctt Require Import Var.
Require Import Unicode.Utf8.

Set Implicit Arguments.

Module Tm.
  Inductive t (Ψ : Ctx) :=
  | var : Var Ψ -> t Ψ
  | fst : t Ψ -> t Ψ
  | snd : t Ψ → t Ψ
  | unit : t Ψ
  | bool : t Ψ
  | ax : t Ψ
  | tt : t Ψ
  | ff : t Ψ
  | prod : t Ψ -> t Ψ -> t Ψ
  | arr : t Ψ -> t Ψ -> t Ψ
  | pair : t Ψ -> t Ψ -> t Ψ
  | ltr : CLK -> t Ψ -> t Ψ
  | isect : (CLK -> t Ψ) -> t Ψ
  | univ : nat -> t Ψ.

  Arguments unit [Ψ].
  Arguments bool [Ψ].
  Arguments ax [Ψ].
  Arguments tt [Ψ].
  Arguments ff [Ψ].
  Arguments univ [Ψ] i.

  Module Sub.
    Definition t (Ψ1 Ψ2 : Ctx) := Var Ψ1 → t Ψ2.

    Definition ren {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) : t Ψ1 Ψ2 :=
      fun x =>
        var (ρ x).
  End Sub.

  Program Fixpoint subst {Ψ1 Ψ2} (σ : Sub.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => σ i
    | fst e => fst (subst σ e)
    | snd e => snd (subst σ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst σ B)
    | arr A B => arr (subst σ A) (subst σ B)
    | pair e1 e2 => pair (subst σ e1) (subst σ e2)
    | ltr κ A => ltr κ (subst σ A)
    | isect A => isect (fun κ => subst σ (A κ))
    | univ i => univ i
    end.

  Definition map {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) : t Ψ1 → t Ψ2 :=
    subst (Sub.ren ρ).
End Tm.

Notation "e ⫽ σ" := (Tm.subst σ e) (at level 20, left associativity).

Reserved Notation "e 'val'" (at level 50).
Reserved Notation "e ⇓ e'" (at level 50).

Inductive is_val : Tm.t 0 → Prop :=
| val_bool : Tm.bool val
| val_unit : Tm.unit val
| val_prod : ∀ {e1 e2}, Tm.prod e1 e2 val
| val_arr : ∀ {e1 e2}, Tm.arr e1 e2 val
| val_ltr : ∀ {κ e}, Tm.ltr κ e val
| val_isect : ∀ {e}, Tm.isect e val
| val_univ : ∀ {i}, Tm.univ i val
| val_ax : Tm.ax val
| val_tt : Tm.tt val
| val_ff : Tm.ff val
| val_pair : ∀ {e1 e2}, Tm.pair e1 e2 val
where "v 'val'" := (is_val v).

Inductive eval : Tm.t 0 → Tm.t 0 → Prop :=
| eval_val :
    ∀ {v},
      v val
      → v ⇓ v

| eval_fst :
    ∀ {e e1 e2 v},
      e ⇓ Tm.pair e1 e2
      → e1 ⇓ v
      → Tm.fst e ⇓ v

| eval_snd :
    ∀ {e e1 e2 v},
      e ⇓ Tm.pair e1 e2
      → e2 ⇓ v
      → Tm.snd e ⇓ v

where "e ⇓ e'" := (eval e e').


Hint Constructors is_val.
Hint Constructors eval.


(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.