From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Axioms.
From gctt Require Import Var.
From gctt Require Tactic.

Require Import Coq.Program.Equality.
Require Import Unicode.Utf8.

Module T := Tactic.
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
  | lam : t (S Ψ) → t Ψ
  | ltr : CLK -> t Ψ -> t Ψ
  | isect : (CLK -> t Ψ) -> t Ψ
  | univ : nat -> t Ψ.

  Arguments unit [Ψ].
  Arguments bool [Ψ].
  Arguments ax [Ψ].
  Arguments tt [Ψ].
  Arguments ff [Ψ].
  Arguments univ [Ψ] i.

  Program Fixpoint map {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => var (ρ i)
    | fst e => fst (map ρ e)
    | snd e => snd (map ρ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρ A) (map ρ B)
    | arr A B => arr (map ρ A) (map ρ B)
    | pair e1 e2 => pair (map ρ e1) (map ρ e2)
    | lam e => lam (map (Ren.cong ρ) e)
    | ltr κ A => ltr κ (map ρ A)
    | isect A => isect (fun κ => map ρ (A κ))
    | univ i => univ i
    end.

  Module Sub.
    Definition t (Ψ1 Ψ2 : Ctx) := Var Ψ1 → t Ψ2.

    Definition ren {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) : t Ψ1 Ψ2 :=
      fun x =>
        var (ρ x).

    Program Definition cong {Ψ1 Ψ2} (σ : t Ψ1 Ψ2) : t (S Ψ1) (S Ψ2) :=
      fun x =>
        match x with
        | Fin.F1 _ => var Fin.F1
        | Fin.FS _ y => map Fin.FS (σ y)
        end.

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
    | lam e => lam (subst (Sub.cong σ) e)
    | ltr κ A => ltr κ (subst σ A)
    | isect A => isect (fun κ => subst σ (A κ))
    | univ i => univ i
    end.
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
| val_lam : ∀ {e}, Tm.lam e val
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


Ltac destruct_evals :=
  repeat
    match goal with
    | H : ?A ⇓ ?B |- _ => dependent destruction H
    end.


Ltac destruct_eval :=
  match goal with
  | |- _ ⇓ _ → _ => let x := fresh in move=> x; dependent destruction x
  end.


(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.


Ltac evals_to_eq :=
  repeat
    match goal with
    | H1 : ?A ⇓ ?V1, H2 : ?A ⇓ ?V2 |- _ => simpl in H1, H2; have: V1 = V2; [apply: determinacy; eauto | move {H1 H2} => *]
    end.
