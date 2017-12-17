Require Import Unicode.Utf8 Program.
From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Axioms Var.
From gctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.

Module Tm.
  Inductive t (Ψ : Ctx) :=
  | var : Var Ψ -> t Ψ
  | fst : t Ψ -> t Ψ
  | snd : t Ψ → t Ψ
  | app : t Ψ → t Ψ → t Ψ
  | unit : t Ψ
  | bool : t Ψ
  | ax : t Ψ
  | tt : t Ψ
  | ff : t Ψ
  | prod : t Ψ -> t Ψ -> t Ψ
  | arr : t Ψ -> t Ψ -> t Ψ
  | pair : t Ψ -> t Ψ -> t Ψ
  | lam : t (S Ψ) → t Ψ
  | ltr : 𝕂 -> t Ψ -> t Ψ
  | isect : (𝕂 → t Ψ) → t Ψ
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
    | app e1 e2 => app (map ρ e1) (map ρ e2)
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
    | app e1 e2 => app (subst σ e1) (subst σ e2)
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

Delimit Scope tm_scope with tm.

Notation "e ⫽ σ" := (Tm.subst σ e%tm) (at level 20, left associativity).

Notation "@0" := (Tm.var _ Fin.F1) : tm_scope.
Notation "@1" := (Tm.var _ (Fin.FS Fin.F1)) : tm_scope.
Notation "▶[ κ ] A" := (Tm.ltr κ A%tm) (at level 50) : tm_scope.
Notation "'𝟚'" := Tm.bool : tm_scope.
Notation "'𝟙'" := Tm.unit : tm_scope.
Notation "★" := Tm.ax : tm_scope.
Notation "e .1" := (Tm.fst e%tm) (at level 50) : tm_scope.
Notation "e .2" := (Tm.snd e%tm) (at level 50) : tm_scope.
Infix "×" := Tm.prod : tm_scope.
Infix "→" := Tm.arr : tm_scope.
Notation "⋂[ κ ] A" := (Tm.isect (fun κ => A%tm)) (at level 50) : tm_scope.
Notation "⋂ A" := (Tm.isect A) (at level 50) : tm_scope.
Notation "𝕌[ i ] " := (Tm.univ i%nat) : tm_scope.
Notation "⟨ e1 , e2 ⟩" := (Tm.pair e1%tm e2%tm) : tm_scope.
Notation "e1 ⋅ e2" := (Tm.app e1%tm e2%tm) (at level 50) : tm_scope.
Notation "'𝛌' e" := (Tm.lam e%tm) (at level 50) : tm_scope.

Reserved Notation "e 'val'" (at level 50).
Reserved Notation "e ⇓ e'" (at level 50).

Inductive is_val : Tm.t 0 → Ω :=
| val_bool : 𝟚 val
| val_unit : 𝟙 val
| val_prod : ∀ {e1 e2}, (e1 × e2) val
| val_arr : ∀ {e1 e2}, (e1 → e2) val
| val_ltr : ∀ {κ e}, ▶[κ] e val
| val_isect : ∀ {e}, ⋂ e val
| val_univ : ∀ {i}, 𝕌[i] val
| val_ax : ★ val
| val_tt : Tm.tt val
| val_ff : Tm.ff val
| val_pair : ∀ {e1 e2}, ⟨e1, e2⟩ val
| val_lam : ∀ {e}, (𝛌 e) val
where "v 'val'" := (is_val v%tm).

Inductive eval : Tm.t 0 → Tm.t 0 → Ω :=
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
      e ⇓ ⟨e1, e2⟩
      → e2 ⇓ v
      → e.2 ⇓ v

| eval_app :
    ∀ {e1 e1' e2},
      e1 ⇓ (𝛌 e1')
      → e1 ⋅ e2 ⇓ Tm.subst (fun _ => e2) e1'

where "e ⇓ e'" := (eval e%tm e'%tm).


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
    | H1 : ?A ⇓ ?V1, H2 : ?A ⇓ ?V2 |- _ =>
      simpl in H1, H2;
      have: V1 = V2;
      [ apply: determinacy; eauto
      | move {H1 H2} => *
      ]
    end.


Definition closed_approx (e1 e2 : Tm.t 0) : Ω :=
  ∀ v, e1 ⇓ v → e2 ⇓ v.

Definition closed_equiv (e1 e2 : Tm.t 0) : Ω :=
  ∀ v, e1 ⇓ v ↔ e2 ⇓ v.

Arguments closed_approx e1%tm e2%tm.
Arguments closed_equiv e1%tm e2%tm.

Infix "≼₀" := closed_approx (at level 30).
Infix "≈₀" := closed_equiv (at level 30).

Theorem closed_approx_refl : ∀ e, e ≼₀ e.
Proof.
  compute.
  auto.
Qed.

Hint Resolve closed_approx_refl.