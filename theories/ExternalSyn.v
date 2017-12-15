From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Vectors.Fin.
Require Import Coq.omega.Omega.

From gctt Require Import Term Axioms Var Sequent Tower.
From gctt Require Tactic.
Module T := Tactic.

Set Implicit Arguments.

Module ETm.
  Inductive t (Λ Ψ : nat) :=
  | var : Var Ψ -> t Λ Ψ
  | fst : t Λ Ψ -> t Λ Ψ
  | snd : t Λ Ψ → t Λ Ψ
  | unit : t Λ Ψ
  | bool : t Λ Ψ
  | ax : t Λ Ψ
  | tt : t Λ Ψ
  | ff : t Λ Ψ
  | prod : t Λ Ψ -> t Λ Ψ -> t Λ Ψ
  | arr : t Λ Ψ -> t Λ Ψ -> t Λ Ψ
  | pair : t Λ Ψ -> t Λ Ψ -> t Λ Ψ
  | ltr : Var Λ → t Λ Ψ -> t Λ Ψ
  | isect : t (S Λ) Ψ -> t Λ Ψ
  | univ : nat -> t Λ Ψ.

  Arguments unit [Λ Ψ].
  Arguments bool [Λ Ψ].
  Arguments ax [Λ Ψ].
  Arguments tt [Λ Ψ].
  Arguments ff [Λ Ψ].
  Arguments univ [Λ Ψ] i.

  Program Fixpoint map `(ρΛ : Ren.t Λ1 Λ2) `(ρΨ : Ren.t Ψ1 Ψ2) (e : t Λ1 Ψ1) : t Λ2 Ψ2 :=
    match e with
    | var i => var _ (ρΨ i)
    | fst e => fst (map ρΛ ρΨ e)
    | snd e => snd (map ρΛ ρΨ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρΛ ρΨ A) (map ρΛ ρΨ B)
    | arr A B => arr (map ρΛ ρΨ A) (map ρΛ ρΨ B)
    | pair e1 e2 => pair (map ρΛ ρΨ e1) (map ρΛ ρΨ e2)
    | ltr k A => ltr (ρΛ k) (map ρΛ ρΨ A)
    | isect A => isect (map (Ren.cong ρΛ) ρΨ A)
    | univ i => univ i
    end.

  Definition mapv {Λ} `(ρΨ : Ren.t Ψ1 Ψ2) : t Λ Ψ1 → t Λ Ψ2 :=
    map (λ x, x) ρΨ.

  Definition mapk {Λ1 Λ2 Ψ} (ρ : Ren.t Λ1 Λ2) : t Λ1 Ψ → t Λ2 Ψ :=
    map ρ (λ x, x).
End ETm.

Notation "e .^ n" := (ETm.mapv (Ren.weak n) e) (at level 50).

Module ECtx.
  Inductive t (Λ : Var.Ctx) : Var.Ctx → Type :=
  | nil : t Λ 0
  | snoc : ∀ {Ψ}, t Λ Ψ → ETm.t Λ Ψ → t Λ (S Ψ).

  Arguments nil [Λ].
End ECtx.

Notation "`⋄" := ECtx.nil.
Infix "`;" := (ECtx.snoc) (at level 50, left associativity).

Module EJdg.
  Inductive t Λ :=
  | eq_ty : ∀ {Ψ}, ECtx.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ
  | eq_mem : ∀ {Ψ}, ECtx.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ
  | conv : ∀ {Ψ}, ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ.
End EJdg.

Notation "⌊ Λ ∣ Γ ≫ A ≐ B ⌋" := (@EJdg.eq_ty Λ _ Γ A B).
Notation "⌊ Λ ∣ Γ ≫ A ∋ e1 ≐ e2 ⌋" := (@EJdg.eq_mem Λ _ Γ A e1 e2).
Notation "⌊ Λ ∣ Ψ ⊢ e1 ≃ e2 ⌋" := (@EJdg.conv Λ Ψ e1 e2).

Example example_judgment :=  ⌊ 1 ∣ `⋄ ≫ ETm.ltr Fin.F1 ETm.unit ≐ ETm.ltr Fin.F1 ETm.unit ⌋.

Module Env.
  Definition t Λ := Var Λ → CLK.

  Program Definition cons {Λ} (κ : CLK) (σ : t Λ) : t (S Λ) :=
    λ x,
      match x with
      | Fin.F1 _ => κ
      | Fin.FS _ x => σ x
      end.
End Env.

Notation "κ ∷ σ" := (Env.cons κ σ) (at level 30).

Reserved Notation "T⟦ e ⟧ κs" (at level 50).
Reserved Notation "Γ⟦ Γ ⟧ κs" (at level 50).

Fixpoint interp_tm `(e : ETm.t Λ Ψ) (κs : Env.t Λ) : Tm.t Ψ :=
  match e with
  | ETm.var i => Tm.var i
  | ETm.fst e => Tm.fst (T⟦e⟧ κs)
  | ETm.snd e => Tm.snd (T⟦e⟧ κs)
  | ETm.unit => Tm.unit
  | ETm.bool => Tm.bool
  | ETm.ax => Tm.ax
  | ETm.tt => Tm.tt
  | ETm.ff => Tm.ff
  | ETm.prod A B => Tm.prod (T⟦A⟧ κs) (T⟦B⟧ κs)
  | ETm.arr A B => Tm.arr (T⟦A⟧ κs) (T⟦B⟧ κs)
  | ETm.pair A B => Tm.pair (T⟦A⟧ κs) (T⟦B⟧ κs)
  | ETm.ltr r A => Tm.ltr (κs r) (T⟦A⟧ κs)
  | ETm.isect A => Tm.isect (λ κ, T⟦A⟧ (κ ∷ κs))
  | ETm.univ i => Tm.univ i
  end
where "T⟦ e ⟧ κs" := (interp_tm e κs).

Program Fixpoint interp_ctx `(Γ : ECtx.t Λ Ψ) (κs : Env.t Λ) : Prectx Ψ :=
  match Γ with
  | `⋄ => ⋄
  | Γ `; A => Γ⟦ Γ ⟧ κs ; T⟦ A ⟧ κs
  end
where "Γ⟦ Γ ⟧ κs" := (interp_ctx Γ κs).

Definition interp_jdg `(J : EJdg.t Λ) : Prop :=
  ∀ (κs : Env.t Λ),
    match J with
    | ⌊ _ ∣ Γ ≫ A ≐ B ⌋ =>
      τω ⊧ Γ⟦ Γ ⟧ κs ctx
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ T⟦ A ⟧ κs ∼ T⟦ B ⟧ κs
    | ⌊ _ ∣ Γ ≫ A ∋ e1 ≐ e2 ⌋ =>
      τω ⊧ Γ⟦ Γ ⟧ κs ctx
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ (T⟦ A ⟧ κs) ∼ (T⟦ A ⟧ κs)
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ T⟦ A ⟧ κs ∋ T⟦ e1 ⟧ κs ∼ T⟦ e2 ⟧ κs
    | ⌊ _ ∣ Ψ ⊢ e1 ≃ e2 ⌋ =>
      (T⟦ e1 ⟧ κs) ≈ (T⟦ e2 ⟧ κs)
    end.

Notation "J⟦ J ⟧" := (interp_jdg J) (at level 50).

Ltac rewrite_all_hyps :=
  repeat
    match goal with
    | x : _ |- _ => rewrite -x
    end.

Local Open Scope program_scope.

Theorem interp_tm_clk_naturality {Λ1 Λ2 Ψ} :
  ∀ (e : ETm.t Λ1 Ψ) (ρ : Ren.t Λ1 Λ2) (κs : Env.t Λ2),
    T⟦ e ⟧ κs ∘ ρ = T⟦ ETm.mapk ρ e ⟧ κs.
Proof.
  move=> e; move: Λ2.
  elim e => *; eauto; simpl; try by [rewrite_all_hyps].
  + f_equal; T.eqcd => ?.
    rewrite_all_hyps.
    f_equal; T.eqcd => i.
    by dependent induction i.
Qed.

Theorem interp_tm_var_naturality {Λ Ψ0 Ψ1 Ψ2} (e : ETm.t Λ Ψ0) (γ : Tm.Sub.t Ψ1 Ψ2) ρ κs :
  (T⟦ e ⟧ κs) ⫽ (γ ∘ ρ) = (T⟦ ETm.mapv ρ e ⟧ κs) ⫽ γ.
Proof.
  induction e; eauto; simpl; try by [rewrite_all_hyps].
  f_equal; T.eqcd => ?.
  rewrite IHe.
  by rewrite Ren.cong_id.
Qed.
