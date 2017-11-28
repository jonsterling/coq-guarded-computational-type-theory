From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Vectors.Fin.

From gctt Require Import Term.
From gctt Require Import Axioms.
From gctt Require Import Var.
From gctt Require Import Sequent.
From gctt Require Import Tower.
From gctt Require Tactic.

Module T := Tactic.


Set Implicit Arguments.

Module FTm.
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

  Program Fixpoint map {Λ1 Λ2 Ψ1 Ψ2} (ρΛ : Ren.t Λ1 Λ2) (ρΨ : Ren.t Ψ1 Ψ2) (e : t Λ1 Ψ1) : t Λ2 Ψ2 :=
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

  Definition mapk {Λ1 Λ2 Ψ} (ρ : Ren.t Λ1 Λ2) : t Λ1 Ψ → t Λ2 Ψ :=
    map ρ (fun x => x).
End FTm.

Module FCtx.
  Inductive t (Λ : Var.Ctx) : Var.Ctx → Type :=
  | nil : t Λ 0
  | snoc : ∀ {Ψ}, t Λ Ψ → FTm.t Λ Ψ → t Λ (S Ψ).

  Arguments nil [Λ].
End FCtx.

Notation "`⋄" := FCtx.nil.
Infix "`;" := (FCtx.snoc) (at level 50, left associativity).

Module FJdg.
  Inductive t Λ :=
  | eq_ty : ∀ {Ψ}, FCtx.t Λ Ψ → FTm.t Λ Ψ → FTm.t Λ Ψ → t Λ
  | eq_mem : ∀ {Ψ}, FCtx.t Λ Ψ → FTm.t Λ Ψ → FTm.t Λ Ψ → FTm.t Λ Ψ → t Λ.
End FJdg.

Notation "⌊ Λ ∣ Γ ≫ A ≐ B ⌋" := (@FJdg.eq_ty Λ _ Γ A B).
Notation "⌊ Λ ∣ Γ ≫ A ∋ e1 ≐ e2 ⌋" := (@FJdg.eq_mem Λ _ Γ A e1 e2).


Example example_judgment :=  ⌊ 1 ∣ `⋄ ≫ FTm.ltr Fin.F1 FTm.unit ≐ FTm.ltr Fin.F1 FTm.unit ⌋.

Module Env.
  Definition t Λ := Var Λ → CLK.

  Program Definition cons {Λ} (κ : CLK) (σ : t Λ) : t (S Λ) :=
    fun x =>
      match x with
      | Fin.F1 _ => κ
      | Fin.FS _ x => σ x
      end.
End Env.

Notation "κ ∷ σ" := (Env.cons κ σ) (at level 30).

Reserved Notation "T⟦ e ⟧ κs" (at level 50).
Reserved Notation "Γ⟦ Γ ⟧ κs" (at level 50).

Fixpoint interp_tm {Λ Ψ} (e : FTm.t Λ Ψ) (κs : Env.t Λ) : Tm.t Ψ :=
  match e with
  | FTm.var i => Tm.var i
  | FTm.fst e => Tm.fst (T⟦e⟧ κs)
  | FTm.snd e => Tm.snd (T⟦e⟧ κs)
  | FTm.unit => Tm.unit
  | FTm.bool => Tm.bool
  | FTm.ax => Tm.ax
  | FTm.tt => Tm.tt
  | FTm.ff => Tm.ff
  | FTm.prod A B => Tm.prod (T⟦A⟧ κs) (T⟦B⟧ κs)
  | FTm.arr A B => Tm.arr (T⟦A⟧ κs) (T⟦B⟧ κs)
  | FTm.pair A B => Tm.pair (T⟦A⟧ κs) (T⟦B⟧ κs)
  | FTm.ltr r A => Tm.ltr (κs r) (T⟦A⟧ κs)
  | FTm.isect A => Tm.isect (fun κ => T⟦A⟧ (κ ∷ κs))
  | FTm.univ i => Tm.univ i
  end
where "T⟦ e ⟧ κs" := (interp_tm e κs).

Program Fixpoint interp_ctx {Λ Ψ} (Γ : FCtx.t Λ Ψ) (κs : Env.t Λ) : Prectx Ψ :=
  match Γ with
  | `⋄ => ⋄
  | Γ `; A => Γ⟦ Γ ⟧ κs ; T⟦ A ⟧ κs
  end
where "Γ⟦ Γ ⟧ κs" := (interp_ctx Γ κs).

Definition interp_jdg {Λ} (J : FJdg.t Λ) : Prop :=
  ∀ (κs : Env.t Λ),
    match J with
    | ⌊ _ ∣ Γ ≫ A ≐ B ⌋ =>
      τω ⊧ Γ⟦ Γ ⟧ κs ctx
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ T⟦ A ⟧ κs ∼ T⟦ B ⟧ κs
    | ⌊ _ ∣ Γ ≫ A ∋ e1 ≐ e2 ⌋ =>
      τω ⊧ Γ⟦ Γ ⟧ κs ctx
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ (T⟦ A ⟧ κs) ∼ (T⟦ A ⟧ κs)
      → τω ⊧ Γ⟦ Γ ⟧ κs ≫ T⟦ A ⟧ κs ∋ T⟦ e1 ⟧ κs ∼ T⟦ e2 ⟧ κs
    end.

Notation "J⟦ J ⟧" := (interp_jdg J) (at level 50).

Ltac rewrite_all_hyps :=
  repeat
    match goal with
    | x : _ |- _ => rewrite -x
    end.

Local Open Scope program_scope.

Theorem interp_tm_naturality :
  ∀ Λ1 Λ2 Ψ (e : FTm.t Λ1 Ψ) (ρ : Ren.t Λ1 Λ2) (κs : Env.t Λ2),
    T⟦ e ⟧ κs ∘ ρ = T⟦ FTm.mapk ρ e ⟧ κs.
Proof.
  move=> Λ1 Λ2 Ψ e; move: Λ2.
  elim e => *; eauto; simpl; try by [rewrite_all_hyps].
  + f_equal; T.eqcd => ?.
    rewrite_all_hyps.
    f_equal; T.eqcd => i.
    by dependent induction i.
Qed.

Program Definition interp_clk_wk Λ Ψ (e : FTm.t Λ Ψ) (κs : Env.t Λ) (κ : CLK) :
  T⟦ e ⟧ κs = T⟦ FTm.mapk (Ren.weak 1) e ⟧ (κ ∷ κs)
  := interp_tm_naturality e (Ren.weak 1) (κ ∷ κs).
Next Obligation.
  by simplify_eqs.
Qed.

(*
Module Jdg.
  (* TODO: replace with open judgments *)
  Inductive atomic Λ Ψ :=
  | eq_ty : FTm.t Λ Ψ → FTm.t Λ Ψ → atomic Λ Ψ.


  Definition meaning (Λ : nat) (J : atomic Λ 0) : Prop :=
    match J with
    | eq_ty A B =>
      ∀ (σ : Env Λ),
        ⊧ ⟦ A ⟧ σ ∼ ⟦ B ⟧ σ
    end.


  Notation "⟦ Λ ∣ J ⟧" := (@meaning Λ J) (at level 50).

  Theorem test3 :
    ∀ (Λ : nat) (A : FTm.t Λ 0),
      ⟦ Λ ∣ eq_ty A A ⟧
      → ⟦ Λ ∣ eq_ty A (FTm.isect (FTm.mapk (Ren.weak 1) A)) ⟧.
  Proof.
    move=> Λ A D σ //=.
    have : (λ κ : CLK, ⟦ FTm.mapk (Ren.weak 1) A ⟧ κ ∷ σ) = (fun κ => ⟦A⟧ σ).
    + T.eqcd => *.
      by [rewrite -interp_clk_wk].
    + T.rewrite_; apply: ClosedRules.isect_irrelevance.
      case: (D σ) => ? [? ?];
      eauto.
  Qed.

End Jdg.
*)
