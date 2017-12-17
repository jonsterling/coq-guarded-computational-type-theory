Require Import Unicode.Utf8 Program.Equality Program.Tactics Program.Basics Vectors.Fin omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Term Axioms Var Sequent Tower.
From gctt Require Tactic.
Module T := Tactic.

Generalizable All Variables.
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

Delimit Scope eclk_scope with eclk.
Delimit Scope etm_scope with etm.

Notation "#0" := Fin.F1 : eclk_scope.
Notation "#1" := (Fin.FS Fin.F1) : eclk_scope.

Notation "@0" := (ETm.var _ Fin.F1) : etm_scope.
Notation "@1" := (ETm.var _ (Fin.FS Fin.F1)) : etm_scope.

Notation "▶[ k ] A" := (ETm.ltr k%eclk A%etm) (at level 50) : etm_scope.
Notation "𝟙" := ETm.unit : etm_scope.
Notation "𝟚" := ETm.bool : etm_scope.
Notation "★" := ETm.ax : etm_scope.
Notation "e .1" := (ETm.fst e%etm) (at level 50) : etm_scope.
Notation "e .2" := (ETm.snd e%etm) (at level 50) : etm_scope.
Infix "×" := ETm.prod : etm_scope.
Notation "⋂ A" := (ETm.isect A%etm) (at level 50) : etm_scope.
Notation "𝕌[ i ] " := (ETm.univ i%nat) : etm_scope.
Notation "⟨ e1 , e2 ⟩" := (ETm.pair e1%etm e2%etm) : etm_scope.
Notation "e .^ n" := (ETm.mapv (Ren.weak n) e%etm) (at level 50) : etm_scope.

Module ECtx.
  Inductive t (Λ : Var.Ctx) : Var.Ctx → Type :=
  | nil : t Λ 0
  | snoc : ∀ {Ψ}, t Λ Ψ → ETm.t Λ Ψ → t Λ (S Ψ).
End ECtx.

Delimit Scope ectx_scope with ectx.

Arguments ECtx.nil [Λ].
Arguments snoc [Ψ] Γ%ectx A%etm.

Notation "⋄" := ECtx.nil : ectx_scope.
Infix ";" := (ECtx.snoc) (at level 50, left associativity) : ectx_scope.

Module EJdg.
  Inductive t Λ :=
  | eq_ty : ∀ {Ψ}, ECtx.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ
  | eq_mem : ∀ {Ψ}, ECtx.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ
  | conv : ∀ {Ψ}, ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ.

  Arguments eq_ty [Λ Ψ] Γ%ectx A%etm B%etm.
  Arguments eq_mem [Λ Ψ] Γ%ectx A%etm e1%etm e2%etm.
  Arguments conv [Λ Ψ] e1%etm e2%etm.
End EJdg.


Delimit Scope ejdg_scope with ejdg.

Notation "Λ ∣ Γ ≫ A ≐ B" := (@EJdg.eq_ty Λ _ Γ A B) (at level 10) : ejdg_scope.
Notation "Λ ∣ Γ ≫ A ∋ e1 ≐ e2" := (@EJdg.eq_mem Λ _ Γ A e1 e2) (at level 10) : ejdg_scope.
Notation "Λ ∣ Ψ ⊢ e1 ≃ e2" := (@EJdg.conv Λ Ψ e1 e2) (at level 10) : ejdg_scope.

Notation "⌊ 𝒥 ⌋" := 𝒥%ejdg (only parsing).

Example example_judgment :=  ⌊ 1 ∣ ⋄ ≫ ▶[#0] 𝟙 ≐ ▶[#0] 𝟙 ⌋.

Module Env.
  Definition t Λ := Var Λ → 𝕂.

  Program Definition cons {Λ} (κ : 𝕂) (σ : t Λ) : t (S Λ) :=
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
  | ETm.fst e => (T⟦e⟧ κs) .1
  | ETm.snd e => (T⟦e⟧ κs) .2
  | ETm.unit => 𝟙
  | ETm.bool => 𝟚
  | ETm.ax => ★
  | ETm.tt => Tm.tt
  | ETm.ff => Tm.ff
  | ETm.prod A B => (T⟦A⟧ κs) × (T⟦B⟧ κs)
  | ETm.arr A B => (T⟦A⟧ κs) → (T⟦B⟧ κs)
  | ETm.pair A B => ⟨T⟦A⟧ κs, T⟦B⟧ κs⟩
  | ETm.ltr r A => ▶[κs r] T⟦A⟧ κs
  | ETm.isect A => ⋂[κ] T⟦A⟧ (κ ∷ κs)
  | ETm.univ i => Tm.univ i
  end
where "T⟦ e ⟧ κs" := (interp_tm e%etm κs) : tm_scope.

Arguments interp_tm [Λ Ψ] e%etm κs.

Program Fixpoint interp_ctx `(Γ : ECtx.t Λ Ψ) (κs : Env.t Λ) : Prectx Ψ :=
  match Γ with
  | ⋄%ectx => ⋄%ictx
  | (Γ ; A)%ectx => (Γ⟦ Γ ⟧ κs ; T⟦ A ⟧ κs)%ictx
  end
where "Γ⟦ Γ ⟧ κs" := (interp_ctx Γ%ectx κs).

Arguments interp_ctx [Λ Ψ] Γ%ectx κs.

Definition interp_jdg `(J : EJdg.t Λ) : Ω :=
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

Arguments interp_jdg [Λ] J%ejdg.
Notation "J⟦ J ⟧" := (interp_jdg J%ejdg) (at level 50).

Ltac rewrite_all_hyps :=
  repeat
    match goal with
    | x : _ |- _ => rewrite -x
    end.

Local Open Scope program_scope.
Local Open Scope tm_scope.

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

Local Close Scope tm_scope.
