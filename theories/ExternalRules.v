From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8.
Require Import Program.Equality.

From gctt Require Import Axioms Var Term ExternalSyn Tower Closure Sequent InternalRules.
From gctt Require InternalRules.
Module IR := InternalRules.


Theorem open_ax_equality Λ Ψ (Γ : ECtx.t Λ Ψ) :
  J⟦ ⌊ Λ ∣ Γ ≫ ETm.unit ∋ ETm.ax ≐ ETm.ax ⌋ ⟧.
Proof.
  move=> ? ? ? ? ? ?.
  apply: (@IR.eq_mem_from_level 0).
  apply: IR.unit_ax_equality.
Qed.

Theorem compute_symmetry Λ Ψ e1 e2 :
  J⟦ ⌊ Λ ∣ Ψ ⊢ e1 ≃ e2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Ψ ⊢ e2 ≃ e1 ⌋ ⟧.
Proof.
  move=> D κs γ v.
  specialize (D κs γ v).
  intuition.
Qed.

Theorem compute_transitivity Λ Ψ e1 e2 e3 :
  J⟦ ⌊ Λ ∣ Ψ ⊢ e1 ≃ e2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Ψ ⊢ e2 ≃ e3 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Ψ ⊢ e1 ≃ e3 ⌋ ⟧.
Proof.
  move=> D E κs γ v.
  specialize (D κs γ v).
  specialize (E κs γ v).
  intuition.
Qed.

Theorem conv_fst_pair Λ Ψ e1 e2 :
  J⟦ ⌊ Λ ∣ Ψ ⊢ ETm.fst (ETm.pair e1 e2) ≃ e1 ⌋ ⟧.
Proof.
  move=> κs γ v.
  split => //= D; inversion D; eauto.
  + match goal with
    | X : _ val |- _ => inversion X
    end.
  + match goal with
    | X : Tm.pair _ _ ⇓ _ |- _ => inversion X
    end.
    by congruence.
Qed.

Theorem hypothesis `{Γ : ECtx.t Λ Ψ} {A} :
  J⟦ ⌊ Λ ∣ Γ `; A ≫ A.^1 ∋ ETm.var _ Fin.F1 ≐ ETm.var _ Fin.F1 ⌋ ⟧.
Proof.
  move=> κs Γctx ty γ0 γ1 γ01.
  case: γ01 => [_ γ01].
  simplify_eqs.
  by rewrite -interp_tm_var_naturality.
Qed.

Theorem conv_ty `{Γ : ECtx.t Λ Ψ} {A0 A1 B} :
  J⟦ ⌊ Λ ∣ Ψ ⊢ A0 ≃ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ B ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ≐ B ⌋ ⟧.
Proof.
  move=> 𝒟 ℰ ? ? ? ? ?.
  apply: IR.ty_eq_conv.
  - eauto.
  - move=> ?; edestruct 𝒟; eauto.
  - apply: ℰ; eauto.
Qed.


Theorem ty_eq_symm `{Γ : ECtx.t Λ Ψ} {A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ≐ A0 ⌋ ⟧.
Proof.
  move=> 𝒟 κs Γctx γ0 γ1 γ01.
  apply: IR.ty_eq_symm.
  apply: 𝒟; eauto.
  apply: IR.env_eq_symm; eauto.
Qed.

Theorem ty_eq_trans `{Γ : ECtx.t Λ Ψ} {A0 A1 A2} :
  J⟦ ⌊ Λ ∣ Γ ≫ A1 ≐ A2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A2 ⌋ ⟧.
Proof.
  move=> 𝒟 ℰ ? ? ? ? ?.
  apply: IR.ty_eq_trans.
  - apply: 𝒟; eauto.
  - apply: ℰ; eauto.
    apply: IR.env_eq_refl_left; eauto.
Qed.


Theorem ty_eq_refl_left `{Γ : ECtx.t Λ Ψ} {A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A0 ⌋ ⟧.
Proof.
  move=> 𝒟.
  apply: ty_eq_trans.
  - apply: ty_eq_symm.
    eassumption.
  - eassumption.
Qed.


Theorem open_clock_irrelevance Λ Ψ Γ (A : ETm.t Λ Ψ) :
  J⟦ ⌊ Λ ∣ Γ ≫ A ≐ A ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A ≐ ETm.isect (ETm.mapk (Ren.weak 1) A) ⌋ ⟧.
Proof.
  move=> 𝒟 κs ? ? γ1 ?; simplify_eqs.
  replace (λ κ : 𝕂, (T⟦ ETm.mapk _ _ ⟧ _) ⫽ _) with (λ κ:𝕂, (T⟦A⟧ κs) ⫽ γ1).
  - apply: IR.isect_irrelevance.
    apply: 𝒟; eauto.
  - T.eqcd => *.
    by rewrite -interp_tm_clk_naturality.
Qed.

Theorem conv_mem `{Γ : ECtx.t Λ Ψ} {A e00 e01 e1} :
  J⟦ ⌊ Λ ∣ Ψ ⊢ e00 ≃ e01 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A ∋ e00 ≐ e1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A ∋ e01 ≐ e1 ⌋ ⟧.
Proof.
  move=> 𝒟 ℰ ? ? ? ? ? ?.
  apply: IR.mem_eq_conv.
  - eauto.
  - move=> ?; edestruct 𝒟; eassumption.
  - apply: ℰ; eauto.
Qed.


Theorem rewrite_ty_in_mem `{Γ : ECtx.t Λ Ψ} {A0 A1 e1 e2} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ∋ e1 ≐ e2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ∋ e1 ≐ e2⌋ ⟧.
Proof.
  move=> 𝒟 ℰ ? ? _ ? ? ?.
  apply: IR.rewrite_ty_in_mem.
  - apply: ℰ; eauto.
    apply: ty_eq_refl_left; eauto.
  - apply: 𝒟; eauto.
    apply: IR.env_eq_refl_left; eauto.
Qed.

Theorem conv_mem_ty `{Γ : ECtx.t Λ Ψ} {A0 A1 e0 e1} :
  J⟦ ⌊ Λ ∣ Ψ ⊢ A0 ≃ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ∋ e0 ≐ e1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ∋ e0 ≐ e1 ⌋ ⟧.
Proof.
  move=> 𝒟 ℰ κs ? ? ? ? ?.
  apply: IR.mem_eq_conv_ty.
  - eauto.
  - move=> ?; edestruct 𝒟; eauto.
  - apply: ℰ; eauto.
    move=> ? ? ?.
    apply: IR.ty_eq_conv.
    + eauto.
    + move=> ?; edestruct 𝒟; eassumption.
    + apply: IR.ty_eq_symm.
      apply: IR.ty_eq_conv.
      * eauto.
      * move=> ?; edestruct 𝒟; eassumption.
      * eauto.
Qed.

Theorem later_mem_univ `{Γ : ECtx.t Λ Ψ} {k i A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ ETm.ltr k (ETm.univ i) ∋ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ ETm.univ i ∋ (ETm.ltr k A0) ≐ (ETm.ltr k A1) ⌋ ⟧.
Proof.
  move=> 𝒟 ? ? ? ? ? ?; simpl.
  apply: IR.later_mem_univ.
  apply: 𝒟; eauto.
  move=> ? ? ?; simpl.
  apply: IR.later_formation.
  apply: Later.next.
  eauto.
Qed.
