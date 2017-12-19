From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8 Program.Equality Program.Basics.
From gctt Require Import Axioms Var Term ExternalSyn Tower Closure Sequent InternalRules.
From gctt Require InternalRules.
Module IR := InternalRules.

Module Unit.
  Theorem ax_equality Λ Ψ (Γ : ECtx.t Λ Ψ) :
    ⟦ Λ ∣ Γ ≫ 𝟙 ∋ ★ ≐ ★ ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    apply: IR.unit_ax_equality.
  Qed.
End Unit.

Module Conversion.
  Module Structural.
    Theorem symm {Λ Ψ e1 e2} :
      ⟦ Λ ∣ Ψ ⊢ e1 ≃ e2 ⟧
      → ⟦ Λ ∣ Ψ ⊢ e2 ≃ e1 ⟧.
    Proof.
      move=> D κs γ v.
      specialize (D κs γ v).
      intuition.
    Qed.

    Theorem trans {Λ Ψ e1 e2 e3} :
      ⟦ Λ ∣ Ψ ⊢ e1 ≃ e2 ⟧
      → ⟦ Λ ∣ Ψ ⊢ e2 ≃ e3 ⟧
      → ⟦ Λ ∣ Ψ ⊢ e1 ≃ e3 ⟧.
    Proof.
      move=> 𝒟 ℰ κs γ v.
      specialize (𝒟 κs γ v).
      specialize (ℰ κs γ v).
      intuition.
    Qed.
  End Structural.

  Theorem fst_of_pair {Λ Ψ e1 e2} :
    ⟦ Λ ∣ Ψ ⊢ ⟨e1, e2⟩ .1 ≃ e1 ⟧.
  Proof.
    move=> κs γ v.
    split; move=> [𝒟1 𝒟2].
    - split; auto.
      dependent destruction 𝒟1.
      + Term.destruct_evals.
      + dependent destruction H.
        * Term.destruct_evals.
        * eauto.
    - split; auto; simpl.
      econstructor.
      + apply: step_fst_pair.
      + auto.
  Qed.
End Conversion.

Module General.
  Local Hint Resolve ty_eq_refl_left ty_eq_trans ty_eq_symm.

  Theorem hypothesis `{Γ : ECtx.t Λ Ψ} {A} :
    ⟦ Λ ∣ Γ ; A ≫ A.[^1] ∋ @0 ≐ @0 ⟧.
  Proof.
    move=> κs Γctx ty γ0 γ1 γ01.
    case: γ01 => [_ γ01].
    simplify_eqs.
    by rewrite -interp_tm_var_naturality.
  Qed.

  Theorem conv_ty `{Γ : ECtx.t Λ Ψ} {A0 A1 B} :
    ⟦ Λ ∣ Ψ ⊢ A0 ≃ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ≐ B ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ≐ B ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ?.
    apply: IR.ty_eq_conv.
    - eauto.
    - move=> ?; edestruct 𝒟; eauto.
    - apply: ℰ; eauto.
  Qed.

  Theorem conv_mem `{Γ : ECtx.t Λ Ψ} {A e00 e01 e1} :
    ⟦ Λ ∣ Ψ ⊢ e00 ≃ e01 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e00 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e01 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: IR.mem_eq_conv.
    - eauto.
    - move=> ?; edestruct 𝒟; eassumption.
    - apply: ℰ; eauto.
  Qed.

  Theorem conv_mem_ty `{Γ : ECtx.t Λ Ψ} {A0 A1 e0 e1} :
    ⟦ Λ ∣ Ψ ⊢ A0 ≃ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ e0 ≐ e1 ⟧.
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

  Theorem ty_eq_symm `{Γ : ECtx.t Λ Ψ} {A0 A1} :
    ⟦ Λ ∣ Γ ≫ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ≐ A0 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ?.
    apply: IR.ty_eq_symm.
    apply: 𝒟; eauto.
    apply: IR.env_eq_symm; eauto.
  Qed.

  Theorem ty_eq_trans `{Γ : ECtx.t Λ Ψ} {A0 A1 A2} :
    ⟦ Λ ∣ Γ ≫ A1 ≐ A2 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ≐ A2 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ?.
    apply: IR.ty_eq_trans.
    - apply: 𝒟; eauto.
    - apply: ℰ; eauto.
      apply: IR.env_eq_refl_left; eauto.
  Qed.

  Theorem ty_eq_refl_left `{Γ : ECtx.t Λ Ψ} {A0 A1} :
    ⟦ Λ ∣ Γ ≫ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ≐ A0 ⟧.
  Proof.
    move=> 𝒟.
    apply: ty_eq_trans.
    - apply: ty_eq_symm.
      eassumption.
    - eassumption.
  Qed.

  Theorem replace_ty_in_mem `{Γ : ECtx.t Λ Ψ} {A0 A1 e1 e2} :
    ⟦ Λ ∣ Γ ≫ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ e1 ≐ e2 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ e1 ≐ e2 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? _ ? ? ?.
    apply: IR.rewrite_ty_in_mem.
    - apply: ℰ; eauto.
      apply: ty_eq_refl_left; eauto.
    - apply: 𝒟; eauto.
      apply: IR.env_eq_refl_left; eauto.
  Qed.
End General.

Module Bool.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} {i} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ 𝟚 ≐ 𝟚 ⟧.
  Proof.
    move=> ? ? ? ? ? ? //=.
    apply: IR.univ_mem_formation.
    apply: IR.bool_formation_lvl.
  Qed.
End Bool.

Module Prod.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} {i A0 A1 B0 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (A0 × B0) ≐ (A1 × B1) ⟧.
  Proof.
    move=> 𝒟 ℰ κs Γctx ℱ γ0 γ1 γ01 //=.
    apply: IR.prod_formation_univ.
    - by apply: 𝒟.
    - by apply: ℰ.
  Qed.
End Prod.


Module Isect.
  Theorem irrelevance Λ Ψ Γ (A : ETm.t Λ Ψ) :
    ⟦ Λ ∣ Γ ≫ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ A ≐ ⋂ (A.⦃^1⦄) ⟧.
  Proof.
    move=> 𝒟 κs ? ? γ1 ?; simplify_eqs.
    replace (λ κ : 𝕂, (⟦_.⦃_⦄ ⟧ _) ⫽ _) with (λ κ:𝕂, (⟦A⟧ κs) ⫽ γ1).
    - apply: IR.isect_irrelevance.
      apply: 𝒟; eauto.
    - T.eqcd => *.
        by rewrite -interp_tm_clk_naturality.
  Qed.
End Isect.

Module Later.
  Theorem formation `{Γ : ECtx.t Λ Ψ} {k i A0 A1} :
    ⟦ Λ ∣ Γ ≫ ▶[k] 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ▶[k] A0 ≐ ▶[k] A1 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ?; simpl.
    apply: IR.later_mem_univ.
    apply: 𝒟; eauto.
    move=> ? ? ?; simpl.
    apply: IR.later_formation.
    apply: Later.next.
    apply: IR.univ_formation.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {k A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ▶[k] A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? ?; simpl.
    apply: IR.later_intro.
    apply: Later.next.
    apply: 𝒟; auto.
  Qed.

  Theorem force `{Γ : ECtx.t Λ Ψ} {A B} :
    ⟦ Λ ∣ Γ ≫ ⋂ A ≐ ⋂ B ⟧
    → ⟦ Λ ∣ Γ ≫ ⋂ ▶[#0] A ≐ ⋂ B ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ?; simpl.
    apply: IR.later_force.
    apply: 𝒟; eauto.
  Qed.

  Theorem induction `{Γ : ECtx.t Λ Ψ} k {A e0 e1} :
    ⟦ Λ ∣ Γ; ▶[k] A ≫ A.[^1] ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ (ETm.fix_ e0) ≐ (ETm.fix_ e1) ⟧.
  Proof.
    move=> 𝒟 κs ? ℰ; simpl.
    apply: (@IR.loeb_induction_open (κs k)).
    simplify_eqs.

    move: {𝒟} (𝒟 κs); simplify_eqs => 𝒟.
    rewrite interp_tm_var_ren_naturality.
    apply: 𝒟.
    - split; auto.
      move=> ? ? ? //=.
      apply: IR.later_formation.
      apply: Later.next.
      auto.
    - move=> ? ? γ01 //=.
      rewrite -interp_tm_var_ren_naturality.
      Term.simplify_subst.
      apply: ℰ.
      by case: γ01.
  Qed.

End Later.


Module Examples.
  Example BitStream {Λ Ψ} (k : Var Λ) : ETm.t Λ Ψ :=
    (ETm.fix_ (𝟚 × ▶[k] @0))%etm.

  Example BitStream_wf `{Γ : ECtx.t Λ Ψ} {k i} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (BitStream k) ≐ (BitStream k) ⟧.
  Proof.
    apply: (Later.induction k).
    apply: Prod.univ_eq.
    - apply: Bool.univ_eq.
    - apply: Later.formation.
      apply: General.hypothesis.
  Qed.
End Examples.