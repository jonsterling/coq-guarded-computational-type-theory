From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8 Program.Equality Program.Basics omega.Omega.
From gctt Require Import Axioms Var Term ExternalSyn Tower Closure Sequent InternalRules.
From gctt Require InternalRules.
Module IR := InternalRules.


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

  Theorem conv_mem `{Γ : ECtx.t Λ Ψ} {A e00} e01 {e1} :
    ⟦ Λ ∣ Ψ ⊢ e00 ≃ e01 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e01 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e00 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: IR.mem_eq_conv.
    - eauto.
    - move=> ?; edestruct 𝒟; eassumption.
    - apply: ℰ; eauto.
  Qed.

  Theorem conv_ty `{Γ : ECtx.t Λ Ψ} A1 {A0 e0 e1} :
    ⟦ Λ ∣ Ψ ⊢ A0 ≃ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ e0 ≐ e1 ⟧.
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

  Theorem eq_symm `{Γ : ECtx.t Λ Ψ} {A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e1 ≐ e0 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01.
    apply: IR.mem_eq_symm.
    apply: IR.rewrite_ty_in_mem.
    - apply: 𝒟; eauto.
      apply: IR.env_eq_symm; eauto.
    - apply: IR.ty_eq_symm.
      apply: ℰ; eauto.
  Qed.

  Theorem eq_trans `{Γ : ECtx.t Λ Ψ} {A e0 e1 e2} :
    ⟦ Λ ∣ Γ ≫ A ∋ e1 ≐ e2 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e2 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: IR.mem_eq_trans.
    - apply: 𝒟; eauto.
    - apply: ℰ; eauto.
      apply: IR.env_eq_refl_left; eauto.
  Qed.

  Theorem eq_refl_left `{Γ : ECtx.t Λ Ψ} {A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e0 ⟧.
  Proof.
    move=> 𝒟.
    apply: eq_trans.
    - apply: eq_symm.
      eassumption.
    - eassumption.
  Qed.

  Theorem replace_ty `{Γ : ECtx.t Λ Ψ} i {A0 A1 e1 e2} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ e1 ≐ e2 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ e1 ≐ e2 ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ _ ? ? ?.
    apply: IR.rewrite_ty_in_mem.
    - apply: ℰ; eauto.
      move=> γ0' γ1' γ01'.
      apply: IR.eq_ty_from_level.
      apply: (@IR.univ_mem_inversion i).
      suff: τω ⊧ ⟦ Γ ⟧ κs ≫ ⟦ 𝕌[ i] ⟧ κs ∼ (⟦ 𝕌[ i] ⟧ κs).
      + move=> 𝒢.
        have 𝒟10' := (𝒟 κs ℱ 𝒢 γ1' γ0' (IR.env_eq_symm ℱ γ01')).
        have 𝒟00' := (𝒟 κs ℱ 𝒢 γ0' γ0' (IR.env_eq_refl_left ℱ γ01')).
        apply: IR.mem_eq_trans.
        * apply: IR.mem_eq_symm.
          exact 𝒟10'.
        * exact 𝒟00'.
      + move=> ? ? ? //=.
        apply: IR.univ_formation.
    - apply: IR.eq_ty_from_level.
      apply: (@IR.univ_mem_inversion).
      apply: 𝒟; auto.
      + move=> ? ? ? //=; apply: IR.univ_formation.
      + apply: IR.env_eq_refl_left; eassumption.
  Qed.

  Theorem mem_conv_all `{Γ : ECtx.t Λ Ψ} A' e0' e1' {A e0 e1} :
    ⟦ Λ ∣ Ψ ⊢ A ≃ A' ⟧
    → ⟦ Λ ∣ Ψ ⊢ e0 ≃ e0' ⟧
    → ⟦ Λ ∣ Ψ ⊢ e1 ≃ e1' ⟧
    → ⟦ Λ ∣ Γ ≫ A' ∋ e0' ≐ e1' ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> *.
    apply: conv_ty; eauto.
    apply: conv_mem; eauto.
    apply: eq_symm.
    apply: conv_mem; eauto.
    by apply: eq_symm.
  Qed.

  Theorem univ_formation i j `{Γ : ECtx.t Λ Ψ} :
    i < j
    → ⟦ Λ ∣ Γ ≫ 𝕌[j] ∋ 𝕌[i] ≐ 𝕌[i] ⟧.
  Proof.
    move=> ? ? ? ? ? ? ? //=.
    apply: IR.univ_mem_formation.
    apply: IR.univ_formation_lvl.
    assumption.
  Qed.
End General.

Module Unit.
  Theorem ax_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟙 ∋ ★ ≐ ★ ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    apply: IR.unit_ax_equality.
  Qed.
End Unit.


Module Bool.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ 𝟚 ≐ 𝟚 ⟧.
  Proof.
    move=> ? ? ? ? ? ? //=.
    apply: IR.univ_mem_formation.
    apply: IR.bool_formation_lvl.
  Qed.

  Theorem tt_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟚 ∋ ETm.tt ≐ ETm.tt ⟧.
  Proof.
    move=> ? ? ? ? ? ? //=.
    apply: IR.bool_tt_equality.
  Qed.
End Bool.



Module Prod.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1 B0 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (A0 × B0) ≐ (A1 × B1) ⟧.
  Proof.
    move=> 𝒟 ℰ κs Γctx ℱ γ0 γ1 γ01 //=.
    apply: IR.prod_formation_univ.
    - by apply: 𝒟.
    - by apply: ℰ.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {i j A B e00 e01 e10 e11} :
    ⟦ Λ ∣ Γ ≫ A ∋ e00 ≐ e10 ⟧
    → ⟦ Λ ∣ Γ ≫ B ∋ e01 ≐ e11 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[j] ∋ B ≐ B ⟧
    → ⟦ Λ ∣ Γ ≫ A × B ∋ ⟨e00, e01⟩ ≐ ⟨e10, e11⟩ ⟧.
  Proof.
    move=> 𝒟 ℰ ℱ 𝒢 κs Γctx ℋ γ0 γ1 γ01 //=.
    apply: IR.prod_intro.
    - apply: 𝒟; eauto.
      move=> ? ? ?.
      apply: IR.eq_ty_from_level.
      apply: IR.univ_mem_inversion.
      apply: ℱ; eauto.
      move=> ? ? ?.
      apply: IR.univ_formation.
    - apply: ℰ; eauto.
      move=> ? ? ?.
      apply: IR.eq_ty_from_level.
      apply: IR.univ_mem_inversion.
      apply: 𝒢; eauto.
      move=> ? ? ?.
      apply: IR.univ_formation.
  Qed.
End Prod.


Module Isect.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A0 ≐ ⋂ A1 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01 //=.
    apply: IR.univ_mem_formation.
    apply: IR.isect_formation => κ.
    T.efwd 𝒟; first (apply: IR.univ_mem_inversion);
    try rewrite -interp_ctx_clk_naturality;
    by [simplify_eqs; eauto].
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} i {A e0 e1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ A ∋ (e0.⦃^1⦄) ≐ (e1.⦃^1⦄) ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ⋂ A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℱ κs Γctx ℰ γ0 γ1 γ01 //=.
    case: (ℰ γ0 γ1 γ01) => R [[n0 ℰ0] [n1 ℰ1]].
    case: (ℰ γ1 γ0 (IR.env_eq_symm Γctx γ01)) => R' [[n0' ℰ0'] [n1' ℰ1']].

    replace R' with R in ℰ0', ℰ1'.

    - clear R'.
      IR.Tac.accum_lvl n.
      apply: (@IR.eq_mem_from_level n).
      repeat Tower.destruct_tower.
      apply: IR.isect_intro => κ.
      T.specialize_hyps.
      exists (S κ); split.
      + apply: Tower.monotonicity; last by [eassumption].
        rewrite /n; omega.
      + specialize (𝒟 (κ ∷ κs)).
        T.efwd 𝒟.
        * case: 𝒟 => R' [[n2 𝒟0] 𝒟1].
          replace R' with (S κ) in 𝒟0, 𝒟1.
          ** T.use 𝒟1.
             repeat f_equal;
             rewrite -interp_tm_clk_naturality;
             by simplify_eqs.
          ** apply: (@Tower.extensionality (n + n2)); simpl.
             *** apply: Tower.monotonicity; last by [eauto].
                 rewrite /n; omega.
             *** apply: Tower.monotonicity; last by [eauto].
                 rewrite /n; omega.
        * T.use γ01; f_equal.
          rewrite -interp_ctx_clk_naturality.
          by simplify_eqs.
        * move=> ? ? ?.
          apply: IR.eq_ty_from_level.
          apply: IR.univ_mem_inversion.
          apply: ℱ; auto.
          move=> ? ? ?.
          apply: IR.univ_formation.
        * T.use Γctx.
          f_equal.
          rewrite -interp_ctx_clk_naturality.
          by simplify_eqs.
    - apply: (@Tower.extensionality (n1 + n0')); simpl.
      * apply: Tower.monotonicity; last by [eassumption].
        omega.
      * apply: Tower.monotonicity; last by [eassumption].
        omega.
  Qed.

  Theorem irrelevance `{Γ : ECtx.t Λ Ψ} {i A} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ ⋂ (A.⦃^1⦄) ⟧.
  Proof.
    move=> 𝒟 κs ? ? γ0 γ1 γ01; simplify_eqs.
    replace (λ κ:𝕂, (⟦_.⦃_⦄ ⟧ _) ⫽ _) with (λ κ:𝕂, (⟦A⟧ κs) ⫽ γ1).
    - apply: IR.univ_mem_formation.
      apply: IR.isect_irrelevance.
      apply: IR.univ_mem_inversion.
      apply: 𝒟; eauto.
    - T.eqcd => *.
      by rewrite -interp_tm_clk_naturality.
  Qed.

  Theorem cartesian `{Γ : ECtx.t Λ Ψ} i {A0 B0 A1 B1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (⋂ (A0 × B0)) ≐ ((⋂ A0) × (⋂ B0)) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: IR.univ_mem_formation.
    apply: IR.isect_preserves_products => κ;
    apply: IR.univ_mem_inversion;
    [ specialize (𝒟 (κ ∷ κs));
      have := (IR.functionality_square (𝒟 _ _))
    | specialize (ℰ (κ ∷ κs));
      have := (IR.functionality_square (ℰ _ _))
    ];
    rewrite -interp_ctx_clk_naturality; simplify_eqs;
    move=> ℋ; edestruct ℋ as [ℋ0 [ℋ1 ℋ2]]; eauto.

    - apply: IR.mem_eq_trans.
      + apply: IR.mem_eq_symm; eauto.
      + eauto.

    - apply: IR.mem_eq_trans.
      + apply: IR.mem_eq_symm; eauto.
      + eauto.
  Qed.
End Isect.

Module Later.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {k A0 A1} :
    ⟦ Λ ∣ Γ ≫ ▶[k] 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ▶[k] A0 ≐ ▶[k] A1 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ?; simpl.
    apply: IR.later_mem_univ.
    apply: 𝒟; eauto.
    move=> ? ? ? //=.
    apply: IR.later_formation.
    apply: Later.next.
    apply: IR.univ_formation.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {k i A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ▶[k] A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ? //=.
    apply: IR.later_intro.
    apply: Later.next.
    apply: 𝒟; auto.
    move=> ? ? ?.
    apply: IR.eq_ty_from_level.
    apply: IR.univ_mem_inversion.
    apply: ℰ; auto.
    move=> ? ? ?.
    apply: IR.univ_formation.
  Qed.

  Theorem force `{Γ : ECtx.t Λ Ψ} {i A B} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A ≐ ⋂ B ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ ▶[#0] A ≐ ⋂ B ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? //=.
    apply: IR.univ_mem_formation.
    apply: IR.later_force.
    apply: IR.univ_mem_inversion.
    apply: 𝒟; eauto.
  Qed.

  Theorem induction `{Γ : ECtx.t Λ Ψ} k {A e0 e1} :
    ⟦ Λ ∣ Γ; ▶[k] A ≫ A.[^1] ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ μ{ e0 } ≐ μ{ e1 } ⟧.
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

  (* Guarded stream of bits. *)
  Example BitStream {Λ Ψ} (k : Var Λ) : ETm.t Λ Ψ :=
    μ{ 𝟚 × ▶[k] @0 }%etm.

  Arguments BitStream [Λ Ψ] k%eclk.

  (* Coinductive sequence of bits. *)
  Example BitSeq {Λ Ψ} : ETm.t Λ Ψ :=
    (⋂ (BitStream #0))%etm.

  Example BitStream_wf `{Γ : ECtx.t Λ Ψ} i {k} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (BitStream k) ≐ (BitStream k) ⟧.
  Proof.
    apply: (Later.induction k).
    apply: Prod.univ_eq.
    - apply: Bool.univ_eq.
    - apply: Later.univ_eq.
      apply: General.hypothesis.
  Qed.

  Example BitSeq_wf `{Γ : ECtx.t Λ Ψ} {i} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ BitSeq ≐ BitSeq ⟧.
  Proof.
    apply: Isect.univ_eq.
    apply: BitStream_wf.
  Qed.

  Example Ones {Λ Ψ} : ETm.t Λ Ψ :=
    μ{ ⟨ETm.tt, @0⟩ }%etm.


  Example BitStream_unfold `{Γ : ECtx.t Λ Ψ} {i k} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ BitStream k ≐ (𝟚 × ▶[k] BitStream k) ⟧.
  Proof.
    apply: (General.conv_mem (𝟚 × ▶[k] BitStream k)%etm).
    - move=> ? ?; apply: fix_unfold; eauto.
    - apply: Prod.univ_eq.
      + apply: Bool.univ_eq.
      + apply: Later.univ_eq.
        apply: Later.intro.
        * apply: BitStream_wf.
        * apply: (General.univ_formation i).
          eauto.
  Qed.

  Example Ones_wf_guarded `{Γ : ECtx.t Λ Ψ} {k} :
    ⟦ Λ ∣ Γ ≫ BitStream k ∋ Ones ≐ Ones ⟧.
  Proof.
    apply: (Later.induction k).
    apply: (General.replace_ty 0).
    - apply: General.eq_symm.
      apply: BitStream_unfold.
    - apply: Prod.intro.
      + apply: Bool.tt_equality.
      + apply: General.hypothesis.
      + apply: (Bool.univ_eq 0).
      + apply: (Later.univ_eq 0).
        apply: Later.intro.
        * apply: BitStream_wf.
        * apply: (General.univ_formation 0).
          eauto.
  Qed.

  Example Ones_wf_infinite `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ BitSeq ∋ Ones ≐ Ones ⟧.
  Proof.
    apply: Isect.intro.
    apply: Ones_wf_guarded.
    apply: (BitStream_wf 0).
  Qed.


  Example BitSeq_unfold `{Γ : ECtx.t Λ Ψ} i :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ BitSeq ≐ (𝟚 × BitSeq) ⟧.
  Proof.
    rewrite /BitSeq /BitStream.
    suff: ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ BitStream #0 ≐ ⋂ (𝟚 × ▶[#0] BitStream #0) ⟧.
    - move=> 𝒟; apply: General.eq_trans 𝒟.
      suff: ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ (𝟚 × ▶[#0] BitStream #0) ≐ ((⋂ 𝟚) × (⋂ ▶[#0] BitStream #0)) ⟧.
      + move=> ℰ; apply: General.eq_trans ℰ.
        apply: Prod.univ_eq.
        * apply: General.eq_symm.
          apply: Isect.irrelevance.
          apply: Bool.univ_eq.
        * apply: Later.force.
          apply: BitSeq_wf.

      + apply: Isect.cartesian.
        * apply: Bool.univ_eq.
        * apply: Later.univ_eq.
          apply: Later.intro.
          ** by apply: BitStream_wf.
          ** by apply: General.univ_formation.

    - apply: Isect.univ_eq.
      apply: BitStream_unfold.
  Qed.
End Examples.