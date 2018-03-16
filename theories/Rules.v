Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8 Program.Equality Program.Basics omega.Omega Logic.FunctionalExtensionality.
From ctt Require Import Axioms Var Program Expression Elaborate Tower Closure Sequent.

From ctt Require Theorems.
Module Th := Theorems.

Open Scope program_scope.

Lemma cons_weak_simple {Λ κ} {κs : Env.t Λ} :
  κ ∷ κs ∘ (^1)%ren = κs.
Proof.
  rewrite /compose.
  T.eqcd => x.
  by simplify_eqs.
Qed.


Hint Rewrite @cons_weak_simple : syn_db.
Hint Rewrite <- @elab_ctx_clk_naturality @elab_tm_clk_naturality @elab_tm_var_naturality @elab_tm_var_ren_naturality @elab_tm_ren_naturality @elab_tm_subst_naturality : syn_db.
Hint Unfold compose : syn_db.

Local Hint Extern 40 => autorewrite with syn_db; Program.simplify_subst.
Local Hint Extern 20 => Th.Univ.tac.

Local Hint Resolve Th.General.ty_eq_refl_left Th.General.ty_eq_trans Th.General.ty_eq_symm Th.General.mem_eq_trans Th.General.mem_eq_symm Th.General.env_eq_refl_left Th.General.env_eq_symm Th.General.open_mem_eq_refl_left Th.General.open_ty_eq_refl_left.

Module Conversion.
  Theorem symm {Λ Ψ M1 M2} :
    ⟦ Λ ∣ Ψ ⊢ M1 ≃ M2 ⟧
    → ⟦ Λ ∣ Ψ ⊢ M2 ≃ M1 ⟧.
  Proof.
    move=> D κs γ V.
    specialize (D κs γ V).
    intuition.
  Qed.

  Theorem trans {Λ Ψ M1 M2 M3} :
    ⟦ Λ ∣ Ψ ⊢ M1 ≃ M2 ⟧
    → ⟦ Λ ∣ Ψ ⊢ M2 ≃ M3 ⟧
    → ⟦ Λ ∣ Ψ ⊢ M1 ≃ M3 ⟧.
  Proof.
    move=> 𝒟 ℰ κs γ V.
    specialize (𝒟 κs γ V).
    specialize (ℰ κs γ V).
    intuition.
  Qed.

  Theorem fst_of_pair {Λ Ψ M1 M2} :
    ⟦ Λ ∣ Ψ ⊢ ⟨M1, M2⟩ .1 ≃ M1 ⟧.
  Proof.
    move=> κs γ V.
    split; move=> [𝒟1 𝒟2].
    - split; auto.
      dependent destruction 𝒟1.
      + OpSem.destruct_evals.
      + dependent destruction H.
        * OpSem.destruct_evals.
        * eauto.
    - split; auto; simpl.
      econstructor.
      + apply: OpSem.step_fst_pair.
      + auto.
  Qed.
End Conversion.

Module General.
  Theorem hypothesis `{Γ : ECtx.t Λ Ψ} {A} :
    ⟦ Λ ∣ Γ ∙ A ≫ A.[^1] ∋ @0 ≐ @0 ⟧.
  Proof.
    move=> κs Γctx ty γ0 γ1 γ01.
    case: γ01 => [_ γ01].
    auto.
  Qed.

  (* TODO: fix notation ? *)
  Theorem weakening `{Γ : ECtx.t Λ Ψ} i {A B M0 M1} :
    ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ∙ B ≫ (A.[^1]) ∋ (M0.[^1]) ≐ (M1.[^1]) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01.
    repeat rewrite -elab_tm_var_ren_naturality.
    simplify_subst.
    apply: 𝒟.
    - by case: ℱ.
    - Th.Univ.tac.
      apply: ℰ; eauto.
      by case: ℱ.
    - by case: γ01.
  Qed.

  Theorem conv_mem `{Γ : ECtx.t Λ Ψ} {A M00} M01 {M1} :
    ⟦ Λ ∣ Ψ ⊢ M00 ≃ M01 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M01 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M00 ≐ M1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: Th.General.mem_eq_conv.
    - move=> ?; edestruct 𝒟; eassumption.
    - apply: ℰ; eauto.
  Qed.

  Theorem conv_ty `{Γ : ECtx.t Λ Ψ} A1 {A0 M0 M1} :
    ⟦ Λ ∣ Ψ ⊢ A0 ≃ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ M0 ≐ M1 ⟧.
  Proof.
    move=> 𝒟 ℰ κs ? ? ? ? ?.
    apply: Th.General.mem_eq_conv_ty.
    - move=> ?; edestruct 𝒟; eauto.
    - apply: ℰ; eauto.
      move=> ? ? ?.
      apply: Th.General.ty_eq_conv.
      + move=> ?; edestruct 𝒟; eassumption.
      + apply: Th.General.ty_eq_symm.
        apply: Th.General.ty_eq_conv.
        * move=> ?; edestruct 𝒟; eassumption.
        * eauto.
  Qed.

  Theorem eq_symm `{Γ : ECtx.t Λ Ψ} {A M0 M1} :
    ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M1 ≐ M0 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01.
    apply: Th.General.mem_eq_symm.
    apply: Th.General.replace_ty_in_mem_eq; eauto.
    apply: 𝒟; eauto.
    by apply: Th.General.env_eq_symm.
  Qed.

  Theorem eq_trans `{Γ : ECtx.t Λ Ψ} {A M0 M1 M2} :
    ⟦ Λ ∣ Γ ≫ A ∋ M1 ≐ M2 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M2 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: Th.General.mem_eq_trans; auto.
    - apply: 𝒟; eauto.
    - apply: ℰ; eauto.
      apply: Th.General.env_eq_refl_left; eauto.
  Qed.

  Theorem eq_refl_left `{Γ : ECtx.t Λ Ψ} {A M0 M1} :
    ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M0 ⟧.
  Proof.
    move=> 𝒟.
    apply: eq_trans.
    - apply: eq_symm.
      eassumption.
    - eassumption.
  Qed.

  Theorem replace_ty `{Γ : ECtx.t Λ Ψ} i {A0 A1 M1 M2} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ A0 ∋ M1 ≐ M2 ⟧
    → ⟦ Λ ∣ Γ ≫ A1 ∋ M1 ≐ M2 ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ _ ? ? ?.
    apply: Th.General.replace_ty_in_mem_eq.
    - apply: ℰ; [eauto | | eauto].
      apply: Th.General.open_ty_eq_refl_left.
      + assumption.
      + apply: Th.Univ.open_inversionω; eauto.
    - apply: Th.Univ.inversionω.
      apply: 𝒟; eauto.
      apply: Th.General.env_eq_refl_left; eauto.
  Qed.

  Theorem mem_conv_all `{Γ : ECtx.t Λ Ψ} A' M0' M1' {A M0 M1} :
    ⟦ Λ ∣ Ψ ⊢ A ≃ A' ⟧
    → ⟦ Λ ∣ Ψ ⊢ M0 ≃ M0' ⟧
    → ⟦ Λ ∣ Ψ ⊢ M1 ≃ M1' ⟧
    → ⟦ Λ ∣ Γ ≫ A' ∋ M0' ≐ M1' ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧.
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
    apply: Th.Univ.intro.
    apply: Th.Univ.formation_lvl.
    assumption.
  Qed.
End General.

Module Unit.
  Theorem ax_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟙 ∋ ★ ≐ ★ ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    apply: Th.Unit.ax_equality.
  Qed.
End Unit.


Module Bool.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ 𝟚 ≐ 𝟚 ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    Th.Bool.tac.
  Qed.

  Theorem tt_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟚 ∋ Expr.tt ≐ Expr.tt ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    Th.Bool.tac.
  Qed.

  Theorem ff_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟚 ∋ Expr.ff ≐ Expr.ff ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    Th.Bool.tac.
  Qed.
End Bool.


Module Arr.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1 B0 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ∙ A0 ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (A0 ⇒ B0) ≐ (A1 ⇒ B1) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: Th.Arr.univ_eq.
    - by apply: 𝒟.
    - move=> ? ? //= [_ ℋ] //=.
      simplify_subst.
      T.efwd ℰ.
      + T.use ℰ; eauto.
      + split; [T.use γ01 | T.use ℋ]; eauto.
      + eauto.
      + split; first by assumption.
        apply: Th.General.open_ty_eq_refl_left.
        * assumption.
        * apply: Th.Univ.open_inversionω.
          eauto.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {i A B f0 f1} :
    ⟦ Λ ∣ Γ ∙ A ≫ B ∋ f0 ≐ f1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ∙ A ≫ 𝕌[i] ∋ B ≐ B ⟧
    → ⟦ Λ ∣ Γ ≫ (A ⇒ B) ∋ 𝛌{ f0 } ≐ 𝛌{f1} ⟧.
  Proof.
    move=> 𝒟 ℰ ℱ κs 𝒢 ℋ γ0 γ1 γ01 //=.
    apply: Th.Arr.intro.
    - move=> ? ? //= [_ ℐ] //=.
      simplify_subst.
      T.efwd 𝒟.
      + T.use 𝒟; eauto.
      + split; [T.use γ01 | T.use ℐ]; eauto.
      + apply: Th.Univ.open_inversionω.
        apply: ℱ; auto.
      + split; first by assumption.
        apply: Th.Univ.open_inversionω.
        apply: ℰ; auto.
    - apply: Th.Univ.inversion.
      apply: ℰ; auto.
      apply: Th.General.env_eq_refl_left; eauto.
    - apply: Th.Univ.open_inversion.
      + move=> ? ? γ01' //=.
        simplify_subst.
        apply: ℱ; auto.
        * split; auto.
          apply: Th.Univ.open_inversionω.
          eauto.
        * suff γ00 : τω ⊧ ∥Γ∥ κs ∋⋆ γ0 ∼ γ0.
          ** split; simpl.
             *** T.use γ00; eauto.
             *** case: γ01' => //= _ ℐ.
                 T.use ℐ; eauto.
          ** apply: Th.General.env_eq_refl_left; eauto.
  Qed.

  Theorem elim `{Γ : ECtx.t Λ Ψ} {i A B f0 f1 M0 M1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ∙ A ≫ 𝕌[i] ∋ B ≐ B ⟧
    → ⟦ Λ ∣ Γ ≫ (A ⇒ B) ∋ f0 ≐ f1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ (B ⫽ Sub.inst0 M0) ∋ (f0 ⋅ M0) ≐ (f1 ⋅ M1) ⟧.
  Proof.
    move=> 𝒟 ℰ ℱ 𝒢 κs ℋ ℐ γ0 γ1 γ01.
    autorewrite with syn_db; simpl.
    replace
      ((∥B∥ κs) ⫽ (γ0 ◎ (∥Sub.inst0 M0∥ κs)))%prog
      with ((∥B∥ κs) ⫽ Sub.cong γ0 ⫽ Sub.inst0 ((∥M0∥ κs) ⫽ γ0))%prog.
    - apply: Th.Arr.elim.
      + apply: Th.Univ.inversion.
        apply: 𝒟; eauto.
        apply: Th.General.env_eq_refl_left; eauto.
      + apply: Th.Univ.open_inversion.
        * move=> ? ? //= [_ 𝒥].
          T.efwd ℰ.
          ** T.use ℰ; auto.
          ** suff γ00 : τω ⊧ ∥Γ∥ κs ∋⋆ γ0 ∼ γ0.
             *** split; [T.use γ00 | T.use 𝒥]; eauto.
             *** apply: Th.General.env_eq_refl_left; eauto.
          ** eauto.
          ** split; auto.
             apply: Th.Univ.open_inversionω.
             apply: 𝒟; auto.
      + apply: ℱ; auto.
        apply: Th.Univ.open_inversionω.
        apply: univ_eq; eauto.
      + apply: 𝒢; auto.
        apply: Th.Univ.open_inversionω.
        eauto.
    - simplify_subst.
      dependent induction x; auto.
  Qed.
End Arr.

Module Prod.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1 B0 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ∙ A0 ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (A0 × B0) ≐ (A1 × B1) ⟧.
  Proof.
    move=> 𝒟 ℰ κs Γctx ℱ γ0 γ1 γ01 //=.
    apply: Th.Prod.univ_eq.
    - by apply: 𝒟.
    - move=> ? ? [_ 𝒢] //=.
      simplify_subst.
      T.efwd ℰ.
      + T.use ℰ; eauto.
      + split; [T.use γ01 | T.use 𝒢]; eauto.
      + eauto.
      + split; first by assumption.
        apply: Th.General.open_ty_eq_refl_left.
        * assumption.
        * apply: Th.Univ.open_inversionω.
          eauto.
  Qed.

  Lemma subst `{Γ : Prectx Ψ} {A B0 B1 M0 M1} :
    τω ⊧ Γ ∙ A ≫ B0 ∼ B1
    → τω ⊧ Γ ≫ A ∋ M0 ∼ M1
    → τω ⊧ Γ ≫ (B0 ⫽ Sub.inst0 M0) ∼ (B1 ⫽ Sub.inst0 M1).
  Proof.
    move=> 𝒟 ℰ γ0 γ1 γ01.
    simplify_subst.
    apply: 𝒟.
    split; eauto.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {i A B M00 M01 M10 M11} :
    ⟦ Λ ∣ Γ ≫ A ∋ M00 ≐ M10 ⟧
    → ⟦ Λ ∣ Γ ≫ B ⫽ Sub.inst0 M00 ∋ M01 ≐ M11 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ∙ A ≫ 𝕌[i] ∋ B ≐ B ⟧
    → ⟦ Λ ∣ Γ ≫ A × B ∋ ⟨M00, M01⟩ ≐ ⟨M10, M11⟩ ⟧.
  Proof.
    move=> 𝒟 ℰ ℱ 𝒢 κs Γctx ℋ γ0 γ1 γ01 //=.
    suff 𝒥 : τω ⊧ ∥Γ∥ κs ≫ ∥A∥ κs ∼ ∥A∥ κs.
    - apply: Th.Prod.intro.
      + apply: 𝒟; eauto.
      + T.efwd ℰ.
        * T.use ℰ.
          simplify_subst.
          dependent induction x; auto.
        * auto.
        * apply: Th.General.open_ty_eq_refl_left; auto.
          replace (∥B ⫽ Sub.inst0 M00∥ κs)%prog with ((∥B∥ κs) ⫽ Sub.inst0 (∥M00∥ κs)%prog)%prog.
          ** apply: subst; auto.
             apply: Th.Univ.open_inversionω.
             apply: 𝒢; auto.
          ** replace (∥B ⫽ Sub.inst0 M00∥ κs)%prog with ((∥B ⫽ Sub.inst0 M00∥ κs) ⫽ @Prog.var _)%prog.
             *** rewrite -elab_tm_subst_naturality /elab_subst //=.
                 simplify_subst.
                 rewrite Prog.subst_ret.
                 by dependent induction x.
             *** by rewrite Prog.subst_ret.
        * auto.
      + apply: Th.General.ty_eq_refl_left.
        apply: Th.Univ.inversion.
        apply: ℱ; eauto.
      + move=> //= ? ? [_ /Th.Level.eq_mem_from_level ℐ].
        apply: Th.Univ.inversion.
        repeat rewrite Prog.subst_coh.
        apply: 𝒢; auto.
        split; simpl.
        * T.use (Th.General.env_eq_refl_left Γctx γ01).
          simplify_subst.
        * T.use ℐ.
          simplify_subst.
    - apply: Th.General.open_ty_eq_refl_left; auto.
      apply: Th.Univ.open_inversionω.
      apply: ℱ; auto.
  Qed.
End Prod.


Module Isect.

  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A0 ≐ ⋂ A1 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01 //=.
    apply: Th.Univ.intro.
    apply: Th.Isect.formation => κ.
    T.efwd 𝒟; eauto;
    autorewrite with core;
    eauto.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} i {A M0 M1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ A ∋ (M0.⦃^1⦄) ≐ (M1.⦃^1⦄) ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ⋂ A ∋ M0 ≐ M1 ⟧.
  Proof.
    move=> 𝒟 ℱ κs ? ℰ ? ? ? //=.
    apply: Th.Isect.intro.
    - Th.Univ.tac.
      apply: univ_eq; eauto.
      apply: Th.General.env_eq_refl_left; eauto.
    - move=> κ.
      T.efwd 𝒟.
      + T.use 𝒟; eauto.
      + eauto.
      + Th.Univ.tac.
        apply: ℱ; eauto.
      + eauto.
  Qed.

  Theorem irrelevance `{Γ : ECtx.t Λ Ψ} {i A} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ ⋂ (A.⦃^1⦄) ⟧.
  Proof.
    move=> 𝒟 κs ? ? γ0 γ1 γ01; simplify_eqs.
    replace (λ κ:𝕂, (∥_.⦃_⦄∥ _) ⫽ _)%prog with (λ κ:𝕂, (∥A∥ κs) ⫽ γ1)%prog.
    - apply: Th.Univ.intro.
      apply: Th.Isect.irrelevance.
      apply: Th.Univ.inversion.
      apply: 𝒟; eauto.
    - simplify_subst; eauto.
  Qed.

  Theorem preserves_sigma `{Γ : ECtx.t Λ Ψ} i {A0 B0 A1 B1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ∙ A0 ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (⋂ (A0 × B0)) ≐ ((⋂ A1) × (⋂ B1)) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: Th.Univ.intro.
    simplify_subst.
    apply: Th.Isect.preserves_sigma.
    - move=> κ.
      Th.Univ.tac.
      apply: 𝒟; eauto.
    - move=> κ γ0' γ1' γ01'.
      Th.Univ.tac.
      simplify_subst.
      apply: ℰ.
      + split; auto.
        move=> ? ? ?.
        suff:  ⟦ (S Λ) ∣ Γ .⦃ ^ 1 ⦄ ≫ 𝕌[ i] ∋ A0 ≐ A0 ⟧.
        * move=> H; Th.Univ.tac; apply: H; eauto.
        * move=> ? ? ? ? ? ?; simplify_subst.
          apply: Th.General.mem_eq_trans.
          ** apply: Th.General.mem_eq_symm; eauto.
             apply: 𝒟; eauto.
             apply: Th.General.env_eq_symm; eauto.
          ** apply: 𝒟; eauto.
             apply: Th.General.env_eq_refl_left; eauto.
      + eauto.
      + split; simpl; simplify_subst.
        ** T.use γ01; eauto.
        ** case: γ01' => //= ? ℋ; simpl.
           apply: (Th.Level.eq_mem_from_level i).
           T.use ℋ; eauto.
  Qed.
End Isect.

Module Later.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {k A0 A1} :
    ⟦ Λ ∣ Γ ≫ ▶[k] 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ▶[k] A0 ≐ ▶[k] A1 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? //=.
    apply: Th.Later.univ_eq.
    apply: 𝒟; try by eassumption.

    move=> ? ? ? //=.
    apply: (Th.Level.eq_ty_from_level (S i)).
    apply: Th.Later.formation.
    apply: Later.next.
    apply: Th.Univ.formation_S.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {k i A M0 M1} :
    ⟦ Λ ∣ Γ ≫ A ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ▶[k] A ∋ M0 ≐ M1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ? //=.
    apply: Th.Later.intro.
    apply: Later.next.
    apply: 𝒟; auto.

    Th.Univ.tac.
    apply: ℰ; eauto.
  Qed.

  Theorem force `{Γ : ECtx.t Λ Ψ} {i A B} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A ≐ ⋂ B ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ ▶[#0] A ≐ ⋂ B ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? //=.
    apply: Th.Univ.intro.
    apply: Th.Later.force.
    Th.Univ.tac.
    apply: 𝒟; eauto.
  Qed.

  Theorem preserves_sigma `{Γ : ECtx.t Λ Ψ} i κ {A0 B0 A1 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ∙ A0 ≫ ▶[κ] 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (▶[κ] (A0 × B0)) ≐ ((▶[κ] A1) × (▶[κ] B1)) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: Th.Univ.intro.
    apply: Th.Later.preserves_sigma; simpl in *.
    - apply: Later.next.
      T.efwd 𝒟; eauto.
    - apply: Later.push_universal => γ0'.
      apply: Later.push_universal => γ1'.
      apply: Later.push_universal; case=> _ ℋ.
      simpl in *.
      specialize (𝒟 κs ℱ).
      simpl in *.
      T.efwd ℰ.
      + apply: (Later.map Th.Univ.inversion).
        apply: Th.Later.mem_univ_inversion.
        apply: Th.Later.univ_eq.
        T.use ℰ; eauto.
      + split; simpl.
        * T.use γ01; eauto.
        * apply: (Th.Level.eq_mem_from_level i).
          T.use ℋ; eauto.
      + move=> ? ? ? //=.
        apply: (Th.Level.eq_ty_from_level (S i)).
        apply: Th.Later.formation.
        apply: Later.next.
        apply: Th.Univ.formation_S.
      + split; eauto.
        move=> γ0'' γ1'' γ01''.
        suff: (τω ⊧ ((∥A0∥ κs) ⫽ γ0'') ∼ ((∥A1∥ κs) ⫽ γ0'')) ∧ (τω ⊧ ((∥A0∥ κs) ⫽ γ1'') ∼ ((∥A1∥ κs) ⫽ γ0'')).
        * case=> H0 H1.
          apply: Th.General.ty_eq_trans; eauto.
        * split; apply: Th.Univ.inversionω.
          ** T.efwd 𝒟.
             *** eauto.
             *** apply: Th.General.env_eq_refl_left; eauto.
             *** eauto.
          ** T.efwd 𝒟.
             *** eauto.
             *** apply: Th.General.env_eq_symm; eauto.
             *** eauto.
  Qed.

  Theorem preserves_pi `{Γ : ECtx.t Λ Ψ} i κ {A0 B0 A1 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ∙ A0 ≫ ▶[κ] 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (▶[κ] (A0 ⇒ B0)) ≐ ((▶[κ] A1) ⇒ (▶[κ] B1)) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: Th.Univ.intro.
    apply: Th.Later.preserves_pi; simpl in *.
    - apply: Later.next.
      T.efwd 𝒟; eauto.
    - apply: Later.push_universal => γ0'.
      apply: Later.push_universal => γ1'.
      apply: Later.push_universal; case=> _ ℋ.
      simpl in *.
      specialize (𝒟 κs ℱ).
      simpl in *.
      T.efwd ℰ.
      + apply: (Later.map Th.Univ.inversion).
        apply: Th.Later.mem_univ_inversion.
        apply: Th.Later.univ_eq.
        T.use ℰ; eauto.
      + split; simpl.
        * T.use γ01; eauto.
        * apply: (Th.Level.eq_mem_from_level i).
          T.use ℋ; eauto.
      + move=> ? ? ? //=.
        apply: (Th.Level.eq_ty_from_level (S i)).
        apply: Th.Later.formation.
        apply: Later.next.
        apply: Th.Univ.formation_S.
      + split; eauto.
        move=> γ0'' γ1'' γ01''.
        suff: (τω ⊧ ((∥A0∥ κs) ⫽ γ0'') ∼ ((∥A1∥ κs) ⫽ γ0'')) ∧ (τω ⊧ ((∥A0∥ κs) ⫽ γ1'') ∼ ((∥A1∥ κs) ⫽ γ0'')).
        * case=> H0 H1.
          apply: Th.General.ty_eq_trans; eauto.
        * split; apply: Th.Univ.inversionω.
          ** T.efwd 𝒟.
             *** eauto.
             *** apply: Th.General.env_eq_refl_left; eauto.
             *** eauto.
          ** T.efwd 𝒟.
             *** eauto.
             *** apply: Th.General.env_eq_symm; eauto.
             *** eauto.
  Qed.

  Theorem induction `{Γ : ECtx.t Λ Ψ} k {i A M0 M1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ∙ ▶[k] A ≫ A.[^1] ∋ M0 ≐ M1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ μ{ M0 } ≐ μ{ M1 } ⟧.
  Proof.
    move=> 𝒟 ℰ κs ? ℱ ? ? γ01 //=.
    apply: (Th.Later.loeb_induction_closed (κs k)).
    - apply: Th.Univ.inversion.
      apply: 𝒟; eauto.
    - move=> //= ? ? [_ 𝒢]; simplify_subst.

      T.efwd ℰ.
      + T.use ℰ; eauto.
      + split; [T.use γ01 | T.use 𝒢]; eauto.
      + move=> //= ? ? [? ?].
        simplify_subst.
        apply: ℱ; eauto.
      + split; first by [assumption].
        move=> //= ? ? ?.
        apply: (Th.Level.eq_ty_from_level i).
        apply: Th.Later.formation.
        apply: Later.next.
        apply: Th.Univ.inversion.
        apply: 𝒟; eauto.
  Qed.
End Later.


Module Examples.

  (* Guarded stream of bits. *)
  Example BitStream {Λ Ψ} (k : Var Λ) : Expr.t Λ Ψ :=
    μ{ 𝟚 × ▶[k] @1 }%etm.

  Arguments BitStream [Λ Ψ] k%eclk.

  (* Coinductive sequence of bits. *)
  Example BitSeq {Λ Ψ} : Expr.t Λ Ψ :=
    (⋂ (BitStream #0))%etm.

  Example BitStream_wf `{Γ : ECtx.t Λ Ψ} i {k} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (BitStream k) ≐ (BitStream k) ⟧.
  Proof.
    apply: (Later.induction k).
    - apply: General.univ_formation; eauto.
    - apply: Prod.univ_eq.
      + apply: Bool.univ_eq.
      + apply: Later.univ_eq.

        suff Q: @1%etm = (@0 .[^1])%etm; auto.
        rewrite !Q {Q}.

        suff Q : (▶[k] 𝕌[i])%etm = ((▶[k] 𝕌[i]).[^1])%etm; auto.
        rewrite !Q {Q}.

        apply: General.weakening.
        * apply: General.hypothesis.
        * apply: Later.univ_eq.
          apply: Later.intro; apply: General.univ_formation; auto.
  Qed.

  Example BitSeq_wf `{Γ : ECtx.t Λ Ψ} {i} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ BitSeq ≐ BitSeq ⟧.
  Proof.
    apply: Isect.univ_eq.
    apply: BitStream_wf.
  Qed.

  Example Ones {Λ Ψ} : Expr.t Λ Ψ :=
    μ{ ⟨Expr.tt, @0⟩ }%etm.


  Example BitStream_unfold `{Γ : ECtx.t Λ Ψ} {i k} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ BitStream k ≐ (𝟚 × ▶[k] BitStream k) ⟧.
  Proof.
    apply: (General.conv_mem (𝟚 × ▶[k] BitStream k)%etm).
    - move=> ? ?; apply: OpSem.fix_unfold.
    - apply: Prod.univ_eq.
      + apply: Bool.univ_eq.
      + apply: Later.univ_eq.
        apply: Later.intro.
        * apply: BitStream_wf.
        * apply: (General.univ_formation i).
          auto.
  Qed.

  Example Ones_wf_guarded `{Γ : ECtx.t Λ Ψ} {k} :
    ⟦ Λ ∣ Γ ≫ BitStream k ∋ Ones ≐ Ones ⟧.
  Proof.
    apply: (Later.induction k).
    - apply: BitStream_wf.
    - apply: (General.replace_ty 0).
      + apply: General.eq_symm.
        apply: BitStream_unfold.
      + apply: Prod.intro.
        * by apply: Bool.tt_equality.
        * by apply: General.hypothesis.
        * by apply: (Bool.univ_eq 0).
        * apply: (Later.univ_eq 0).
          apply: Later.intro.
          ** by apply: BitStream_wf.
          ** by apply: General.univ_formation.
             Unshelve.
             constructor.
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
    apply: General.eq_trans.
    - apply: General.eq_trans.
      + apply: Prod.univ_eq.
        * apply: General.eq_symm.
          apply: Isect.irrelevance.
          apply: Bool.univ_eq.
        * apply: Later.force.
          apply: BitSeq_wf.
      + apply: Isect.preserves_sigma.
        * apply: Bool.univ_eq.
        * apply: Later.univ_eq.
          apply: Later.intro.
          ** by apply: BitStream_wf.
          ** by apply: General.univ_formation.
    - apply: Isect.univ_eq.
      apply: BitStream_unfold.
  Qed.
End Examples.
