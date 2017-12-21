From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8 Program.Equality Program.Basics omega.Omega.
From gctt Require Import Axioms Var Term ExternalSyn Tower Closure Sequent InternalRules.
From gctt Require InternalRules.
Module IR := InternalRules.

Local Hint Extern 40 =>
match goal with
| |- context[(_.⦃_⦄)%ectx] => rewrite -interp_ctx_clk_naturality /compose; simplify_eqs
| |- context[(_.⦃_⦄)%etm] => rewrite -interp_tm_clk_naturality /compose; simplify_eqs
| |- context[(_.[_])%etm] => try rewrite -interp_tm_var_naturality /compose; try rewrite -interp_tm_var_ren_naturality /compose; simplify_eqs
| |- context[(_ ⫽ _)%etm] => Term.simplify_subst
end.

Local Hint Extern 20 => IR.Univ.tac.
Local Hint Resolve IR.General.ty_eq_refl_left IR.General.ty_eq_trans IR.General.ty_eq_symm IR.General.mem_eq_trans IR.General.mem_eq_symm IR.General.env_eq_refl_left IR.General.env_eq_symm.

Tactic Notation "explode" "functionality" uconstr(𝒟) :=
  let X := fresh in
  (have X := (IR.General.functionality_square 𝒟));
  (edestruct X as [? [? ?]]); simpl in *; eauto.

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
  Theorem hypothesis `{Γ : ECtx.t Λ Ψ} {A} :
    ⟦ Λ ∣ Γ ; A ≫ A.[^1] ∋ @0 ≐ @0 ⟧.
  Proof.
    move=> κs Γctx ty γ0 γ1 γ01.
    case: γ01 => [_ γ01].
    auto.
  Qed.

  Theorem conv_mem `{Γ : ECtx.t Λ Ψ} {A e00} e01 {e1} :
    ⟦ Λ ∣ Ψ ⊢ e00 ≃ e01 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e01 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e00 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: IR.General.mem_eq_conv.
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
    apply: IR.General.mem_eq_conv_ty.
    - eauto.
    - move=> ?; edestruct 𝒟; eauto.
    - apply: ℰ; eauto.
      move=> ? ? ?.
      apply: IR.General.ty_eq_conv.
      + eauto.
      + move=> ?; edestruct 𝒟; eassumption.
      + apply: IR.General.ty_eq_symm.
        apply: IR.General.ty_eq_conv.
        * eauto.
        * move=> ?; edestruct 𝒟; eassumption.
        * eauto.
  Qed.

  Theorem eq_symm `{Γ : ECtx.t Λ Ψ} {A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e1 ≐ e0 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01.
    apply: IR.General.mem_eq_symm.
    apply: IR.General.replace_ty_in_mem_eq; eauto.
    apply: 𝒟; eauto.
  Qed.

  Theorem eq_trans `{Γ : ECtx.t Λ Ψ} {A e0 e1 e2} :
    ⟦ Λ ∣ Γ ≫ A ∋ e1 ≐ e2 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e2 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ?.
    apply: IR.General.mem_eq_trans.
    - apply: 𝒟; eauto.
    - apply: ℰ; eauto.
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
    apply: IR.General.replace_ty_in_mem_eq.
    - apply: ℰ; eauto.
      move=> γ0' γ1' γ01'.
      IR.Univ.tac.
      explode functionality (𝒟 _ _ _).
    - IR.Univ.tac.
      apply: 𝒟; auto.
      apply: IR.General.env_eq_refl_left; eassumption.
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
    apply: IR.Univ.intro.
    apply: IR.Univ.formation_lvl.
    assumption.
  Qed.
End General.

Module Unit.
  Theorem ax_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟙 ∋ ★ ≐ ★ ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    apply: IR.Unit.ax_equality.
  Qed.
End Unit.


Module Bool.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ 𝟚 ≐ 𝟚 ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    IR.Bool.tac.
  Qed.

  Theorem tt_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟚 ∋ ETm.tt ≐ ETm.tt ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    IR.Bool.tac.
  Qed.

  Theorem ff_equality `{Γ : ECtx.t Λ Ψ} :
    ⟦ Λ ∣ Γ ≫ 𝟚 ∋ ETm.ff ≐ ETm.ff ⟧.
  Proof.
    move=> ? ? ? ? ? ?.
    IR.Bool.tac.
  Qed.
End Bool.


Module Prod.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1 B0 B1} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (A0 × B0) ≐ (A1 × B1) ⟧.
  Proof.
    move=> 𝒟 ℰ κs Γctx ℱ γ0 γ1 γ01 //=.
    apply: IR.Prod.univ_eq.
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
    apply: IR.Prod.intro.
    - apply: 𝒟; eauto.
      IR.Univ.tac.
      apply: ℱ; eauto.
    - apply: ℰ; eauto.
      IR.Univ.tac.
      apply: 𝒢; eauto.
  Qed.
End Prod.


Module Isect.

  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {A0 A1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A0 ≐ ⋂ A1 ⟧.
  Proof.
    move=> 𝒟 κs Γctx ℰ γ0 γ1 γ01 //=.
    apply: IR.Univ.intro.
    apply: IR.Isect.formation => κ.
    T.efwd 𝒟; eauto.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} i {A e0 e1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ A ∋ (e0.⦃^1⦄) ≐ (e1.⦃^1⦄) ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ⋂ A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℱ κs ? ℰ ? ? ? //=.
    apply: IR.Isect.intro.
    - IR.Univ.tac.
      apply: univ_eq; eauto.
    - move=> κ; T.efwd_thru 𝒟.
      IR.Univ.tac.
      apply: ℱ; eauto.
  Qed.

  Theorem irrelevance `{Γ : ECtx.t Λ Ψ} {i A} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ ⋂ (A.⦃^1⦄) ⟧.
  Proof.
    move=> 𝒟 κs ? ? γ0 γ1 γ01; simplify_eqs.
    replace (λ κ:𝕂, (⟦_.⦃_⦄ ⟧ _) ⫽ _) with (λ κ:𝕂, (⟦A⟧ κs) ⫽ γ1); last by eauto.
    apply: IR.Univ.intro.
    apply: IR.Isect.irrelevance.
    apply: IR.Univ.inversion.
    apply: 𝒟; eauto.
  Qed.

  Theorem cartesian `{Γ : ECtx.t Λ Ψ} i {A0 B0 A1 B1} :
    ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ S Λ ∣ Γ.⦃^1⦄ ≫ 𝕌[i] ∋ B0 ≐ B1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ (⋂ (A0 × B0)) ≐ ((⋂ A0) × (⋂ B0)) ⟧.
  Proof.
    move=> 𝒟 ℰ κs ℱ 𝒢 γ0 γ1 γ01 //=.
    apply: IR.Univ.intro.
    apply: IR.Isect.cartesian => κ;
    apply: IR.Univ.inversion.
    - explode functionality (𝒟 (κ ∷ κs) _ _).
    - explode functionality (ℰ (κ ∷ κs) _ _).
  Qed.
End Isect.

Module Later.
  Theorem univ_eq `{Γ : ECtx.t Λ Ψ} i {k A0 A1} :
    ⟦ Λ ∣ Γ ≫ ▶[k] 𝕌[i] ∋ A0 ≐ A1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ▶[k] A0 ≐ ▶[k] A1 ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? //=.
    apply: IR.Later.univ_eq.
    apply: 𝒟; eauto.

    move=> ? ? ? //=.
    apply: Later.formationω.
    apply: Later.next.
    eauto.
  Qed.

  Theorem intro `{Γ : ECtx.t Λ Ψ} {k i A e0 e1} :
    ⟦ Λ ∣ Γ ≫ A ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ A ≐ A ⟧
    → ⟦ Λ ∣ Γ ≫ ▶[k] A ∋ e0 ≐ e1 ⟧.
  Proof.
    move=> 𝒟 ℰ ? ? ? ? ? ? //=.
    apply: IR.Later.intro.
    apply: Later.next.
    apply: 𝒟; auto.

    IR.Univ.tac.
    apply: ℰ; eauto.
  Qed.

  Theorem force `{Γ : ECtx.t Λ Ψ} {i A B} :
    ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ A ≐ ⋂ B ⟧
    → ⟦ Λ ∣ Γ ≫ 𝕌[i] ∋ ⋂ ▶[#0] A ≐ ⋂ B ⟧.
  Proof.
    move=> 𝒟 ? ? ? ? ? ? //=.
    apply: IR.Univ.intro.
    apply: IR.Later.force.
    IR.Univ.tac.
    apply: 𝒟; eauto.
  Qed.

  Theorem induction `{Γ : ECtx.t Λ Ψ} k {A e0 e1} :
    ⟦ Λ ∣ Γ; ▶[k] A ≫ A.[^1] ∋ e0 ≐ e1 ⟧
    → ⟦ Λ ∣ Γ ≫ A ∋ μ{ e0 } ≐ μ{ e1 } ⟧.
  Proof.
    move=> 𝒟 κs ? ℰ //=.
    apply: (IR.Later.loeb_induction_open (κs k)).
    move=> ? ? ?.
    T.efwd_thru 𝒟.
    - move=> ? ? [? ?].
      T.efwd_thru ℰ.
    - split; auto.
      move=> ? ? ?.
      apply: IR.Later.formationω.
      apply: Later.next.
      auto.
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
          auto.
  Qed.

  Example Ones_wf_guarded `{Γ : ECtx.t Λ Ψ} {k} :
    ⟦ Λ ∣ Γ ≫ BitStream k ∋ Ones ≐ Ones ⟧.
  Proof.
    apply: (Later.induction k).
    apply: (General.replace_ty 0).
    - apply: General.eq_symm.
      apply: BitStream_unfold.
    - apply: Prod.intro.
      + by apply: Bool.tt_equality.
      + by apply: General.hypothesis.
      + by apply: (Bool.univ_eq 0).
      + apply: (Later.univ_eq 0).
        apply: Later.intro.
        * by apply: BitStream_wf.
        * by apply: General.univ_formation.
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