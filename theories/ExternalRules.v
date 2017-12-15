From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Unicode.Utf8.
Require Import Program.Equality.

From gctt Require Import Axioms Var Term ExternalSyn Tower Closure Sequent InternalRules.
From gctt Require InternalRules.
Module IR := InternalRules.

Theorem open_clock_irrelevance Λ Ψ Γ (A : ETm.t Λ Ψ) :
  J⟦ ⌊ Λ ∣ Γ ≫ A ≐ A ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A ≐ ETm.isect (ETm.mapk (Ren.weak 1) A) ⌋ ⟧.
Proof.
  move=> D κs Γctx γ0 γ1 γ01;
  specialize (D κs Γctx γ0 γ1 γ01).

  have : (λ κ : CLK, (T⟦ ETm.mapk (Ren.weak 1) A ⟧ κ ∷ κs) ⫽ γ1 ) = (λ κ, (T⟦A⟧ κs) ⫽ γ1).
  + T.eqcd => *.
    rewrite -interp_tm_clk_naturality;
    by simplify_eqs.
  + simplify_eqs; T.rewrite_;
    eauto.
Qed.

Theorem open_ax_equality Λ Ψ (Γ : ECtx.t Λ Ψ) :
  J⟦ ⌊ Λ ∣ Γ ≫ ETm.unit ∋ ETm.ax ≐ ETm.ax ⌋ ⟧.
Proof.
  move=> κs Γctx unit_ty γ0 γ1 γ01.
  unshelve eauto.
  exact 0.
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


Example conv_test Λ Ψ :
  J⟦ ⌊ Λ ∣ Ψ ⊢ ETm.fst (ETm.pair ETm.tt ETm.ff) ≃ ETm.snd (ETm.pair ETm.ff ETm.tt) ⌋ ⟧.
Proof.
  move=> κs γ v //=.
  split => D.
  + have: v = Tm.tt.
    ++ apply: determinacy; eauto.
    ++ T.rewrite_; eauto.
  + have: v = Tm.tt.
    ++ apply: determinacy; eauto.
    ++ T.rewrite_; eauto.
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
  move=> 𝒟 ℰ κs Γctx γ0 γ1 γ01.
  specialize (𝒟 κs γ0).
  case: (ℰ κs Γctx γ0 γ1 γ01) => R [X1 X2].
  exists R; split.
  - case: X1 => [n X1].
    rewrite /Tower.t in X1.
    Clo.destruct_clo.
    + induction n; Spine.simplify.
      * done.
      * case: H => [j H].
        T.destruct_conjs.
        simpl in *.
        exists (S n).
        rewrite /Tower.t -Clo.roll.
        apply: Sig.init.
        Spine.simplify.
        exists j; repeat T.split; auto.
        edestruct 𝒟; auto.
    + exists n; rewrite /Tower.t -Clo.roll.
      apply: Sig.conn; eauto.
      edestruct 𝒟.
      Clo.destruct_has; eauto.
  - auto.
Qed.


Theorem ty_eq_sym `{Γ : ECtx.t Λ Ψ} {A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ≐ A0 ⌋ ⟧.
  move=> 𝒟 κs Γctx γ0 γ1 γ01.
  specialize (𝒟 κs Γctx).
  apply: IR.ty_eq_symm.
  move: (𝒟 γ0 γ1 γ01) => [R01 [[? ?] [? ?]]].
  move: (𝒟 γ0 γ0 (IR.env_eq_refl_left Γctx γ01)) => [R00 [[? ?] [? ?]]].
  move: (𝒟 γ1 γ0 (IR.env_eq_sym Γctx γ01)) => [R10 [[? ?] [? ?]]].
  IR.Tac.accum_lvl n.
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ0, R01)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ1, R01)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ1, R10)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ0, R10)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ0, R00)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ0, R00)); [by IR.Tac.tower_mono|].

  exists R00; replace R00 with R10.
  - T.split; by [exists n].
  - apply: Tower.extensionality; eauto.
Qed.

Theorem ty_eq_trans `{Γ : ECtx.t Λ Ψ} {A0 A1 A2} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ≐ A2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A2 ⌋ ⟧.
Proof.
  move=> 𝒟 ℰ κs Γctx γ0 γ1 γ01.
  specialize (𝒟 κs Γctx).
  specialize (ℰ κs Γctx γ0 γ1 γ01).
  move: (𝒟 γ0 γ1 γ01) => [R01 [[? ?] [? ?]]].
  move: (𝒟 γ0 γ0 (IR.env_eq_refl_left Γctx γ01)) => [R00 [[? ?] [? ?]]].
  move: (𝒟 γ1 γ0 (IR.env_eq_sym Γctx γ01)) => [R10 [[? ?] [? ?]]].
  IR.Tac.accum_lvl n.
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ0, R01)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ1, R01)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ1, R10)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ0, R10)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A1 ⟧ κs) ⫽ γ0, R00)); [by IR.Tac.tower_mono|].
  (have ? : τ[n] ((T⟦ A0 ⟧ κs) ⫽ γ0, R00)); [by IR.Tac.tower_mono|].

  apply: IR.ty_eq_trans; first by [eauto]; exists R00.
  replace R00 with R10; last by [apply: Tower.extensionality; eauto].
  T.split; exists n; last by [eauto].
  replace R10 with R01; first by [eauto].
  transitivity R00; symmetry;
  apply: Tower.extensionality; eauto.
Qed.


Theorem ty_eq_refl_left `{Γ : ECtx.t Λ Ψ} {A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A0 ⌋ ⟧.
Proof.
  move=> 𝒟.
  apply: ty_eq_trans.
  - eassumption.
  - by apply: ty_eq_sym.
Qed.

Theorem rewrite_ty_in_mem `{Γ : ECtx.t Λ Ψ} {A0 A1 e1 e2} :
  J⟦ ⌊ Λ ∣ Γ ≫ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A0 ∋ e1 ≐ e2 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ A1 ∋ e1 ≐ e2⌋ ⟧.
Proof.
  move=> 𝒟 ℰ κs Γctx ℱ γ0 γ1 γ01.
  specialize (ℰ κs Γctx (ty_eq_refl_left 𝒟 κs Γctx) γ0 γ1 γ01).
  specialize (𝒟 κs Γctx γ0 γ1 γ01).
  specialize (ℱ γ0 γ1 γ01).
  eauto.
Qed.

Theorem later_mem_univ `{Γ : ECtx.t Λ Ψ} {k i A0 A1} :
  J⟦ ⌊ Λ ∣ Γ ≫ ETm.ltr k (ETm.univ i) ∋ A0 ≐ A1 ⌋ ⟧
  → J⟦ ⌊ Λ ∣ Γ ≫ ETm.univ i ∋ (ETm.ltr k A0) ≐ (ETm.ltr k A1) ⌋ ⟧.
Proof.
  move=> 𝒟 κs Γctx ℱ γ0 γ1 γ01. simpl in *.
  suff: τω ⊧ Γ⟦ Γ ⟧ κs ≫ Tm.ltr (κs k) (Tm.univ i) ∼ (Tm.ltr (κs k) (Tm.univ i)).
  - move=> ℰ.
    specialize (𝒟 κs Γctx ℰ γ0 γ1 γ01).
    eauto.
  - move=> ? ? ? //=.
    apply: IR.later_formation.
    apply: Later.next.
    eauto.
Qed.
