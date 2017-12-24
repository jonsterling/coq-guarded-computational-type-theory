Require Import Unicode.Utf8 Program.Equality Program.Tactics Program.Basics Vectors.Fin omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Term Axioms Var Sequent Tower ExternalSyn.
From gctt Require Tactic.
Module T := Tactic.

Generalizable All Variables.
Set Implicit Arguments.

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

Reserved Notation "⟦ e ⟧ κs" (at level 50).

Fixpoint interp_tm `(e : ETm.t Λ Ψ) (κs : Env.t Λ) : Tm.t Ψ :=
  match e with
  | ETm.var i => Tm.var i
  | ETm.fst e => ⟦e⟧ κs .1
  | ETm.snd e => ⟦e⟧ κs .2
  | ETm.unit => 𝟙
  | ETm.bool => 𝟚
  | ETm.ax => ★
  | ETm.tt => Tm.tt
  | ETm.ff => Tm.ff
  | ETm.prod A B => ⟦A⟧ κs × ⟦B⟧ κs
  | ETm.arr A B => (⟦A⟧ κs) ⇒ ⟦B⟧ κs
  | ETm.pair A B => ⟨⟦A⟧ κs, ⟦B⟧ κs⟩
  | ETm.ltr r A => ▶[κs r] ⟦A⟧ κs
  | ETm.isect A => ⋂[κ] ⟦A⟧ κ ∷ κs
  | ETm.univ i => 𝕌[i]
  | ETm.fix_ e => Tm.fix_ (⟦e⟧ κs)
  end
where "⟦ e ⟧ κs" := (interp_tm e%etm κs) : tm_scope.

Arguments interp_tm [Λ Ψ] e%etm κs.

Program Fixpoint interp_ctx `(Γ : ECtx.t Λ Ψ) (κs : Env.t Λ) : Prectx Ψ :=
  match Γ with
  | ⋄%ectx => ⋄%ictx
  | (Γ ∙ A)%ectx => (⟦ Γ ⟧ κs ∙ ⟦ A ⟧ κs)%ictx
  end
where "⟦ Γ ⟧ κs" := (interp_ctx Γ%ectx κs) : ctx_scope.

Arguments interp_ctx [Λ Ψ] Γ%ectx κs.

Definition interp_jdg `(J : EJdg.t Λ) : Ω :=
  ∀ κs,
    match J with
    | ⌊ _ ∣ Γ ≫ A ∋ e1 ≐ e2 ⌋ =>
      τω ⊧ ⟦ Γ ⟧ κs ctx
      → (τω ⊧ ⟦ Γ ⟧ κs ≫ ⟦ A ⟧ κs ∼ ⟦ A ⟧ κs)
      → τω ⊧ ⟦ Γ ⟧ κs ≫ ⟦ A ⟧ κs ∋ ⟦ e1 ⟧ κs ∼ ⟦ e2 ⟧ κs
    | ⌊ _ ∣ Ψ ⊢ e1 ≃ e2 ⌋ =>
      (⟦ e1 ⟧ κs) ≈ (⟦ e2 ⟧ κs)
    end.

Arguments interp_jdg [Λ] J%ejdg.
Notation "⟦ J ⟧" := (interp_jdg J%ejdg) (at level 50) : type_scope.

Local Open Scope tm_scope.
Local Open Scope program_scope.

Theorem interp_tm_clk_naturality {Λ1 Λ2 Ψ} (e : ETm.t Λ1 Ψ) (ρ : Ren.t Λ1 Λ2) (κs : Env.t Λ2) :
  ⟦ e ⟧ κs ∘ ρ = ⟦ e.⦃ρ⦄ ⟧ κs.
Proof.
  move: Λ2 ρ κs; elim e => *;
  T.rewrites_with ltac:(try rewrite Ren.cong_id).

  repeat f_equal; T.eqcd => *.
  match goal with
  | x : _ |- _ => rewrite -x
  end.

  f_equal.
  T.eqcd => x.
  by dependent induction x.
Qed.

Theorem interp_ctx_clk_naturality {Λ1 Λ2 Ψ} (Γ : ECtx.t Λ1 Ψ) (ρ : Ren.t Λ1 Λ2) (κs : Env.t Λ2) :
  (⟦ Γ ⟧ κs ∘ ρ)%ictx = (⟦ Γ.⦃ρ⦄ ⟧ κs)%ictx.
Proof.
  induction Γ; simpl; auto.
  rewrite interp_tm_clk_naturality.
  T.rewrites.
Qed.

Theorem interp_tm_var_naturality {Λ Ψ0 Ψ1 Ψ2} (e : ETm.t Λ Ψ0) (γ : Sub.t Ψ1 Ψ2) ρ κs :
  (⟦ e ⟧ κs) ⫽ (γ ∘ ρ) = (⟦ e.[ρ] ⟧ κs) ⫽ γ.
Proof.
  move: Ψ1 Ψ2 γ ρ κs.
  induction e; eauto; simpl;
  T.rewrites_with
    ltac:(repeat f_equal;
          try (T.eqcd; intros);
          try rewrite Sub.cong_coh;
          try rewrite Ren.cong_id).
Qed.


Theorem interp_tm_var_ren_naturality {Λ Ψ0 Ψ1} (e : ETm.t Λ Ψ0) (ρ : Ren.t Ψ0 Ψ1) κs :
  (⟦ e ⟧ κs).[ ρ ] = (⟦ e.[ρ] ⟧ κs).
Proof.
  by rewrite
     -(Tm.subst_ret (⟦ e .[ ρ] ⟧ κs))
     -(Tm.subst_ret (⟦ e ⟧ κs .[ρ]))
     Tm.subst_ren_coh
     interp_tm_var_naturality.
Qed.

Lemma interp_subst_cong_coh {Λ Ψ0 Ψ1 Ψ2} (σ01 : Sub.t Ψ0 Ψ1) (σ12 : Sub.t Ψ1 Ψ2) (κs : Env.t Λ) :
  Tm.subst (Sub.cong σ12) ∘ (λ x, ⟦ Sub.cong σ01 x ⟧ κs) =
  Sub.cong (Tm.subst σ12 ∘ (λ x, ⟦ σ01 x ⟧ κs)).
Proof.
  T.eqcd => x.
  dependent induction x.
  - eauto.
  - Term.simplify_subst.
    by rewrite -interp_tm_var_naturality.
Qed.

Theorem interp_tm_subst_naturality {Λ Ψ0 Ψ1 Ψ2} (e : ETm.t Λ Ψ0) (σ12 : Sub.t Ψ1 Ψ2) (σ01 : Sub.t Ψ0 Ψ1) κs :
  (⟦ e ⟧ κs) ⫽ (Tm.subst σ12 ∘ (fun x => ⟦ σ01 x ⟧ κs)) = (⟦ e ⫽ σ01 ⟧ κs) ⫽ σ12.
Proof.
  symmetry.
  move: Ψ1 Ψ2 σ01 σ12 κs.
  induction e; eauto; simpl;
  T.rewrites_with
    ltac:(repeat f_equal; try (T.eqcd; intros);
          try rewrite /ETm.wk_sub;
          try rewrite interp_subst_cong_coh;
          Term.simplify_subst;
          try rewrite -interp_tm_clk_naturality).
Qed.

Theorem interp_tm_ren_naturality {Λ0 Λ1 Ψ0 Ψ1 Ψ2} (e : ETm.t Λ0 Ψ0) (ρΛ : Ren.t Λ0 Λ1) (ρΨ : Ren.t Ψ0 Ψ1) (σ : Sub.t Ψ1 Ψ2) κs :
  (⟦ e ⟧ κs ∘ ρΛ) ⫽ (σ ∘ ρΨ) = (⟦ ETm.map ρΛ ρΨ e ⟧ κs) ⫽ σ.
Proof.
  symmetry.
  move: Ψ1 Ψ2 σ Λ1 ρΨ ρΛ κs.
  induction e; eauto; simpl;

  T.rewrites_with
    ltac:(repeat f_equal; try (T.eqcd; intros);
          try rewrite /ETm.wk_sub;
          try rewrite interp_subst_cong_coh;
          Term.simplify_subst;
          try rewrite -interp_tm_clk_naturality;
          try rewrite -Sub.cong_coh_ptwise).

  by dependent induction x0.
Qed.

Local Close Scope tm_scope.
