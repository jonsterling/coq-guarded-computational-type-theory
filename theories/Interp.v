Require Import Unicode.Utf8 Program.Equality Program.Tactics Program.Basics Vectors.Fin omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Program Axioms Var Sequent Tower ExternalSyn.
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

Fixpoint interp_tm `(e : EProg.t Λ Ψ) (κs : Env.t Λ) : Prog.t Ψ :=
  match e with
  | EProg.var i => Prog.var i
  | EProg.fst e => ⟦e⟧ κs .1
  | EProg.snd e => ⟦e⟧ κs .2
  | EProg.unit => 𝟙
  | EProg.bool => 𝟚
  | EProg.ax => ★
  | EProg.tt => Prog.tt
  | EProg.ff => Prog.ff
  | EProg.prod A B => ⟦A⟧ κs × ⟦B⟧ κs
  | EProg.arr A B => (⟦A⟧ κs) ⇒ ⟦B⟧ κs
  | EProg.pair A B => ⟨⟦A⟧ κs, ⟦B⟧ κs⟩
  | EProg.ltr r A => ▶[κs r] ⟦A⟧ κs
  | EProg.isect A => ⋂[κ] ⟦A⟧ κ ∷ κs
  | EProg.univ i => 𝕌[i]
  | EProg.fix_ e => 𝛍{⟦e⟧ κs}
  | EProg.lam e => 𝛌{⟦e⟧ κs}
  | EProg.app e1 e2 => ⟦e1⟧ κs ⋅ ⟦e2⟧ κs
  end
where "⟦ e ⟧ κs" := (interp_tm e%etm κs) : prog_scope.

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


Definition interp_subst `(σ : @Sub.t (EProg.t Λ) Ψ0 Ψ1) (κs : Env.t Λ) : @Sub.t Prog.t Ψ0 Ψ1 :=
  fun x =>
    (⟦ σ x ⟧ κs)%prog.

Notation "⟦ σ ⟧ κs" := (interp_subst σ%esubst κs) : subst_scope.

Local Open Scope prog_scope.
Local Open Scope program_scope.

Theorem interp_tm_clk_naturality {Λ1 Λ2 Ψ} (e : EProg.t Λ1 Ψ) (ρ : Ren.t Λ1 Λ2) (κs : Env.t Λ2) :
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

Theorem interp_tm_var_naturality {Λ Ψ0 Ψ1 Ψ2} (e : EProg.t Λ Ψ0) (σ : Sub.t Ψ1 Ψ2) ρ κs :
  (⟦ e ⟧ κs) ⫽ (σ ∘ ρ) = (⟦ e.[ρ] ⟧ κs) ⫽ σ.
Proof.
  move: Ψ1 Ψ2 σ ρ κs.
  induction e; eauto; simpl;
  T.rewrites_with
    ltac:(repeat f_equal;
          try (T.eqcd; intros);
          try rewrite Sub.cong_coh;
          try rewrite Ren.cong_id).
Qed.


Theorem interp_tm_var_ren_naturality {Λ Ψ0 Ψ1} (e : EProg.t Λ Ψ0) (ρ : Ren.t Ψ0 Ψ1) κs :
  (⟦ e ⟧ κs).[ ρ ] = (⟦ e.[ρ] ⟧ κs).
Proof.
  by rewrite
     -(Prog.subst_ret (⟦ e .[ ρ] ⟧ κs))
     -(Prog.subst_ret (⟦ e ⟧ κs .[ρ]))
     Prog.subst_ren_coh
     interp_tm_var_naturality.
Qed.


Lemma interp_subst_cong_coh {Λ Ψ0 Ψ1 Ψ2} (σ01 : @Sub.t (EProg.t Λ) Ψ0 Ψ1) (σ12 : @Sub.t Prog.t Ψ1 Ψ2) (κs : Env.t Λ) :
  (Sub.cong σ12 ◎ ⟦ Sub.cong σ01 ⟧ κs)%subst =
  Sub.cong (σ12 ◎ ⟦ σ01 ⟧ κs)%subst.
Proof.
  T.eqcd => x.
  dependent induction x.
  - eauto.
  - simplify_subst.
    by rewrite -interp_tm_var_naturality.
Qed.

Theorem interp_tm_subst_naturality {Λ Ψ0 Ψ1 Ψ2} (e : EProg.t Λ Ψ0) (σ12 : Sub.t Ψ1 Ψ2) (σ01 : Sub.t Ψ0 Ψ1) κs :
  (⟦ e ⟧ κs) ⫽ (σ12 ◎ ⟦ σ01 ⟧ κs) = (⟦ e ⫽ σ01 ⟧ κs) ⫽ σ12.
Proof.
  symmetry.
  move: Ψ1 Ψ2 σ01 σ12 κs.
  induction e; eauto; simpl;
  T.rewrites_with
    ltac:(repeat f_equal; try (T.eqcd; intros);
          try rewrite /interp_subst /EProg.wk_sub;
          try rewrite interp_subst_cong_coh;
          Program.simplify_subst;
          try rewrite -interp_tm_clk_naturality).
Qed.

Theorem interp_tm_ren_naturality {Λ0 Λ1 Ψ0 Ψ1 Ψ2} (e : EProg.t Λ0 Ψ0) (ρΛ : Ren.t Λ0 Λ1) (ρΨ : Ren.t Ψ0 Ψ1) (σ : Sub.t Ψ1 Ψ2) κs :
  (⟦ e ⟧ κs ∘ ρΛ) ⫽ (σ ∘ ρΨ) = (⟦ e.⦃ρΛ⦄[ρΨ] ⟧ κs) ⫽ σ.
Proof.
  symmetry.
  move: Ψ1 Ψ2 σ Λ1 ρΨ ρΛ κs.
  induction e; eauto; simpl;

  T.rewrites_with
    ltac:(repeat f_equal; try (T.eqcd; intros);
          try rewrite /EProg.wk_sub;
          try rewrite interp_subst_cong_coh;
          simplify_subst;
          try rewrite -interp_tm_clk_naturality;
          try rewrite -Sub.cong_coh_ptwise).

  by dependent induction x0.
Qed.

Local Close Scope prog_scope.
