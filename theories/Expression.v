Require Import Unicode.Utf8 Program.Equality Program.Tactics Program.Basics Vectors.Fin omega.Omega.

Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Program Axioms Var Sequent Tower.
From gctt Require Tactic.
Module T := Tactic.

Generalizable All Variables.
Set Implicit Arguments.


Delimit Scope eclk_scope with eclk.
Delimit Scope etm_scope with etm.
Delimit Scope esubst_scope with esubst.


Module Expr.
  Inductive t (Λ Ψ : nat) :=
  | var : Var Ψ -> t Λ Ψ
  | fst : t Λ Ψ -> t Λ Ψ
  | snd : t Λ Ψ → t Λ Ψ
  | void : t Λ Ψ
  | unit : t Λ Ψ
  | bool : t Λ Ψ
  | ax : t Λ Ψ
  | tt : t Λ Ψ
  | ff : t Λ Ψ
  | prod : t Λ Ψ -> t Λ (S Ψ) -> t Λ Ψ
  | arr : t Λ Ψ -> t Λ (S Ψ) -> t Λ Ψ
  | pair : t Λ Ψ -> t Λ Ψ -> t Λ Ψ
  | ltr : Var Λ → t Λ Ψ -> t Λ Ψ
  | isect : t (S Λ) Ψ -> t Λ Ψ
  | univ : nat -> t Λ Ψ
  | lam : t Λ (S Ψ) → t Λ Ψ
  | fix_ : t Λ (S Ψ) → t Λ Ψ
  | app : t Λ Ψ → t Λ Ψ → t Λ Ψ.

  Arguments void [Λ Ψ].
  Arguments unit [Λ Ψ].
  Arguments bool [Λ Ψ].
  Arguments ax [Λ Ψ].
  Arguments tt [Λ Ψ].
  Arguments ff [Λ Ψ].
  Arguments univ [Λ Ψ] i.

  Module Notation.
    Notation "#0" := Fin.F1 : eclk_scope.
    Notation "#1" := (Fin.FS Fin.F1) : eclk_scope.

    Notation "@0" := (Expr.var _ Fin.F1) : etm_scope.
    Notation "@1" := (Expr.var _ (Fin.FS Fin.F1)) : etm_scope.

    Notation "▶[ k ] A" := (Expr.ltr k%eclk A%etm) (at level 50) : etm_scope.
    Notation "𝟘" := Expr.unit : etm_scope.
    Notation "𝟙" := Expr.unit : etm_scope.
    Notation "𝟚" := Expr.bool : etm_scope.
    Notation "★" := Expr.ax : etm_scope.
    Notation "M .1" := (Expr.fst M%etm) (at level 50) : etm_scope.
    Notation "M .2" := (Expr.snd M%etm) (at level 50) : etm_scope.
    Infix "×" := Expr.prod : etm_scope.
    Infix "⇒" := Expr.arr : etm_scope.
    Notation "⋂ A" := (Expr.isect A%etm) (at level 50) : etm_scope.
    Notation "𝕌[ i ] " := (Expr.univ i%nat) : etm_scope.
    Notation "⟨ M1 , M2 ⟩" := (Expr.pair M1%etm M2%etm) : etm_scope.
    Notation "'μ{' M }" := (Expr.fix_ M%etm) (at level 50) : etm_scope.
    Notation "'𝛌{' M }" := (Expr.lam M%etm) (at level 50) : etm_scope.
    Notation "M1 ⋅ M2" := (Expr.app M1%etm M2%etm) (at level 50) : etm_scope.
  End Notation.

  Import Notation.

  Fixpoint map `(ρΛ : Ren.t Λ1 Λ2) `(ρΨ : Ren.t Ψ1 Ψ2) (M : t Λ1 Ψ1) : t Λ2 Ψ2 :=
    match M with
    | var _ i => var _ (ρΨ i)
    | fst M => fst (map ρΛ ρΨ M)
    | snd M => snd (map ρΛ ρΨ M)
    | void => void
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρΛ ρΨ A) (map ρΛ (Ren.cong ρΨ) B)
    | arr A B => arr (map ρΛ ρΨ A) (map ρΛ (Ren.cong ρΨ) B)
    | pair M1 M2 => pair (map ρΛ ρΨ M1) (map ρΛ ρΨ M2)
    | ltr k A => ltr (ρΛ k) (map ρΛ ρΨ A)
    | isect A => isect (map (Ren.cong ρΛ) ρΨ A)
    | univ i => univ i
    | fix_ M => fix_ (map ρΛ (Ren.cong ρΨ) M)
    | lam M => lam (map ρΛ (Ren.cong ρΨ) M)
    | app M1 M2 => app (map ρΛ ρΨ M1) (map ρΛ ρΨ M2)
    end.

  Definition mapv {Λ} `(ρΨ : Ren.t Ψ1 Ψ2) : t Λ Ψ1 → t Λ Ψ2 :=
    map (λ x, x) ρΨ.

  Definition mapk {Λ1 Λ2 Ψ} (ρ : Ren.t Λ1 Λ2) : t Λ1 Ψ → t Λ2 Ψ :=
    map ρ (λ x, x).

  Module RenNotation.
    Notation "M .[ ρ ]" := (mapv ρ%ren M) (at level 50) : etm_scope.
    Notation "M .⦃ ρ ⦄" := (mapk ρ%ren M) (at level 50) : etm_scope.
    Notation "M .⦃ ρΛ ⦄[ ρΨ ]" := (map ρΛ%ren ρΨ M) (at level 50) : etm_scope.
  End RenNotation.

  Import RenNotation.

  Lemma map_id `(M : t Λ Ψ) : map id id M = M.
  Proof.
    induction M; T.rewrites_with ltac:(try rewrite Ren.cong_id).
  Qed.

  Program Instance syn_struct_term {Λ} : Sub.syn_struct (t Λ) :=
    {| Sub.var := @var Λ;
       Sub.map := @map Λ Λ id
    |}.
  Next Obligation.
    apply: map_id.
  Qed.

  Local Open Scope program_scope.
  Program Definition wk_sub `(σ : @Sub.t (t Λ) Ψ1 Ψ2) : @Sub.t (t (S Λ)) Ψ1 Ψ2 :=
    mapk (^1)%ren ∘ σ.

  Fixpoint subst {Λ} `(σ : Sub.t Ψ1 Ψ2) (M : t Λ Ψ1) : t Λ Ψ2 :=
    match M with
    | var _ i => σ i
    | fst M => fst (subst σ M)
    | snd M => snd (subst σ M)
    | void => void
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst (Sub.cong σ) B)
    | arr A B => arr (subst σ A) (subst (Sub.cong σ) B)
    | pair M1 M2 => pair (subst σ M1) (subst σ M2)
    | ltr k A => ltr k (subst σ A)
    | isect A => isect (subst (wk_sub σ) A)
    | univ i => univ i
    | fix_ M => fix_ (subst (Sub.cong σ) M)
    | lam M => lam (subst (Sub.cong σ) M)
    | app M1 M2 => app (subst σ M1) (subst σ M2)
    end.

  Module SubstNotation.
    Notation "M ⫽ σ" := (subst σ%subst M%etm) (at level 20, left associativity) : etm_scope.
  End SubstNotation.

  Import SubstNotation.
End Expr.

Export Expr.Notation Expr.RenNotation Expr.SubstNotation.

Delimit Scope ectx_scope with ectx.

Module ECtx.
  Inductive t (Λ : Var.Ctx) : Var.Ctx → Type :=
  | nil : t Λ 0
  | snoc : ∀ {Ψ}, t Λ Ψ → Expr.t Λ Ψ → t Λ (S Ψ).

  Arguments nil [Λ].
  Arguments snoc [Λ Ψ] Γ%ectx A%etm.

  Module Notation.
    Notation "⋄" := nil : ectx_scope.
    Notation "Γ ∙ A" := (@snoc _ _ Γ%ectx A%etm) (at level 50, left associativity) : ectx_scope.
  End Notation.

  Import Notation.

  Fixpoint map {Λ1 Λ2 Ψ} (ρ : Ren.t Λ1 Λ2) (Γ : t Λ1 Ψ) : t Λ2 Ψ :=
    match Γ with
    | ⋄%ectx => nil
    | (Γ∙A)%ectx => (map ρ Γ ∙ (A.⦃ρ⦄))%ectx
    end.
End ECtx.

Export ECtx.Notation.

Notation "Γ .⦃ ρ ⦄" := (ECtx.map ρ%ren Γ%ectx) (at level 50) : ectx_scope.

Module EJdg.
  Inductive t Λ :=
  | eq_mem : ∀ {Ψ}, ECtx.t Λ Ψ → Expr.t Λ Ψ → Expr.t Λ Ψ → Expr.t Λ Ψ → t Λ
  | conv : ∀ {Ψ}, Expr.t Λ Ψ → Expr.t Λ Ψ → t Λ.

  Arguments eq_mem [Λ Ψ] Γ%ectx A%etm M1%etm M2%etm.
  Arguments conv [Λ Ψ] M1%etm M2%etm.
End EJdg.


Delimit Scope ejdg_scope with ejdg.

Notation "Λ ∣ Γ ≫ A ∋ M1 ≐ M2" := (@EJdg.eq_mem Λ _ Γ%ectx A%etm M1%etm M2%etm) (at level 10) : ejdg_scope.
Notation "Λ ∣ Ψ ⊢ M1 ≃ M2" := (@EJdg.conv Λ Ψ M1%etm M2%etm) (at level 10) : ejdg_scope.

Notation "⌊ 𝒥 ⌋" := 𝒥%ejdg (only parsing).
