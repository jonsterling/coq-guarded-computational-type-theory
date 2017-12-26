Require Import Unicode.Utf8 Program.Equality Program.Tactics Program.Basics Vectors.Fin omega.Omega.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Term Axioms Var Sequent Tower.
From gctt Require Tactic.
Module T := Tactic.

Generalizable All Variables.
Set Implicit Arguments.


Delimit Scope eclk_scope with eclk.
Delimit Scope etm_scope with etm.
Delimit Scope esubst_scope with esubst.


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
  | prod : t Λ Ψ -> t Λ (S Ψ) -> t Λ Ψ
  | arr : t Λ Ψ -> t Λ (S Ψ) -> t Λ Ψ
  | pair : t Λ Ψ -> t Λ Ψ -> t Λ Ψ
  | ltr : Var Λ → t Λ Ψ -> t Λ Ψ
  | isect : t (S Λ) Ψ -> t Λ Ψ
  | univ : nat -> t Λ Ψ
  | fix_ : t Λ (S Ψ) → t Λ Ψ.

  Arguments unit [Λ Ψ].
  Arguments bool [Λ Ψ].
  Arguments ax [Λ Ψ].
  Arguments tt [Λ Ψ].
  Arguments ff [Λ Ψ].
  Arguments univ [Λ Ψ] i.

  Module Notation.
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
    Infix "⇒" := ETm.arr : etm_scope.
    Notation "⋂ A" := (ETm.isect A%etm) (at level 50) : etm_scope.
    Notation "𝕌[ i ] " := (ETm.univ i%nat) : etm_scope.
    Notation "⟨ e1 , e2 ⟩" := (ETm.pair e1%etm e2%etm) : etm_scope.
    Notation "μ{ e }" := (ETm.fix_ e%etm) (at level 50) : etm_scope.
  End Notation.

  Import Notation.

  Fixpoint map `(ρΛ : Ren.t Λ1 Λ2) `(ρΨ : Ren.t Ψ1 Ψ2) (e : t Λ1 Ψ1) : t Λ2 Ψ2 :=
    match e with
    | var i => var _ (ρΨ i)
    | fst e => fst (map ρΛ ρΨ e)
    | snd e => snd (map ρΛ ρΨ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρΛ ρΨ A) (map ρΛ (Ren.cong ρΨ) B)
    | arr A B => arr (map ρΛ ρΨ A) (map ρΛ (Ren.cong ρΨ) B)
    | pair e1 e2 => pair (map ρΛ ρΨ e1) (map ρΛ ρΨ e2)
    | ltr k A => ltr (ρΛ k) (map ρΛ ρΨ A)
    | isect A => isect (map (Ren.cong ρΛ) ρΨ A)
    | univ i => univ i
    | fix_ e => fix_ (map ρΛ (Ren.cong ρΨ) e)
    end.

  Definition mapv {Λ} `(ρΨ : Ren.t Ψ1 Ψ2) : t Λ Ψ1 → t Λ Ψ2 :=
    map (λ x, x) ρΨ.

  Definition mapk {Λ1 Λ2 Ψ} (ρ : Ren.t Λ1 Λ2) : t Λ1 Ψ → t Λ2 Ψ :=
    map ρ (λ x, x).

  Module RenNotation.
    Notation "e .[ ρ ]" := (mapv ρ%ren e) (at level 50) : etm_scope.
    Notation "e .⦃ ρ ⦄" := (mapk ρ%ren e) (at level 50) : etm_scope.
    Notation "e .⦃ ρΛ ⦄[ ρΨ ]" := (map ρΛ%ren ρΨ e) (at level 50) : etm_scope.
  End RenNotation.

  Import RenNotation.

  Lemma map_id `(e : t Λ Ψ) : map id id e = e.
  Proof.
    induction e; T.rewrites_with ltac:(try rewrite Ren.cong_id).
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

  Fixpoint subst {Λ} `(σ : Sub.t Ψ1 Ψ2) (e : t Λ Ψ1) : t Λ Ψ2 :=
    match e with
    | var i => σ i
    | fst e => fst (subst σ e)
    | snd e => snd (subst σ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst (Sub.cong σ) B)
    | arr A B => arr (subst σ A) (subst (Sub.cong σ) B)
    | pair e1 e2 => pair (subst σ e1) (subst σ e2)
    | ltr k A => ltr k (subst σ A)
    | isect A => isect (subst (wk_sub σ) A)
    | univ i => univ i
    | fix_ e => fix_ (subst (Sub.cong σ) e)
    end.

  Module SubstNotation.
    Notation "e ⫽ σ" := (subst σ%subst e%etm) (at level 20, left associativity) : etm_scope.
  End SubstNotation.

  Import SubstNotation.
End ETm.

Export ETm.Notation ETm.RenNotation ETm.SubstNotation.

Delimit Scope ectx_scope with ectx.

Module ECtx.
  Inductive t (Λ : Var.Ctx) : Var.Ctx → Type :=
  | nil : t Λ 0
  | snoc : ∀ {Ψ}, t Λ Ψ → ETm.t Λ Ψ → t Λ (S Ψ).

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
  | eq_mem : ∀ {Ψ}, ECtx.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ
  | conv : ∀ {Ψ}, ETm.t Λ Ψ → ETm.t Λ Ψ → t Λ.

  Arguments eq_mem [Λ Ψ] Γ%ectx A%etm e1%etm e2%etm.
  Arguments conv [Λ Ψ] e1%etm e2%etm.
End EJdg.


Delimit Scope ejdg_scope with ejdg.

Notation "Λ ∣ Γ ≫ A ∋ e1 ≐ e2" := (@EJdg.eq_mem Λ _ Γ%ectx A%etm e1%etm e2%etm) (at level 10) : ejdg_scope.
Notation "Λ ∣ Ψ ⊢ e1 ≃ e2" := (@EJdg.conv Λ Ψ e1%etm e2%etm) (at level 10) : ejdg_scope.

Notation "⌊ 𝒥 ⌋" := 𝒥%ejdg (only parsing).
