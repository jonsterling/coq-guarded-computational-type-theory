Require Import Unicode.Utf8 Program.
From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Axioms Var.
From gctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.
Delimit Scope tm_scope with tm.

Module Tm.
  Inductive t (Ψ : Ctx) :=
  | var : Var Ψ -> t Ψ
  | fst : t Ψ -> t Ψ
  | snd : t Ψ → t Ψ
  | app : t Ψ → t Ψ → t Ψ
  | unit : t Ψ
  | bool : t Ψ
  | ax : t Ψ
  | tt : t Ψ
  | ff : t Ψ
  | prod : t Ψ -> t (S Ψ) -> t Ψ
  | arr : t Ψ -> t Ψ -> t Ψ
  | pair : t Ψ -> t Ψ -> t Ψ
  | lam : t (S Ψ) → t Ψ
  | ltr : 𝕂 -> t Ψ -> t Ψ
  | isect : (𝕂 → t Ψ) → t Ψ
  | univ : nat -> t Ψ
  | fix_ : t (S Ψ) → t Ψ.

  Arguments unit [Ψ].
  Arguments bool [Ψ].
  Arguments ax [Ψ].
  Arguments tt [Ψ].
  Arguments ff [Ψ].
  Arguments univ [Ψ] i.


  Module Notations.
    Notation "@0" := (Tm.var Fin.F1) : tm_scope.
    Notation "@1" := (Tm.var (Fin.FS Fin.F1)) : tm_scope.
    Notation "▶[ κ ] A" := (Tm.ltr κ A%tm) (at level 50) : tm_scope.
    Notation "'𝟚'" := Tm.bool : tm_scope.
    Notation "'𝟙'" := Tm.unit : tm_scope.
    Notation "★" := Tm.ax : tm_scope.
    Notation "e .1" := (Tm.fst e%tm) (at level 50) : tm_scope.
    Notation "e .2" := (Tm.snd e%tm) (at level 50) : tm_scope.
    Infix "×" := Tm.prod : tm_scope.
    Infix "⇒" := Tm.arr (at level 30) : tm_scope.
    Notation "⋂[ κ ] A" := (Tm.isect (fun κ => A%tm)) (at level 50) : tm_scope.
    Notation "⋂ A" := (Tm.isect A) (at level 50) : tm_scope.
    Notation "𝕌[ i ] " := (Tm.univ i%nat) : tm_scope.
    Notation "⟨ e1 , e2 ⟩" := (Tm.pair e1%tm e2%tm) : tm_scope.
    Notation "e1 ⋅ e2" := (Tm.app e1%tm e2%tm) (at level 50) : tm_scope.
    Notation "'𝛌{' e }" := (Tm.lam e%tm) (at level 50) : tm_scope.
  End Notations.

  Import Notations.

  Program Fixpoint map {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => var (ρ i)
    | fst e => fst (map ρ e)
    | snd e => snd (map ρ e)
    | app e1 e2 => app (map ρ e1) (map ρ e2)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρ A) (map (Ren.cong ρ) B)
    | arr A B => arr (map ρ A) (map ρ B)
    | pair e1 e2 => pair (map ρ e1) (map ρ e2)
    | lam e => lam (map (Ren.cong ρ) e)
    | ltr κ A => ltr κ (map ρ A)
    | isect A => isect (fun κ => map ρ (A κ))
    | univ i => univ i
    | fix_ e => fix_ (map (Ren.cong ρ) e)
    end.

  Program Instance syn_struct_term : Sub.syn_struct t :=
    {| Sub.var := var;
       Sub.map := @map |}.

  Module RenNotation.
    Notation "e .[ ρ ]" := (Tm.map ρ%ren e) (at level 50) : tm_scope.
  End RenNotation.

  Import RenNotation.

  Local Ltac rewrites_aux :=
    repeat f_equal;
    try (let x := fresh in T.eqcd => x);
    try (rewrite Ren.cong_id).

  Local Ltac rewrites :=
    T.rewrites_with rewrites_aux.

  Theorem map_id {Ψ} (e : t Ψ) : map id e = e.
  Proof.
    induction e; by rewrites.
  Qed.


  Program Fixpoint subst {Ψ1 Ψ2} (σ : Sub.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => σ i
    | fst e => fst (subst σ e)
    | snd e => snd (subst σ e)
    | app e1 e2 => app (subst σ e1) (subst σ e2)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst (Sub.cong σ) B)
    | arr A B => arr (subst σ A) (subst σ B)
    | pair e1 e2 => pair (subst σ e1) (subst σ e2)
    | lam e => lam (subst (Sub.cong σ) e)
    | ltr κ A => ltr κ (subst σ A)
    | isect A => isect (fun κ => subst σ (A κ))
    | univ i => univ i
    | fix_ e => fix_ (subst (Sub.cong σ) e)
    end.

  Module SubstNotation.
    Notation "e ⫽ σ" := (Tm.subst σ e%tm) (at level 20, left associativity).
  End SubstNotation.

  Import SubstNotation.

  (* TODO: make this part of the syntax-structure type class *)
  Theorem ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) (e : t _) :
    e.[ρ12].[ρ23]%tm
    =
    e.[ρ23 ∘ ρ12]%tm.
  Proof.
    move: Ψ2 Ψ3 ρ12 ρ23.
    induction e; rewrites;
    by dependent induction H.
  Qed.

  (* TODO: derive this generally for any syntax *)
  Theorem ren_subst_cong_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) :
    map (Ren.cong ρ23) ∘ Sub.cong σ12
    =
    Sub.cong (map ρ23 ∘ σ12).
  Proof.
    T.eqcd => x; rewrite /compose; move: Ψ2 Ψ3 σ12 ρ23.
    dependent destruction x;
    T.rewrites_with ltac:(try rewrite ren_coh).
  Qed.

  Theorem ren_subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) e :
    (e ⫽ σ12).[ρ23]%tm
    =
    e ⫽ (map ρ23 ∘ σ12).
  Proof.
    move: Ψ2 Ψ3 σ12 ρ23.
    induction e; rewrites;
    by rewrite -ren_subst_cong_coh.
  Qed.

  Theorem subst_ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) e :
    e.[ρ12] ⫽ σ23
    =
    e ⫽ (σ23 ∘ ρ12).
  Proof.
    move: Ψ2 Ψ3 ρ12 σ23.
    induction e; rewrites;
    f_equal; f_equal;
    by dependent destruction H.
  Qed.

  Theorem subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) (e : t _) :
    e ⫽ σ12 ⫽ σ23
    =
    e ⫽ (subst σ23 ∘ σ12).
  Proof.
    move: Ψ2 Ψ3 σ12 σ23.
    rewrite /compose.
    induction e; rewrites;
    dependent induction H; auto; simpl;
    by rewrite ren_subst_coh subst_ren_coh.
  Qed.


  Lemma cong_id {Ψ} : Sub.cong (@var Ψ) = @var (S Ψ).
  Proof.
    T.eqcd => x.
    dependent destruction x; auto.
  Qed.

  Theorem subst_ret {Ψ} e :
    e ⫽ (@var Ψ) = e.
  Proof.
    induction e; rewrites;
    by rewrite cong_id.
  Qed.

  Theorem subst_closed (σ : Sub.t 0 0) (e : t 0) :
    e ⫽ σ = e.
  Proof.
    rewrite -{2}(subst_ret e).
    f_equal.
    T.eqcd => x.
    dependent destruction x.
  Qed.

End Tm.

Export Tm.Notations Tm.RenNotation Tm.SubstNotation.

Reserved Notation "e 'val'" (at level 50).
Reserved Notation "e ↦ e'" (at level 50).
Reserved Notation "e ↦⋆ e'" (at level 50).

Inductive is_val : Tm.t 0 → Ω :=
| val_bool : 𝟚 val
| val_unit : 𝟙 val
| val_prod : ∀ {e1 e2}, (e1 × e2) val
| val_arr : ∀ {e1 e2}, (e1 ⇒ e2) val
| val_ltr : ∀ {κ e}, ▶[κ] e val
| val_isect : ∀ {e}, ⋂ e val
| val_univ : ∀ {i}, 𝕌[i] val
| val_ax : ★ val
| val_tt : Tm.tt val
| val_ff : Tm.ff val
| val_pair : ∀ {e1 e2}, ⟨e1, e2⟩ val
| val_lam : ∀ {e}, 𝛌{ e } val
where "v 'val'" := (is_val v%tm).

Inductive step : Tm.t 0 → Tm.t 0 → Ω :=
| step_fst_cong :
    ∀ {e e'},
      e ↦ e'
      → (e.1) ↦ (e'.1)

| step_snd_cong :
    ∀ {e e'},
      e ↦ e'
      → (e.2) ↦ (e'.2)

| step_app_cong :
    ∀ {e1 e1' e2},
      e1 ↦ e1'
      → (e1 ⋅ e2) ↦ (e1' ⋅ e2)

| step_fst_pair : ∀ {e1 e2}, ⟨e1,e2⟩.1 ↦ e1
| step_snd_pair : ∀ {e1 e2}, ⟨e1,e2⟩.2 ↦ e2
| step_app_lam : ∀ {e1 e2}, 𝛌{e1} ⋅ e2 ↦ (e1 ⫽ Sub.inst0 e2)
| step_fix : ∀ e, Tm.fix_ e ↦ (e ⫽ Sub.inst0 (Tm.fix_ e))
where "e ↦ e'" := (step e%tm e'%tm).

Hint Constructors is_val.
Hint Constructors step.

Inductive steps : Tm.t 0 → Tm.t 0 → Ω :=
| steps_nil : ∀ {e}, e ↦⋆ e
| steps_cons : ∀ {e1 e2 e3}, e1 ↦ e2 → e2 ↦⋆ e3 → e1 ↦⋆ e3
where "e ↦⋆ e'" := (steps e%tm e'%tm).

Hint Constructors steps.

Record eval (e v : Tm.t 0) :=
  { eval_steps : e ↦⋆ v;
    eval_val : v val
  }.

Hint Constructors eval.
Notation "e ⇓ v" := (eval e%tm v%tm) (at level 50).

Ltac destruct_evals :=
  repeat
    match goal with
    | H : _ ↦ _ |- _ => dependent destruction H
    | H : _ ↦⋆ _ |- _ => dependent destruction H
    | H : _ ⇓ _ |- _ => dependent destruction H
    | H : _ val |- _ => dependent destruction H
    end.

(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.

Ltac evals_to_eq :=
  repeat
    match goal with
    | H1 : ?A ⇓ ?V1, H2 : ?A ⇓ ?V2 |- _ =>
      simpl in H1, H2;
      have: V1 = V2;
      [ apply: determinacy; eauto
      | move {H1 H2} => *
      ]
    end.


Definition closed_approx (e1 e2 : Tm.t 0) : Ω :=
  ∀ v, e1 ⇓ v → e2 ⇓ v.

Definition closed_equiv (e1 e2 : Tm.t 0) : Ω :=
  ∀ v, e1 ⇓ v ↔ e2 ⇓ v.

Arguments closed_approx e1%tm e2%tm.
Arguments closed_equiv e1%tm e2%tm.

Notation "e0 ≼₀ e1" := (closed_approx e0%tm e1%tm) (at level 30).
Notation "e0 ≈₀ e1" := (closed_equiv e0%tm e1%tm) (at level 30).

Theorem closed_approx_refl : ∀ e, e ≼₀ e.
Proof.
  by compute.
Qed.

Hint Resolve closed_approx_refl.

Theorem approx_invert :
  ∀ e e' v,
    e ⇓ v
    → e ≼₀ e'
    → e' ≼₀ e.
Proof.
  move=> e e' v 𝒟 ℰ v' ℱ.
  specialize (ℰ v 𝒟).
  evals_to_eq.
  by T.destruct_eqs.
Qed.

Theorem fix_unfold :
  ∀ f, (Tm.fix_ f) ≈₀ (f ⫽ Sub.inst0 (Tm.fix_ f)).
Proof.
  move=> f v.
  split.
  - move=> [𝒟1 𝒟2].
    split; auto.
    dependent destruction 𝒟1.
    + by dependent destruction 𝒟2.
    + by dependent destruction H.
  - move=> [𝒟1 𝒟2].
    split; auto.
    econstructor; eauto.
Qed.

Ltac simplify_subst_step :=
  try rewrite Tm.subst_ren_coh;
  try rewrite Tm.ren_subst_coh;
  try rewrite Tm.subst_coh;
  try rewrite Tm.subst_closed;
  try rewrite /compose.

Ltac simplify_subst :=
  repeat (simplify_eqs; f_equal; try T.eqcd; intros; simplify_subst_step).
