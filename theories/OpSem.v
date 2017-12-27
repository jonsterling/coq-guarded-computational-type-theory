Require Import Unicode.Utf8 Program.
From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Axioms Term Var.
From gctt Require Tactic.
Module T := Tactic.


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
| step_fix : ∀ e, 𝛍{e} ↦ (e ⫽ Sub.inst0 (𝛍{e}))
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
  ∀ f, 𝛍{f} ≈₀ (f ⫽ Sub.inst0 (𝛍{f}%tm)).
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

Theorem app_lam :
  ∀ e0 f e1,
    (e0 ↦⋆ 𝛌{f})
    → (f ⫽ Sub.inst0 e1) ≼₀ (e0 ⋅ e1).
Proof.
  move=> e0 e e1 Q.
  constructor.
  - dependent induction H.
    dependent induction Q.
    + econstructor; eauto.
    + econstructor; eauto.
  - dependent induction H.
    eauto.
Qed.

Theorem fst_pair :
  ∀ e0 e1,
    e0 ≼₀ (⟨e0,e1⟩.1).
Proof.
  move=> e0 e1 v H.
  dependent destruction H.
  constructor; auto.
  - econstructor.
    + apply: step_fst_pair.
    + auto.
Qed.

Theorem snd_pair :
  ∀ e0 e1,
    e1 ≼₀ (⟨e0,e1⟩.2).
Proof.
  move=> e0 e1 v H.
  dependent destruction H.
  constructor; auto.
  - econstructor.
    + apply: step_snd_pair.
    + auto.
Qed.
