Require Import Unicode.Utf8 Program.
From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Axioms Term Var.
From gctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.

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



Theorem fst_eval :
  ∀ e e0 e1 v0,
    e ⇓ ⟨e0,e1⟩
    → e0 ⇓ v0
    → e.1 ⇓ v0.
Proof.
  move=> e e0 e1 v0 H0 H1.
  dependent induction H0.
  dependent induction eval_steps0.
  - constructor; auto.
    + econstructor.
      * by apply: step_fst_pair.
      * by dependent destruction H1.
    + by destruct H1.
  - dependent destruction H1.
    constructor; auto.
    econstructor.
    * apply: step_fst_cong; eauto.
    * edestruct IHeval_steps0; eauto.
Qed.

Theorem app_eval :
  ∀ f f' e v,
    (f ⇓ 𝛌{f'})
    → f' ⫽ Sub.inst0 e ⇓ v
    → (f ⋅ e) ⇓ v.
Proof.
  move=> f f' e v H0 H1.
  dependent induction H0.
  dependent induction eval_steps0.
  - constructor; auto.
    + econstructor.
      * by apply: step_app_lam.
      * by dependent induction H1.
    + by destruct H1.
  - dependent destruction H1.
    constructor; auto.
    econstructor.
    * apply: step_app_cong; eauto.
    * edestruct IHeval_steps0; eauto.
Qed.

Theorem snd_eval :
  ∀ e e0 e1 v,
    e ⇓ ⟨e0,e1⟩
    → e1 ⇓ v
    → e.2 ⇓ v.
Proof.
  move=> e e0 e1 v H0 H1.
  dependent induction H0.
  dependent induction eval_steps0.
  - constructor; auto.
    + econstructor.
      * by apply: step_snd_pair.
      * by dependent destruction H1.
    + by destruct H1.
  - dependent destruction H1.
    constructor; auto.
    econstructor.
    * apply: step_snd_cong; eauto.
    * edestruct IHeval_steps0; eauto.
Qed.

Theorem fst_eval_inv :
  ∀ e v1,
    e.1 ⇓ v1
    → ∃ e1 e2, e1 ⇓ v1 ∧ e ⇓ ⟨e1, e2⟩.
Proof.
  move=> e e1 H.
  dependent induction H.
  dependent induction eval_steps0.
  - dependent destruction eval_val0.
  - dependent induction H.
    + edestruct IHeval_steps0; eauto.
      case: H0 => [z [zz zzz]].
      exists x, z; split; auto.
      constructor; auto.
      econstructor; eauto.
      dependent destruction zzz.
      eauto.
    + by exists e1, e2.
Qed.

Theorem snd_eval_inv :
  ∀ e v,
    e.2 ⇓ v
    → ∃ e1 e2, e2 ⇓ v ∧ e ⇓ ⟨e1,e2⟩.
Proof.
  move=> e e1 H.
  dependent induction H.
  dependent induction eval_steps0.
  - dependent induction eval_val0.
  - dependent induction H.
    + edestruct IHeval_steps0; eauto.
      case: H0 => [z [zz zzz]].
      exists x, z; split; auto.
      constructor; auto.
      econstructor; eauto.
      dependent destruction zzz.
      eauto.
    + by exists e1, e2.
Qed.

Theorem app_eval_inv :
  ∀ f e v,
    f ⋅ e ⇓ v
    → ∃ f', (f ⇓ 𝛌{f'}) ∧ (f' ⫽ Sub.inst0 e) ⇓ v.
Proof.
  move=> f e v H.
  dependent induction H.
  dependent induction eval_steps0.
  - dependent induction eval_val0.
  - dependent induction H.
    + edestruct IHeval_steps0; eauto.
      destruct H0.
      exists x; split.
      * constructor; auto.
        econstructor; eauto.
        by dependent induction H0.
      * auto.
    + by exists e1.
Qed.


Theorem fst_cong_approx :
  ∀ e0 e1,
    e0 ≼₀ e1
    → Tm.fst e0 ≼₀ Tm.fst e1.
Proof.
  move=> e0 e1 e01 p1 ℰ.
  have := fst_eval_inv ℰ.
  move=> [e' [p2 [H0 H1]]].
  apply: fst_eval; eauto.
Qed.

Theorem snd_cong_approx :
  ∀ e0 e1,
    e0 ≼₀ e1
    → Tm.snd e0 ≼₀ Tm.snd e1.
Proof.
  move=> e0 e1 e01 p1 ℰ.
  have := snd_eval_inv ℰ.
  move=> [e' [p2 [H0 H1]]].
  apply: snd_eval; eauto.
Qed.

Theorem app_cong_approx :
  ∀ f0 f1 e,
    f0 ≼₀ f1
    → (f0 ⋅ e) ≼₀ (f1 ⋅ e).
Proof.
  move=> f0 f1 e f01 v ℰ.
  have := app_eval_inv ℰ.
  move=> [f' [? ?]].
  apply: app_eval; eauto.
Qed.