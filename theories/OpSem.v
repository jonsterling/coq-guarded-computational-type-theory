Require Import Unicode.Utf8 Program.
Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From ctt Require Import Notation Axioms Program Var.
From ctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.

Reserved Notation "M 'val'" (at level 50).
Reserved Notation "M ↦ M'" (at level 50).
Reserved Notation "M ↦⋆ M'" (at level 50).

Inductive is_val : Prog.t 0 → Ω :=
| val_bool : 𝟚 val
| val_void : 𝟘 val
| val_unit : 𝟙 val
| val_prod : ∀ {M1 M2}, (M1 × M2) val
| val_arr : ∀ {M1 M2}, (M1 ⇒ M2) val
| val_karr : ∀ {M}, Prog.karr M val
| val_ltr : ∀ {κ M}, ▶[κ] M val
| val_isect : ∀ {M}, ⋂ M val
| val_univ : ∀ {i}, 𝕌[i] val
| val_ax : ★ val
| val_tt : Prog.tt val
| val_ff : Prog.ff val
| val_pair : ∀ {M1 M2}, ⟨M1, M2⟩ val
| val_lam : ∀ {M}, 𝛌{ M } val
| val_klam : ∀ {M}, Prog.klam M val
where "V 'val'" := (is_val V%prog).

Inductive step : Prog.t 0 → Prog.t 0 → Ω :=
| step_fst_cong :
    ∀ {M M'},
      M ↦ M'
      → (M.1) ↦ (M'.1)

| step_snd_cong :
    ∀ {M M'},
      M ↦ M'
      → (M.2) ↦ (M'.2)

| step_app_cong :
    ∀ {M1 M1' M2},
      M1 ↦ M1'
      → (M1 ⋅ M2) ↦ (M1' ⋅ M2)

| step_kapp_cong :
    ∀ {M M' κ},
      M ↦ M'
      → (Prog.kapp M κ) ↦ (Prog.kapp M' κ)

| step_fst_pair : ∀ {M1 M2}, ⟨M1,M2⟩.1 ↦ M1
| step_snd_pair : ∀ {M1 M2}, ⟨M1,M2⟩.2 ↦ M2
| step_app_lam : ∀ {M1 M2}, 𝛌{M1} ⋅ M2 ↦ (M1 ⫽ Sub.inst0 M2)
| step_kapp_klam : ∀ {M κ}, Prog.kapp (Prog.klam M) κ ↦ M κ
| step_fix : ∀ M, 𝛍{M} ↦ (M ⫽ Sub.inst0 (𝛍{M}))
where "M ↦ M'" := (step M%prog M'%prog).

Hint Constructors is_val.
Hint Constructors step.

Inductive steps : Prog.t 0 → Prog.t 0 → Ω :=
| steps_nil : ∀ {M}, M ↦⋆ M
| steps_cons : ∀ {M1 M2 M3}, M1 ↦ M2 → M2 ↦⋆ M3 → M1 ↦⋆ M3
where "M ↦⋆ M'" := (steps M%prog M'%prog).

Hint Constructors steps.

Record eval (M V : Prog.t 0) :=
  { eval_steps : M ↦⋆ V;
    eval_val : V val
  }.

Hint Constructors eval.
Notation "M ⇓ V" := (eval M%prog V%prog) (at level 50).

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


Definition closed_approx (M1 M2 : Prog.t 0) : Ω :=
  ∀ V, M1 ⇓ V → M2 ⇓ V.

Definition closed_equiv (M1 M2 : Prog.t 0) : Ω :=
  ∀ V, M1 ⇓ V ↔ M2 ⇓ V.

Arguments closed_approx M1%prog M2%prog.
Arguments closed_equiv M1%prog M2%prog.

Notation "M0 ≼₀ M1" := (closed_approx M0%prog M1%prog) (at level 30).
Notation "M0 ≈₀ M1" := (closed_equiv M0%prog M1%prog) (at level 30).

Theorem closed_approx_refl : ∀ M, M ≼₀ M.
Proof.
  by compute.
Qed.

Hint Resolve closed_approx_refl.

Theorem approx_invert :
  ∀ M M' V,
    M ⇓ V
    → M ≼₀ M'
    → M' ≼₀ M.
Proof.
  move=> M M' V 𝒟 ℰ V' ℱ.
  specialize (ℰ V 𝒟).
  evals_to_eq.
  by T.destruct_eqs.
Qed.

Theorem fix_unfold :
  ∀ M, 𝛍{M} ≈₀ (M ⫽ Sub.inst0 (𝛍{M}%prog)).
Proof.
  move=> M V.
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
  ∀ M0 N M1,
    (M0 ↦⋆ 𝛌{N})
    → (N ⫽ Sub.inst0 M1) ≼₀ (M0 ⋅ M1).
Proof.
  move=> M0 N M1 Q.
  constructor.
  - dependent induction H.
    dependent induction Q.
    + econstructor; eauto.
    + econstructor; eauto.
  - dependent induction H.
    eauto.
Qed.

Theorem fst_pair :
  ∀ M0 M1,
    M0 ≼₀ (⟨M0,M1⟩.1).
Proof.
  move=> M0 M1 V H.
  dependent destruction H.
  constructor; auto.
  - econstructor.
    + apply: step_fst_pair.
    + auto.
Qed.

Theorem snd_pair :
  ∀ M0 M1,
    M1 ≼₀ (⟨M0,M1⟩.2).
Proof.
  move=> M0 M1 V H.
  dependent destruction H.
  constructor; auto.
  - econstructor.
    + apply: step_snd_pair.
    + auto.
Qed.



Theorem fst_eval :
  ∀ M M0 M1 v0,
    M ⇓ ⟨M0,M1⟩
    → M0 ⇓ v0
    → M.1 ⇓ v0.
Proof.
  move=> M M0 M1 v0 H0 H1.
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
  ∀ N N' M V,
    (N ⇓ 𝛌{N'})
    → N' ⫽ Sub.inst0 M ⇓ V
    → (N ⋅ M) ⇓ V.
Proof.
  move=> N N' M V H0 H1.
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
  ∀ M M0 M1 V,
    M ⇓ ⟨M0,M1⟩
    → M1 ⇓ V
    → M.2 ⇓ V.
Proof.
  move=> M M0 M1 V H0 H1.
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
  ∀ M v1,
    M.1 ⇓ v1
    → ∃ M1 M2, M1 ⇓ v1 ∧ M ⇓ ⟨M1, M2⟩.
Proof.
  move=> M M1 H.
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
    + by exists M1, M2.
Qed.

Theorem snd_eval_inv :
  ∀ M V,
    M.2 ⇓ V
    → ∃ M1 M2, M2 ⇓ V ∧ M ⇓ ⟨M1,M2⟩.
Proof.
  move=> M M1 H.
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
    + by exists M1, M2.
Qed.

Theorem app_eval_inv :
  ∀ N M V,
    N ⋅ M ⇓ V
    → ∃ N', (N ⇓ 𝛌{N'}) ∧ (N' ⫽ Sub.inst0 M) ⇓ V.
Proof.
  move=> N M V H.
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
    + by exists M1.
Qed.


Theorem fst_cong_approx :
  ∀ M0 M1,
    M0 ≼₀ M1
    → Prog.fst M0 ≼₀ Prog.fst M1.
Proof.
  move=> M0 M1 M01 p1 ℰ.
  have := fst_eval_inv ℰ.
  move=> [M' [p2 [H0 H1]]].
  apply: fst_eval; eauto.
Qed.

Theorem snd_cong_approx :
  ∀ M0 M1,
    M0 ≼₀ M1
    → Prog.snd M0 ≼₀ Prog.snd M1.
Proof.
  move=> M0 M1 M01 p1 ℰ.
  have := snd_eval_inv ℰ.
  move=> [M' [p2 [H0 H1]]].
  apply: snd_eval; eauto.
Qed.

Theorem app_cong_approx :
  ∀ f0 f1 M,
    f0 ≼₀ f1
    → (f0 ⋅ M) ≼₀ (f1 ⋅ M).
Proof.
  move=> N0 N1 M N01 V ℰ.
  have := app_eval_inv ℰ.
  move=> [N' [? ?]].
  apply: app_eval; eauto.
Qed.