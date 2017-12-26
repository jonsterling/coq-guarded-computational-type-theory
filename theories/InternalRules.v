Require Import Unicode.Utf8 Program.Tactics Program.Equality Program.Basics Logic.FunctionalExtensionality.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Var OrderTheory Axioms Term OpSem Closure Tower Sequent TypeSystem.
From gctt Require Tactic.

Module T := Tactic.

Require Import Coq.omega.Omega.
Open Scope program_scope.

Module Tac.
  Ltac tower_intro :=
    rewrite /Tower.t -Clo.roll.

  Ltac connective_eq_type :=
    apply: Sig.conn; eauto; constructor.

  Local Ltac accum_lvl_aux x n :=
    match goal with
    | H : τ[?n'] _ |- _ => move: H; accum_lvl_aux x (n + n'); move=> H
    | |- _ => pose x := n
    end.

  Ltac accum_lvl x :=
    accum_lvl_aux x 0.

  Ltac tower_mono :=
    apply: Tower.monotonicity; last by [eassumption];
    cbn; omega.

  Ltac prove_eval :=
    match goal with
    | |- ?A ⇓ ?Av => eauto
    end.

  Ltac destruct_prod_val :=
    match goal with
    | H : Connective.prod_val _ _ _ |- _ => dependent destruction H
    end.


  (* When you need to show 'τ[n] (A, R)' but R is not of the right
   shape.  This tactic will replace R with a unification variable,
   which allows you to make progress in your proof; then, you have to
   prove hat R was is the same as whatever the unification variable
   got instantiated to. *)

  Ltac ts_flex_rel :=
    match goal with
    | |- τ[_] (_, ?R) =>
      let R' := fresh in
      evar (R' : rel);
      (suff: R = R'); first T.rewrite_; rewrite /R'; clear R'
    end.

  Ltac prove_step :=
    try by [eassumption];
    match goal with
    | |- _ ⊧ _ ∼ _ => esplit; split
    | |- _ ⊧ _ ∋ _ ∼ _ => esplit; split
    | |- τ[_] _ => tower_intro
    | |- Sig.t _ _ (Tm.univ _, _) => apply: Sig.init
    | |- Sig.t _ _ (_, _) => apply: Sig.conn
    | |- Spine.t _ (Tm.univ _, _) => Spine.simplify; repeat T.split; [idtac | eauto | reflexivity] ; eauto
    | |- Connective.cext _ _ => repeat econstructor
    | |- Connective.has _ _ _ => econstructor
    | |- _ ⇓ _ => prove_eval
    | |- _ ≤ _ => omega
    | |- ∃ _ : nat, _ => esplit
    | |- τω _ => rewrite /τω
    | |- (_ ⊧ _ ∼ _) → _ => case => [?]
    | |- (_ ⊧ _ ∋ _ ∼ _) → _ => move=> [?]
    | |- (_ ∧ _) → _ => case
    | |- τ[?n] _ -> _ => move=> ?
    | |- τω _ → _ => move=> [?]
    | |- _ → _ => move=> ?
    end.

  Ltac prove := repeat prove_step.
End Tac.

Module Level.
  Theorem eq_ty_from_level n {A B} :
    τ[n] ⊧ A ∼ B
    → τω ⊧ A ∼ B.
  Proof.
    move=> [R [TA TB]].
    eexists.
    split.
    + eexists; eauto.
    + eexists; eauto.
  Qed.

  Theorem eq_ty_to_level {A B} :
    τω ⊧ A ∼ B
    → ∃ n, τ[n] ⊧ A ∼ B.
  Proof.
    move=> [R [[n𝒟 𝒟] [nℰ ℰ]]].
    exists (n𝒟 + nℰ), R.
    T.split;
    (apply: Tower.monotonicity; last by [eauto]); omega.
  Qed.

  Theorem eq_mem_from_level n {A e1 e2} :
    τ[n] ⊧ A ∋ e1 ∼ e2
    → τω ⊧ A ∋ e1 ∼ e2.
  Proof.
    move=> [R [TA e1e2]].
    eexists.
    split.
    + eexists; eauto.
    + eauto.
  Qed.

  Theorem eq_mem_to_level {A e1 e2} :
    τω ⊧ A ∋ e1 ∼ e2
    → ∃ n, τ[n] ⊧ A ∋ e1 ∼ e2.
  Proof.
    move=> [R [[n𝒟 𝒟] e1e2]].
    exists n𝒟, R.
    T.split.
    - Tac.tower_mono.
    - auto.
  Qed.

  Lemma mem_eq_at_lvl_of_typehood {m n A B e0 e1} :
    τ[n] ⊧ A ∋ e0 ∼ e1
    → τ[m] ⊧ A ∼ B
    → τ[m] ⊧ A ∋ e0 ∼ e1.
  Proof.
    move=> [R [𝒟0 𝒟1]] [S [ℰ0 ℰ1]].
    exists S; split; first by assumption.
    replace S with R; first by assumption.
    apply: TS.is_extensional;
    eexists; eassumption.
  Qed.
End Level.



Module General.
  Theorem replace_ty_in_mem_eq {τ A0 A1 e1 e2} `{TS.extensional τ} :
    τ ⊧ A0 ∋ e1 ∼ e2
    → τ ⊧ A0 ∼ A1
    → τ ⊧ A1 ∋ e1 ∼ e2.
  Proof.
    Tac.prove.

    match goal with
    | _ : ?R0 ?X |- ?R1 ?X =>
      replace R1 with R0; auto
    end.

    apply: TS.is_extensional; eauto.
  Qed.

  Theorem ty_eq_refl_left {τ A B} :
    τ ⊧ A ∼ B
    → τ ⊧ A ∼ A.
  Proof.
    Tac.prove.
  Qed.

  Theorem ty_eq_symm {τ A B} :
    τ ⊧ A ∼ B
    → τ ⊧ B ∼ A.
  Proof.
    Tac.prove.
  Qed.

  Theorem ty_eq_conv {τ A0 A1 B} `{TS.type_computational τ} :
    A0 ≼₀ A1
    → τ ⊧ A0 ∼ B
    → τ ⊧ A1 ∼ B.
  Proof.
    move=> A01 [R [𝒟A0 𝒟B]].
    exists R; split; auto.
    apply: TS.is_type_computational.
    - exact 𝒟A0.
    - auto.
  Qed.

  Theorem mem_eq_conv_ty {τ A0 A1 e0 e1} `{TS.type_computational τ} :
    A0 ≼₀ A1
    → τ ⊧ A0 ∋ e0 ∼ e1
    → τ ⊧ A1 ∋ e0 ∼ e1.
  Proof.
    move=> A01 [R [𝒟 e01]].
    exists R; split; auto.
    apply: TS.is_type_computational; eauto.
  Qed.

  Theorem mem_eq_symm {τ A e0 e1} `{TS.cper_valued τ} :
    τ ⊧ A ∋ e0 ∼ e1
    → τ ⊧ A ∋ e1 ∼ e0.
  Proof.
    move=> [R [𝒟 ℰ]].
    exists R; split; auto.
    apply: symmetric; auto.
    apply: per.
    apply: TS.is_cper_valued.
    eauto.
  Qed.

  Theorem mem_eq_conv {τ A e00 e01 e1} `{TS.cper_valued τ} :
    e00 ≼₀ e01
    → τ ⊧ A ∋ e00 ∼ e1
    → τ ⊧ A ∋ e01 ∼ e1.
  Proof.
    move=> e00e01 [R [ℰ e00e1]].
    exists R; split; auto.
    apply: crel; eauto.
    apply: TS.is_cper_valued; eauto.
  Qed.


  Theorem mem_eq_conv_both {τ A e00 e01 e10 e11} `{TS.cper_valued τ} :
    e00 ≼₀ e01
    → e10 ≼₀ e11
    → τ ⊧ A ∋ e00 ∼ e10
    → τ ⊧ A ∋ e01 ∼ e11.
  Proof.
    move=> ? ? ?.
    apply: mem_eq_conv; eauto.
    apply: mem_eq_symm; eauto.
    apply: mem_eq_conv; eauto.
    by apply: mem_eq_symm.
  Qed.

  Theorem ty_eq_trans {τ A B C} `{TS.cper_valued τ} `{TS.extensional τ}:
    τ ⊧ B ∼ C
    → τ ⊧ A ∼ B
    → τ ⊧ A ∼ C.
  Proof.
    move=> [R1 [? ?]] [R2 [? ?]].
    exists R2; T.split.
    - eauto.
    - replace R2 with R1; auto.
      symmetry; apply: TS.is_extensional; eauto.
  Qed.

  Theorem mem_eq_trans {τ A e0 e1 e2} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A ∋ e1 ∼ e2
    → τ ⊧ A ∋ e0 ∼ e1
    → τ ⊧ A ∋ e0 ∼ e2.
  Proof.
    Tac.prove.
    apply: transitive; eauto.
    - apply: per.
      apply: TS.is_cper_valued; eauto.
    - match goal with
      | H : ?R1 (e1, e2) |- ?R2 (e1, e2) =>
        replace R2 with R1; auto
      end.
      apply: TS.is_extensional; eauto.
  Qed.

  Theorem mem_eq_refl_left {τ A e0 e1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A ∋ e0 ∼ e1
    → τ ⊧ A ∋ e0 ∼ e0.
  Proof.
    move=> 𝒟.
    apply: mem_eq_trans; eauto.
    apply: mem_eq_symm; eauto.
  Qed.


  Theorem env_eq_symm {Ψ} {Γ : Prectx Ψ} {τ γ0 γ1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τ ⊧ Γ ∋⋆ γ1 ∼ γ0.
  Proof.
    move=> Γctx γ01.
    induction Γ; eauto.
    split; simplify_eqs.
    - apply: IHΓ; eauto.
      + by case: Γctx.
      + by case: γ01.
    - suff: τ ⊧ t ⫽ (γ1 ∘ Fin.FS) ∼ (t ⫽ (γ0 ∘ Fin.FS)).
      + move=> [R [𝒟0 𝒟1]].
        case: γ01 => //= [_ [S [ℰ γ01]]].
        eexists; T.split; eauto.
        apply: symmetric.
        * apply: per.
          apply: TS.is_cper_valued.
          eassumption.
        * replace R with S; auto.
          apply: TS.is_extensional; eauto.
      + case: Γctx => _ 𝒟.
        apply: ty_eq_symm.
        apply: 𝒟.
        by case: γ01.
  Qed.

  Theorem env_eq_trans {Ψ} {Γ : Prectx Ψ} {τ γ0 γ1 γ2} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τ ⊧ Γ ∋⋆ γ1 ∼ γ2
    → τ ⊧ Γ ∋⋆ γ0 ∼ γ2.
  Proof.
    move=> Γctx γ01 γ12.
    induction Γ; eauto.
    split; simplify_eqs.
    - apply: IHΓ; eauto.
      + by case: Γctx.
      + case: γ01 => X _.
        exact X.
      + case: γ12 => X _.
        exact X.
    - suff: τ ⊧ t ⫽ (γ0 ∘ Fin.FS) ∼ (t ⫽ (γ1 ∘ Fin.FS)) ∧ τ ⊧ t ⫽ (γ1 ∘ Fin.FS) ∼ (t ⫽ (γ2 ∘ Fin.FS)).
      + move=> [[R [𝒟0 𝒟1]] [R' [𝒟'0 𝒟'1]]].
        case: γ01 => //= [_ [S [ℰ γ01]]].
        case: γ12 => //= [_ [S' [ℱ γ01']]].
        eexists; T.split; eauto.
        apply: transitive; eauto.
        * apply: per.
          apply: TS.is_cper_valued.
          eassumption.
        * suff: S = R ∧ R = S'.
          ** move=> [Q1 Q2].
             by rewrite Q1 Q2.
          ** split; apply: TS.is_extensional; eauto.
      + split.
        * case: Γctx => _ 𝒟.
          apply: 𝒟.
          by case: γ01.
        * case: Γctx => _ 𝒟.
          apply: 𝒟.
          by case: γ12.
  Qed.


  Theorem env_eq_refl_left {Ψ} {Γ : Prectx Ψ} {τ γ0 γ1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τ ⊧ Γ ∋⋆ γ0 ∼ γ0.
  Proof.
    move=> *.
    apply: env_eq_trans; eauto.
    apply: env_eq_symm; eauto.
  Qed.


  Section FunctionalitySquare.
    Context {Ψ} {Γ : Prectx Ψ} {A e0 e1 : Tm.t Ψ} {γ0 γ1 : @Sub.t Tm.t Ψ 0} {τ} `{TS.cper_valued τ} `{TS.extensional τ}.

    Lemma functionality_square :
      τ ⊧ Γ ≫ A ∋ e0 ∼ e1
      → τ ⊧ Γ ctx
      → τ ⊧ Γ ∋⋆ γ0 ∼ γ1
      → τ ⊧ A ⫽ γ0 ∋ (e0 ⫽ γ0) ∼ (e1 ⫽ γ1)
        ∧ τ ⊧ A ⫽ γ1 ∋ (e0 ⫽ γ1) ∼ (e1 ⫽ γ1)
        ∧ τ ⊧ A ⫽ γ0 ∋ (e0 ⫽ γ0) ∼ (e1 ⫽ γ0).
    Proof.
      move=> 𝒟 ℰ γ01.
      repeat T.split.
      - by apply: 𝒟.
      - apply: 𝒟.
        apply: env_eq_refl_left; auto.
        apply: env_eq_symm; eauto.
      - apply: 𝒟.
        apply: env_eq_refl_left; eauto.
    Qed.
  End FunctionalitySquare.


  Theorem open_ty_eq_refl_left {Ψ} {Γ : Prectx Ψ} {τ A A'} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ≫ A ∼ A'
    → τ ⊧ Γ ≫ A ∼ A.
  Proof.
    move=> 𝒟 ℰ γ0 γ1 γ01.
    apply: ty_eq_trans.
    - apply: ty_eq_symm.
      apply: ℰ.
      apply: env_eq_symm; eauto.
    - apply: ℰ.
      apply: env_eq_refl_left; eauto.
  Qed.


  Theorem open_mem_eq_refl_left {Ψ} {Γ : Prectx Ψ} {τ A A' e0 e1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ≫ A ∼ A'
    → τ ⊧ Γ ≫ A ∋ e0 ∼ e1
    → τ ⊧ Γ ≫ A ∋ e0 ∼ e0.
  Proof.
    move=> 𝒟 ℰ ℱ γ0 γ1 γ01.
    apply: mem_eq_trans; auto.
    - apply: mem_eq_symm; auto.
      apply: replace_ty_in_mem_eq.
      + apply: ℱ.
        apply: env_eq_refl_left; eauto.
        apply: env_eq_symm; eauto.
      + apply: ty_eq_trans.
        * apply: ty_eq_symm.
          apply: ℰ; eauto.
        * apply: ℰ.
          apply: env_eq_refl_left; eauto.
          apply: env_eq_symm; eauto.
    - eauto.
  Qed.
End General.

Module Univ.
  Lemma formation_S {n : nat} :
    τ[S n] ⊧ 𝕌[n] ∼ 𝕌[n].
  Proof.
    Tac.prove.
  Qed.

  Theorem formation_lvl {n i : nat} :
    i < n
    → τ[n] ⊧ 𝕌[i] ∼ 𝕌[i].
  Proof.
    case => [| j q ].
    + apply: formation_S.
    + Tac.prove.
  Qed.

  Theorem formation_ω {i} :
    τω ⊧ 𝕌[i] ∼ 𝕌[i].
  Proof.
    apply: Level.eq_ty_from_level.
    apply: formation_lvl.
    eauto.
  Qed.

  Lemma intro {i A0 A1} :
    τ[i] ⊧ A0 ∼ A1
    → τω ⊧ 𝕌[i] ∋ A0 ∼ A1.
  Proof.
    move=> 𝒟.
    apply: (Level.eq_mem_from_level (S i)).
    esplit; split.
    - rewrite /Tower.t -Clo.roll.
      apply: Sig.init.
      Spine.simplify.
      exists i; repeat split; eauto.
    - eauto.
  Qed.

  Lemma inversion {i A0 A1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τ[i] ⊧ A0 ∼ A1.
  Proof.
    move=> [R [[n 𝒟] ℰ]].
    Tower.destruct_tower.
    destruct n; Spine.simplify.
    - contradiction.
    - case: H => //= [j [p [ev spec]]].
      OpSem.destruct_evals.
      rewrite spec in ℰ.
      case: ℰ => //= [S [ℰ1 ℰ2]].
      by exists S.
  Qed.

  Lemma inversionω {i A0 A1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ A0 ∼ A1.
  Proof.
    move=> 𝒟.
    apply: Level.eq_ty_from_level.
    apply: inversion.
    eassumption.
  Qed.


  Lemma open_inversionω {Ψ} {Γ : Prectx Ψ} {i A0 A1} :
    τω ⊧ Γ ≫ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ Γ ≫ A0 ∼ A1.
  Proof.
    move=> 𝒟 γ0 γ1 γ01.
    specialize (𝒟 γ0 γ1).
    suff: τω ⊧ Γ ∋⋆ γ0 ∼ γ1.
    - move=> /𝒟 ℱ.
      apply: Level.eq_ty_from_level.
      apply: inversion.
      eassumption.
    - induction Γ; simpl; auto; split.
  Qed.

  Lemma open_inversion {Ψ} {Γ : Prectx Ψ} {i A0 A1} :
    τω ⊧ Γ ≫ 𝕌[i] ∋ A0 ∼ A1
    → τ[i] ⊧ Γ ctx
    → τ[i] ⊧ Γ ≫ A0 ∼ A1.
  Proof.
    move=> 𝒟 ℰ γ0 γ1 γ01.
    specialize (𝒟 γ0 γ1).
    suff: τω ⊧ Γ ∋⋆ γ0 ∼ γ1.
    - move=> /𝒟 ℱ.
      by apply: inversion.
    - induction Γ; simpl; auto; split.
      + apply: (IHΓ t t).
        * move=> ?.
          Term.simplify_subst.
          apply: intro.
          simpl in *.
          case: ℰ => 𝒢 ℋ.
          case: γ01 => ? ?.
          by apply: ℋ.
        * by case: ℰ.
        * by case: γ01.

      + apply: Level.eq_mem_from_level.
        case: γ01 => ? ?.
        eauto.
  Qed.



  Theorem spine_inversion {n i R} :
    τ[n] (Tm.univ i, R)
    → Spine.t n (Tm.univ i, R).
  Proof.
    move=> ?.
    by Tower.destruct_tower.
  Qed.

  Ltac tac :=
    simpl;
    match goal with
    | |- τω ⊧ _ ≫ _ ∼ _ => move=> ? ? ?; tac
    | |- τω ⊧ 𝕌[_] ∼ 𝕌[_] => apply: formation_ω
    | |- τω ⊧ _ ∼ _ => apply: Level.eq_ty_from_level; tac
    | |- τ[_] ⊧ _ ∼ _ => apply: inversion
    end.
End Univ.


Module Unit.
  Theorem formation i :
    τ[i] ⊧ 𝟙 ∼ 𝟙.
  Proof.
    unshelve Tac.prove; constructor.
  Qed.

  Theorem ax_equality :
    τω ⊧ 𝟙 ∋ ★ ∼ ★.
  Proof.
    unshelve Tac.prove; constructor.
  Qed.
End Unit.

Module Bool.
  Theorem tt_equality :
    τω ⊧ 𝟚 ∋ Tm.tt ∼ Tm.tt.
  Proof.
    unshelve Tac.prove; constructor.
  Qed.

  Theorem ff_equality :
    τω ⊧ 𝟚 ∋ Tm.ff ∼ Tm.ff.
  Proof.
    unshelve Tac.prove; constructor.
  Qed.

  Theorem formation i :
    τ[i] ⊧ 𝟚 ∼ 𝟚.
  Proof.
    Tac.prove.
  Qed.

  Ltac tac :=
    simpl;
    match goal with
    | |- τ[_] ⊧ 𝟚 ∼ 𝟚 => apply: formation
    | |- τω ⊧ 𝟚 ∋ _ ∼ _ => apply: tt_equality + apply: ff_equality
    | |- τω ⊧ 𝕌[_] ∋ _ ∼ _ => apply: Univ.intro; tac
    end.
End Bool.

Module Fam.

  Local Hint Extern 40 => Term.simplify_subst.
  Local Hint Resolve General.mem_eq_refl_left General.mem_eq_symm.


  (* This is a very bad proof, sorry. *)
  Theorem family_choice {τ A0 A1 B0 B1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A0 ∼ A1
    → τ ⊧ ⋄ ∙ A0 ≫ B0 ∼ B1
    → ∃ (R : Tm.t 0 → rel),
      ∀ e0 e1,
        τ ⊧ A0 ∋ e0 ∼ e1
        → R e0 = R e1
          ∧ τ ((B0 ⫽ Sub.inst0 e0)%tm, R e0)
          ∧ τ ((B1 ⫽ Sub.inst0 e1)%tm, R e1)
          ∧ τ ((B0 ⫽ Sub.inst0 e1)%tm, R e0)
          ∧ τ ((B1 ⫽ Sub.inst0 e0)%tm, R e0).
  Proof.
    move=> 𝒟 ℰ.
    exists (fun e =>
         fun es =>
           τ ⊧ A0 ∋ e ∼ e
           → τ ⊧ B0 ⫽ Sub.inst0 e ∋ (π₁ es) ∼ (π₂ es)).

    move=> e0 e1 ℱ.
    destruct (ℰ (Sub.inst0 e1) (Sub.inst0 e0)) as [Rℰ [ℰ0 ℰ1]]; eauto.
    destruct (ℰ (Sub.inst0 e0) (Sub.inst0 e0)) as [Rℰ' [ℰ0' ℰ1']]; eauto.

    repeat split.
    - T.eqcd; case => e'0 e'1 //=.
      apply: propositional_extensionality; split => 𝒢 ℋ.
      + case: 𝒢 => [|R [𝒢1 𝒢2]]; eauto.
        eexists; split; eauto.
        replace Rℰ with R; eauto.
        apply: TS.is_extensional; eauto; simpl.
        replace Rℰ with Rℰ'; eauto.
        apply: TS.is_extensional; eauto.
      + case: 𝒢 => [|R [𝒢1 𝒢2]]; eauto.
        eexists; split; eauto.
        replace Rℰ' with R; eauto.
        apply: TS.is_extensional; eauto; simpl.
        replace Rℰ' with Rℰ; eauto.
        apply: TS.is_extensional; eauto.
    - T.use ℰ0'; repeat f_equal.
      T.eqcd; case => e'0 e'1 //=.
      apply: propositional_extensionality; split.
      * move=> e'0e'1 e0e0 //=.
        eexists; split; eauto.
      * move=> //= 𝒢.
        destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
        replace Rℰ' with R𝒢; eauto.
        apply: TS.is_extensional; eauto.
    - destruct (ℰ (Sub.inst0 e1) (Sub.inst0 e1)) as [Rℰ'' [ℰ0'' ℰ1'']]; eauto.
      T.use ℰ1''; repeat f_equal.
      T.eqcd; case => e'0 e'1 //=.
      apply: propositional_extensionality; split.
      + move=> e'0e'1 e1e1 //=.
        eexists; split; eauto.
      + move=> //= 𝒢.
        destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
        replace Rℰ'' with R𝒢; eauto.
        apply: TS.is_extensional; eauto.
    - destruct (ℰ (Sub.inst0 e1) (Sub.inst0 e1)) as [Rℰ'' [ℰ0'' ℰ1'']]; eauto.
      T.use ℰ0''; repeat f_equal.
      T.eqcd; case => e'0 e'1 //=.
      apply: propositional_extensionality; split.
      + move=> e'0e'1 e1e1 //=.
        exists Rℰ''; split; auto.
        replace Rℰ'' with Rℰ'; auto.
        replace Rℰ' with Rℰ.
        * apply: TS.is_extensional; first by [exact ℰ0]; eauto.
        * apply: TS.is_extensional; eauto.
      + move=> //= 𝒢.
        destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
        replace Rℰ'' with R𝒢; eauto.
        replace R𝒢 with Rℰ'.
        * replace Rℰ' with Rℰ.
          ** apply: TS.is_extensional; first by [exact ℰ0]; eauto.
          ** apply: TS.is_extensional; eauto.
        * apply: TS.is_extensional; first by [exact ℰ0']; eauto.

    - T.use ℰ1'; repeat f_equal.
      T.eqcd; case => e'0 e'1 //=.
      apply: propositional_extensionality; split.
      + move=> e'0e'1 e1e1 //=.
        eexists; split; eauto.
      + move=> //= 𝒢.
        destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
        replace Rℰ' with R𝒢; eauto.
        apply: TS.is_extensional; eauto.
  Qed.

  Ltac quantifier_formation_tac :=
    let 𝒟 := fresh in
    let Rℰspec := fresh in
    let e0 := fresh in
    let e1 := fresh in
    let R𝒟 := fresh in
    let Q := fresh in

    move=> 𝒟 /(Fam.family_choice 𝒟) [Rℰ Rℰspec];
    case: 𝒟 => R𝒟 [𝒟0 𝒟1];

    eexists; split; Tac.tower_intro;
    (apply: Sig.conn; first by eauto);
    (econstructor; first by eauto);
    move=> e0 e1 e01;
    (case: (Rℰspec e0 e1); first by [exists R𝒟]);
    move=> Q [? [? [? ?]]]; repeat split; eauto;
    rewrite -Q; eauto.

End Fam.

Module Arr.
  Local Hint Extern 40 => Term.simplify_subst.
  Local Hint Resolve General.mem_eq_refl_left General.mem_eq_symm.

  Theorem formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ (⋄ ∙ A0) ≫ B0 ∼ B1
    → τ[n] ⊧ (A0 ⇒ B0) ∼ (A1 ⇒ B1).
  Proof.
    by Fam.quantifier_formation_tac.
  Qed.

  Theorem univ_eq {i A0 A1 B0 B1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ ⋄ ∙ A0 ≫ 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ 𝕌[i] ∋ (A0 ⇒ B0) ∼ (A1 ⇒ B1).
  Proof.
    move=> /Univ.inversion 𝒟 /Univ.open_inversion ℰ.
    apply: Univ.intro.
    apply: formation.
    - assumption.
    - apply: ℰ.
      split; auto.
      move=> ? ? ?; Term.simplify_subst.
      apply: General.ty_eq_refl_left; eauto.
  Qed.

  Theorem intro {i A B f0 f1} :
    τω ⊧ ⋄ ∙ A ≫ B ∋ f0 ∼ f1
    → τ[i] ⊧ A ∼ A
    → τ[i] ⊧ ⋄ ∙ A ≫ B ∼ B
    → τω ⊧ (A ⇒ B) ∋ 𝛌{f0} ∼ 𝛌{f1}.
  Proof.
    move=> 𝒟 ℰ /(Fam.family_choice ℰ) ℱ.
    apply: (Level.eq_mem_from_level i).
    case: ℰ => Rℰ [ℰ0 _].
    case: ℱ => Rℱ ℱsp.
    eexists; split.
    - Tac.tower_intro.
      apply: Sig.conn; first by auto.
      econstructor; eauto.
      move=> e0 e1 e0e1.
      case: (ℱsp e0 e1); auto.
      + eexists; eauto.
      + move=> Q [? [? ?]].
        repeat T.split; eauto.
    - econstructor; eauto.
      constructor => e0 e1 e0e1.
      case: (ℱsp e0 e1); auto.
      + eexists; eauto.
      + move=> ? [? [? [? ?]]].
        edestruct (𝒟 (Sub.inst0 e0) (Sub.inst0 e1)) as [R𝒟 [? ?]]; simpl.
        * split; first by auto.
          Term.simplify_subst.
          eexists; split; eauto.
          eexists; eauto.
        * replace (Rℱ e0) with R𝒟; auto.
          apply: TS.is_extensional; eauto; simpl.
          eexists; eauto.
  Qed.

  Theorem elim {i A B f0 f1 e0 e1} :
    τ[i] ⊧ A ∼ A
    → τ[i] ⊧ ⋄ ∙ A ≫ B ∼ B
    → τω ⊧ (A ⇒ B) ∋ f0 ∼ f1
    → τω ⊧ A ∋ e0 ∼ e1
    → τω ⊧ (B ⫽ Sub.inst0 e0) ∋ (f0 ⋅ e0) ∼ (f1 ⋅ e1).
  Proof.
    move=> 𝒟 /(Fam.family_choice 𝒟) [Rℰ Rℰsp] /Level.eq_mem_to_level [nℱ ℱ] /Level.eq_mem_to_level [n𝒢 𝒢].
    case: ℱ => Rℱ [ℱ0 ℱ1].
    case: (Rℰsp e0 e1).
    - apply: Level.mem_eq_at_lvl_of_typehood; eauto.
    - Tower.destruct_tower.
      dependent destruction ℱ1.
      dependent destruction H1.
      dependent destruction H.
      dependent destruction H0.
      move=> Q [ℰ0 [ℰ1 [ℰ2 ℰ3]]].
      apply: General.mem_eq_conv_both.
      + apply: OpSem.app_lam; eauto.
      + apply: OpSem.app_lam; eauto.
      + apply: Level.eq_mem_from_level.
        eexists; split; eauto.
        case: 𝒢 => R𝒢 [𝒢0 𝒢1].
        suff e0e1 : R0 (e0, e1).
        * replace (Rℰ e0) with (R1 e0); auto.
          apply: TS.is_extensional; eexists; eauto.
          case: (H3 e0 e1); auto => ? [? ?]; eauto.
        * replace R0 with R𝒢; auto.
          apply: TS.is_extensional; eexists; eauto.
  Qed.
End Arr.

Module Prod.
  Local Hint Extern 40 => Term.simplify_subst.
  Local Hint Resolve General.mem_eq_refl_left General.mem_eq_symm.


  Theorem formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ (⋄ ∙ A0) ≫ B0 ∼ B1
    → τ[n] ⊧ (A0 × B0) ∼ (A1 × B1).
  Proof.
    by Fam.quantifier_formation_tac.
  Qed.

  Theorem univ_eq {i A0 A1 B0 B1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ ⋄∙A0 ≫ 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ 𝕌[i] ∋ (A0 × B0) ∼ (A1 × B1).
  Proof.
    move=> /Univ.inversion 𝒟 /Univ.open_inversion ℰ.
    apply: Univ.intro.
    apply: formation.
    - assumption.
    - apply: ℰ.
      split; auto.
      move=> ? ? ?; Term.simplify_subst.
      apply: General.ty_eq_refl_left; eauto.
  Qed.


  Theorem intro i {A B e00 e01 e10 e11} :
    τω ⊧ A ∋ e00 ∼ e10
    → τω ⊧ B ⫽ Sub.inst0 e00 ∋ e01 ∼ e11
    → τ[i] ⊧ A ∼ A
    → τ[i] ⊧ ⋄∙A ≫ B ∼ B
    → τω ⊧ (A × B) ∋ ⟨e00, e01⟩ ∼ ⟨e10, e11⟩.
  Proof.
    move=>
     /Level.eq_mem_to_level [n1 𝒟]
     /Level.eq_mem_to_level [n2 ℰ]
     ℱ
     /(Fam.family_choice ℱ) => 𝒢.

    apply: (Level.eq_mem_from_level (i + n1 + n2)).
    case: 𝒟 => [R𝒟 [𝒟0 𝒟1]].
    case: 𝒢; eauto.
    - move=> R𝒢 𝒢.
      eexists; split.
      + Tac.tower_intro; apply: Sig.conn; auto.
        apply: (@Connective.has_prod _ _ _ R𝒟 R𝒢); eauto.
        * Tac.tower_mono.
        * move=> e0 e1 p.
          specialize (𝒢 e0 e1).
          suff ℋ: τ[i] ⊧ A ∋ e0 ∼ e1.
          ** case: (𝒢 ℋ) => ? [? [? [? ?]]].
             repeat split; auto;
             by Tac.tower_mono.
          ** apply: Level.mem_eq_at_lvl_of_typehood.
             *** exists R𝒟; split; eauto.
             *** eauto.
      + econstructor; eauto.
        constructor; eauto.
        case: ℰ => Rℰ [ℰ0 ℰ1].
        replace (R𝒢 e00) with Rℰ; auto.

        specialize (𝒢 e00 e10).
        suff ℋ: τ[i] ⊧ A ∋ e00 ∼ e10.
        * case: (𝒢 ℋ) => ? [? [? [? ?]]].
          apply: TS.is_extensional; eexists; eauto.
        * apply: Level.mem_eq_at_lvl_of_typehood.
          ** exists R𝒟; split; eauto.
          ** eauto.
  Qed.


  Theorem ind_formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ B0 ∼ B1
    → τ[n] ⊧ (A0 × B0.[^1]) ∼ (A1 × B1.[^1]).
  Proof.
    move=> [R𝒟 [𝒟0 𝒟1]] [Rℰ [ℰ0 ℰ1]].
    eexists; split; Tac.tower_intro; apply: Sig.conn; auto;
    apply: (@Connective.has_prod _ _ _ R𝒟 (fun _ => Rℰ)); eauto;
    move=> e0 e1 e01; repeat T.split; Term.simplify_subst; eauto.
  Qed.

  Theorem ind_univ_eq {i A0 A1 B0 B1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ 𝕌[i] ∋ (A0 × B0.[^1]) ∼ (A1 × B1.[^1]).
  Proof.
    move=> /Univ.inversion 𝒟 /Univ.inversion ℰ.
    apply: Univ.intro.
    by apply: ind_formation.
  Qed.

  Theorem ind_intro {A B e00 e01 e10 e11} :
    τω ⊧ A ∋ e00 ∼ e10
    → τω ⊧ B ∋ e01 ∼ e11
    → τω ⊧ (A × B.[^1]) ∋ ⟨e00, e01⟩ ∼ ⟨e10, e11⟩.
  Proof.
    move=> /Level.eq_mem_to_level [n1 [R𝒟 [𝒟0 𝒟1]]] /Level.eq_mem_to_level [n2 [Rℰ [ℰ0 ℰ1]]].
    apply: (Level.eq_mem_from_level (n1 + n2)).
    eexists; split.
    - Tac.tower_intro; apply: Sig.conn; auto.
      apply: (@Connective.has_prod _ _ _ R𝒟 (fun _ => Rℰ)).
      + Tac.tower_mono.
      + move=> e0 e1 e0e1; repeat split; Term.simplify_subst; auto; Tac.tower_mono.
    - eauto.
  Qed.
End Prod.

Module TowerChoice.
  Lemma ty_eq {n : nat} {A1 A2 : 𝕂 → Tm.t 0} :
    (∀ κ, ∃ Rκ, τ[n] (A1 κ, Rκ) ∧ τ[n] (A2 κ, Rκ))
    → ∃ S, ∀ κ, τ[n] (A1 κ, S κ) ∧ τ[n] (A2 κ, S κ).
  Proof.
    move=> X.
    apply (@unique_choice _ _ (fun κ R => τ[n] (A1 κ, R) ∧ τ[n] (A2 κ, R))) => κ.
    case: (X κ) => S T.
    eexists; split; eauto => S' T';
    apply: TS.is_extensional; eexists;
    T.destruct_conjs; eauto.
  Qed.

  Lemma mem_eq {n : nat} {A : 𝕂 → Tm.t 0} {e0 e1} :
    (∀ κ, ∃ Rκ, τ[n] (A κ, Rκ) ∧ Rκ (e0, e1))
    → ∃ S, ∀ κ, τ[n] (A κ, S κ) ∧ S κ (e0, e1).
  Proof.
    move=> X.
    apply (@unique_choice _ _ (fun κ R => τ[n] (A κ, R) ∧ R (e0, e1))) => κ.
    case: (X κ) => S T.
    eexists; split; eauto => S' T';
    apply: TS.is_extensional; eexists;
    T.destruct_conjs; eauto.
  Qed.
End TowerChoice.

Module Isect.
  Theorem formation {n B0 B1} :
    (∀ κ, τ[n] ⊧ (B0 κ) ∼ (B1 κ))
    → τ[n] ⊧ ⋂ B0 ∼ ⋂ B1.
  Proof.
    move=> 𝒟.
    case: (TowerChoice.ty_eq 𝒟) => S ℰ.
    Tac.prove;
    T.specialize_hyps;
    rewrite /Tower.t in ℰ;
    T.destruct_conjs; eauto.
  Qed.

  Theorem intro_at_lvl {n A e0 e1} :
    (∀ κ, τ[n] ⊧ (A κ) ∋ e0 ∼ e1)
    → τ[n] ⊧ ⋂ A ∋ e0 ∼ e1.
  Proof.
    move=> 𝒟.
    case: (TowerChoice.mem_eq 𝒟) => S ℰ.
    Tac.prove.
    - T.specialize_hyps;
      rewrite /Tower.t in ℰ;
      T.destruct_conjs; eauto.
    - move=> κ.
      T.specialize_hyps.
      case: ℰ => [_ ?].
      eauto.
  Qed.

  (* NOTE that the type equality premise is necessary for this rule to be true! *)
  Theorem intro {A e0 e1} :
    τω ⊧ (⋂ A) ∼ (⋂ A)
    → (∀ κ, τω ⊧ (A κ) ∋ e0 ∼ e1)
    → τω ⊧ ⋂ A ∋ e0 ∼ e1.
  Proof.
    move=> /Level.eq_ty_to_level [n𝒟 𝒟] ℰ.
    apply: (Level.eq_mem_from_level n𝒟).
    apply: intro_at_lvl => κ.
    T.specialize_hyps.

    case: {ℰ} (Level.eq_mem_to_level ℰ) => nℰ ℰ.
    apply: Level.mem_eq_at_lvl_of_typehood; first by eassumption.

    case: 𝒟 => R [𝒟 _].
    Tower.destruct_tower.
    eexists; split; T.specialize_hyps; eauto.
  Qed.



  Definition cext_transparent (R : rel) (es : Tm.t 0 × Tm.t 0) :=
    exists v0 v1, π₁ es ⇓ v0 ∧ π₂ es ⇓ v1 ∧ R (v0, v1).

  Theorem cext_implies_cext_transparent {R es} :
    Connective.cext R es
    → cext_transparent R es.
  Proof.
    case: es => e0 e1; move=> 𝒞.
    dependent destruction 𝒞.
    exists v0, v1; eauto.
  Qed.

  Lemma cext_equiv_cext_transparent :
    Connective.cext = cext_transparent.
  Proof.
    T.eqcd => R.
    T.eqcd; case => e0 e1.
    apply: propositional_extensionality; split.
    - apply: cext_implies_cext_transparent.
    - move=> //= [v0 [v1 ?]].
      T.destruct_conjs.
      econstructor; eauto.
  Qed.

  Theorem cartesian {n A0 B0 A1 B1} :
    (∀ κ, τ[n] ⊧ (A0 κ) ∼ (A1 κ))
    → (∀ κ, τ[n] ⊧ (B0 κ) ∼ (B1 κ))
    → τ[n] ⊧ (⋂[κ] (A0 κ × (B0 κ).[^1])) ∼ ((⋂ A1) × (⋂ B1).[^1]).
  Proof.
    move=> 𝒟 ℰ.
    case: (TowerChoice.ty_eq 𝒟) => S𝒟 𝒟'.
    case: (TowerChoice.ty_eq ℰ) => Sℰ ℰ'.
    esplit; split.

    - Tac.prove; T.specialize_hyps; T.destruct_conjs.
      rewrite /Tower.t -Clo.roll.
      apply: Sig.conn; auto.
      apply: (@Connective.has_prod _ _ _ _ (fun _ => _)).
      + eauto.
      + move=> ? ? ?; repeat T.split; Term.simplify_subst; eauto.

    - Tac.ts_flex_rel.
      + Tac.tower_intro.
        apply: Sig.conn; auto.
        evar (R : rel).
        apply: (@Connective.has_prod _ _ _ _ (fun _ => R)); rewrite /R; clear R.
        * Tac.tower_intro.
          apply: Sig.conn; auto.
          apply: Connective.has_isect => κ.
          T.specialize_hyps; T.destruct_conjs; Tac.prove.
        * move=> e0 e1 //= e0e1; repeat T.split; auto; Tac.tower_intro; Term.simplify_subst; Tac.prove; T.specialize_hyps; T.destruct_conjs; Term.simplify_subst; eauto.

      + T.eqcd; case => e0 e1.
        apply: propositional_extensionality; split => H.

        * rewrite cext_equiv_cext_transparent in H.
          case: LocalClock => κ₀ _.
          case: (H κ₀) => //= [v0 [v1 [? [? ?]]]].

          econstructor; eauto.
          Tac.destruct_prod_val.
          constructor => κ;
          case: (H κ) => //= [v0' [v1' [? [? ?]]]];
          Tac.destruct_prod_val;
          OpSem.evals_to_eq;
          by T.destruct_eqs.

        * Connective.destruct_cext.
          repeat Tac.destruct_prod_val;
          eauto.
  Qed.

  Theorem irrelevance {i A B}:
    τ[i] ⊧ A ∼ B
    → τ[i] ⊧ A ∼ ⋂[_] B.
  Proof.
    Tac.prove.

    match goal with
    | |- Connective.has _ _ (_, ?R) =>
      replace R with (fun e0e1 => ∀ κ:𝕂, R e0e1)
    end.

    + Tac.prove.
    + T.eqcd => ?.
      apply: propositional_extensionality.
      case: LocalClock => ? _.
      T.split; eauto.
  Qed.
End Isect.

(* TODO: move these elsewhere *)
Theorem rel_total : Later.Total rel.
Proof.
  by rewrite /rel.
Qed.

Theorem rel_inh : Later.Inh rel.
Proof.
  by rewrite /rel.
Qed.

Hint Resolve rel_total rel_inh.

Module Later.
  Theorem formationω {κ} {A B} :
    ▷[κ] (τω ⊧ A ∼ B)
    → τω ⊧ ▶[κ] A ∼ ▶[κ] B.
  Proof.
    move=> /Later.yank_existential; case; auto.
    move=> R H0.
    suff: ▷[κ] (∃ n, τ[n] (A, R) ∧ τ[n] (B, R)).
    - move=> /Later.yank_existential; case; auto.
      move=> n H1.
      Tac.prove; Later.gather; case; Tac.prove.
    - Later.gather.
      move=> [[n1 H1] [n2 H2]].
      Tac.accum_lvl n.
      exists n.
      split; Tac.tower_mono.
  Qed.

  Theorem intro {κ} {A e1 e2} :
    ▷[κ] (τω ⊧ A ∋ e1 ∼ e2)
    → τω ⊧ ▶[κ] A ∋ e1 ∼ e2.
  Proof.
    move=> /Later.yank_existential.
    case; eauto.
    move=> R 𝒟.
    rewrite Later.cart in 𝒟.
    case: 𝒟 => [/Later.yank_existential 𝒟0 𝒟1].
    case: 𝒟0; eauto.
    move=> n 𝒟0.
    Tac.prove.
  Qed.

  (* This proof is really horrific! And I apparently didn't use it. *)
  Theorem mem_univ_inversion {κ i} {A0 A1} :
    (τω ⊧ 𝕌[i] ∋ ▶[κ] A0 ∼ ▶[κ] A1)
    → ▷[κ] (τω ⊧ 𝕌[i] ∋ A0 ∼ A1).
  Proof.
    move=> /Level.eq_mem_to_level [n [R [𝒟 A0A1]]].
    Tower.destruct_tower.
    induction n; Spine.simplify; try by [contradiction].
    case: H => //= [j [? [? [Rspec]]]].
    apply: Later.push_existential.
    exists R.
    OpSem.destruct_evals.
    rewrite Later.cart.
    split.
    - apply: Later.next.
      exists (S n).
      rewrite /Tower.t -Clo.roll.
      apply: Sig.init.
      Spine.simplify.
      eauto.
    - rewrite Rspec in A0A1.
      case: A0A1 => //= [S [H1 H2]].
      replace (Clo.t (Spine.t j)) with (Tower.t j) in H1, H2; last by [auto].
      Tower.destruct_tower.
      Tower.destruct_tower.
      suff: ▷[κ] (R = R0).
      + move=> E; Later.gather.
        move=> //= [H5 [H6 E]].
        exists R; split; first by [auto].
        by rewrite -E in H5.
      + refine (Later.map (functional_extensionality R R0) _).
        apply: Later.push_universal.
        move=> e0e1.
        rewrite -Later.commute_eq.
        by apply: (equal_f x).
  Qed.

  Theorem univ_eq {κ i} {A0 A1} :
    τω ⊧ ▶[κ] 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ 𝕌[i] ∋ ▶[κ] A0 ∼ ▶[κ] A1.
  Proof.
    move=> /Level.eq_mem_to_level [n [R [𝒟 ℰ]]].
    Tower.destruct_tower.
    esplit; T.split.
    - exists (i + 1).
      Tac.prove.
      replace (i + 1) with (S i); last by [omega].
      Spine.simplify.
      esplit; repeat T.split; eauto.
      reflexivity.
    - have H1 := Later.map Univ.spine_inversion H0.
      induction n.
      + exists (fun _ => ▷[κ0] ⊤).
        (* any relation will do! *)
        replace (Clo.t (Spine.t i)) with τ[i]; last by [auto].
        split; simpl; Tac.prove;
        Later.gather => *; T.destruct_conjs;
        Spine.simplify; by [contradiction].
      + move {IHn}; suff: ▷[κ0] (τ[i] ⊧ A0 ∼ A1).
        * move=> /Later.yank_existential; case; eauto.
          move=> S H2; rewrite Later.cart in H2.
          case: H2 => [H20 H21].
          exists (fun e0e1 => ▷[κ0] (S e0e1)).
          simpl in *.
          split; rewrite -Clo.roll;
          (apply: Sig.conn; first by [eauto]);
          by [apply: Connective.has_later].
        * Later.gather.
          move=> [H1 [H2 H3]].
          Spine.simplify.
          case: H3 => [j [? [? R0spec]]].
          OpSem.destruct_evals.
          simpl in *; by [rewrite R0spec in H1].
  Qed.

  Lemma force_reflexive {i A} :
    (τ[i] ⊧ ⋂ A ∼ ⋂ A)
    → τ[i] ⊧ ⋂[κ] ▶[κ] (A κ) ∼ ⋂[κ] (A κ).
  Proof.
    move=> [R [𝒟 _]].
    exists R; T.split; auto.
    Tower.destruct_tower.
    replace (fun e0e1 => ∀ κ, S κ e0e1) with (fun e0e1 => ∀ κ, ▷[κ] (S κ e0e1)).
    - Tac.prove.
      T.specialize_hyps.
      rewrite -Clo.roll.
      by Tac.prove; apply: Later.next.
    - T.eqcd => ?.
      apply: Later.force.
  Qed.


  Theorem force {i A B} :
    (τ[i] ⊧ ⋂ A ∼ ⋂ B)
    → τ[i] ⊧ ⋂[κ] ▶[κ] A κ ∼ ⋂[κ] B κ.
  Proof.
    move=> 𝒟.
    apply: General.ty_eq_trans.
    - eassumption.
    - apply: force_reflexive.
      apply: General.ty_eq_refl_left.
      eassumption.
  Qed.


  Theorem loeb_induction_closed κ {A e0 e1} :
    τω ⊧ ⋄ ∙ ▶[κ]A ≫ A.[^1] ∋ e0 ∼ e1
    → τω ⊧ A ∋ (Tm.fix_ e0) ∼ (Tm.fix_ e1).
  Proof.
    move=> 𝒟.
    apply: (@Later.loeb κ).
    move=> /Later.yank_existential; case; auto; move=> R ℰ.
    rewrite Later.cart in ℰ.
    case: ℰ => /Later.yank_existential; case; auto => n ℰ1 ℰ2.

    T.efwd 𝒟.
    - apply: General.mem_eq_conv_both.
      + move=> v; case: (fix_unfold e0 v) => _; apply.
      + move=> v; case: (fix_unfold e1 v) => _; apply.
      + T.use 𝒟; f_equal; by Term.simplify_subst.

    - simpl; split; auto.
      exists (fun e0e1 => ▷[κ] (R e0e1)); split.
      + exists n.
        Tac.prove.
        Later.gather.
        move=> [? ?].
          by rewrite Tm.subst_ret.
      + by Later.gather; case.
  Qed.
End Later.


Module Canonicity.
  Definition quote_bool (b : bool) : Tm.t 0 :=
    match b with
    | true => Tm.tt
    | false => Tm.ff
    end.

  Notation "⌊ b ⌋𝔹" := (quote_bool b).

  Theorem canonicity {e} :
    τω ⊧ 𝟚 ∋ e ∼ e
    → ∃ b : bool, e ⇓ ⌊b⌋𝔹.
  Proof.
    move=> /Level.eq_mem_to_level [n [R [𝒟 ?]]].
    Tower.destruct_tower.
    Connective.destruct_cext.
    dependent destruction H1.
    - by exists true.
    - by exists false.
  Qed.
End Canonicity.