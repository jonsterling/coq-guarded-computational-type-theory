Require Import Unicode.Utf8 Program.Tactics Program.Equality Program.Basics Logic.FunctionalExtensionality.

Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Var OrderTheory Axioms Program OpSem Closure Tower Sequent TypeSystem.
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

  (* When you need to show 'τ[n] (A, R)' but R is not of the right
   shape.  This tactic will replace R with a unification variable,
   which allows you to make progress in your proof; then, you have to
   prove hat R was is the same as whatever the unification variable
   got instantiated to. *)

  Ltac ts_choose_rel myrel :=
    match goal with
    | |- τ[_] (_, ?R) =>
      (suff: R = myrel); first T.rewrite_
    end.

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
    | |- Sig.t _ _ (Prog.univ _, _) => apply: Sig.init
    | |- Sig.t _ _ (_, _) => apply: Sig.conn
    | |- Spine.t _ (Prog.univ _, _) => Spine.simplify; repeat T.split; [idtac | eauto | reflexivity] ; eauto
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


  (* TODO: get rid of this, since it only really works in the easy cases. *)
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

  Theorem eq_mem_from_level n {A M1 M2} :
    τ[n] ⊧ A ∋ M1 ∼ M2
    → τω ⊧ A ∋ M1 ∼ M2.
  Proof.
    move=> [R [TA M1M2]].
    eexists.
    split.
    + eexists; eauto.
    + eauto.
  Qed.

  Theorem eq_mem_to_level {A M1 M2} :
    τω ⊧ A ∋ M1 ∼ M2
    → ∃ n, τ[n] ⊧ A ∋ M1 ∼ M2.
  Proof.
    move=> [R [[n𝒟 𝒟] M1M2]].
    exists n𝒟, R.
    T.split.
    - Tac.tower_mono.
    - auto.
  Qed.


  Lemma eq_env_from_level {Ψ} {Γ : Prectx Ψ} i {γ0 γ1} :
    τ[i] ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τω ⊧ Γ ∋⋆ γ0 ∼ γ1.
  Proof.
    move=> 𝒟.
    induction Γ; simpl; repeat split.
    - apply: IHΓ.
      by case: 𝒟.
    - apply: eq_mem_from_level.
      case: 𝒟 => _ //= ?.
      eauto.
  Qed.

  Lemma mem_eq_at_lvl_of_typehood {m n A B M0 M1} :
    τ[n] ⊧ A ∋ M0 ∼ M1
    → τ[m] ⊧ A ∼ B
    → τ[m] ⊧ A ∋ M0 ∼ M1.
  Proof.
    move=> [R [𝒟0 𝒟1]] [S [ℰ0 ℰ1]].
    exists S; split; first by assumption.
    replace S with R; first by assumption.
    apply: TS.is_extensional;
    eexists; eassumption.
  Qed.
End Level.



Module General.
  Theorem replace_ty_in_mem_eq {τ A0 A1 M1 M2} `{TS.extensional τ} :
    τ ⊧ A0 ∋ M1 ∼ M2
    → τ ⊧ A0 ∼ A1
    → τ ⊧ A1 ∋ M1 ∼ M2.
  Proof.
    move=> [R1 [? ?]] [R2 [? ?]].
    exists R2; split; auto.
    replace R2 with R1; auto.
    apply: TS.is_extensional; eauto.
  Qed.

  Theorem ty_eq_refl_left {τ A B} :
    τ ⊧ A ∼ B
    → τ ⊧ A ∼ A.
  Proof.
    move=> [? [? ?]].
    eexists; eauto.
  Qed.

  Theorem ty_eq_symm {τ A B} :
    τ ⊧ A ∼ B
    → τ ⊧ B ∼ A.
  Proof.
    move=> [? [? ?]].
    eexists; eauto.
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

  Theorem mem_eq_conv_ty {τ A0 A1 M0 M1} `{TS.type_computational τ} :
    A0 ≼₀ A1
    → τ ⊧ A0 ∋ M0 ∼ M1
    → τ ⊧ A1 ∋ M0 ∼ M1.
  Proof.
    move=> A01 [R [𝒟 M01]].
    exists R; split; auto.
    apply: TS.is_type_computational; eauto.
  Qed.

  Theorem mem_eq_symm {τ A M0 M1} `{TS.cper_valued τ} :
    τ ⊧ A ∋ M0 ∼ M1
    → τ ⊧ A ∋ M1 ∼ M0.
  Proof.
    move=> [R [𝒟 ℰ]].
    exists R; split; auto.
    apply: symmetric; auto.
    apply: per.
    apply: TS.is_cper_valued.
    eauto.
  Qed.

  Theorem mem_eq_conv {τ A M00 M01 M1} `{TS.cper_valued τ} :
    M00 ≼₀ M01
    → τ ⊧ A ∋ M00 ∼ M1
    → τ ⊧ A ∋ M01 ∼ M1.
  Proof.
    move=> M00M01 [R [ℰ M00M1]].
    exists R; split; auto.
    apply: crel; eauto.
    apply: TS.is_cper_valued; eauto.
  Qed.


  Theorem mem_eq_conv_both {τ A M00 M01 M10 M11} `{TS.cper_valued τ} :
    M00 ≼₀ M01
    → M10 ≼₀ M11
    → τ ⊧ A ∋ M00 ∼ M10
    → τ ⊧ A ∋ M01 ∼ M11.
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

  Theorem mem_eq_trans {τ A M0 M1 M2} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A ∋ M1 ∼ M2
    → τ ⊧ A ∋ M0 ∼ M1
    → τ ⊧ A ∋ M0 ∼ M2.
  Proof.
    Tac.prove.
    apply: transitive; eauto.
    - apply: per.
      apply: TS.is_cper_valued; eauto.
    - match goal with
      | H : ?R1 (M1, M2) |- ?R2 (M1, M2) =>
        replace R2 with R1; auto
      end.
      apply: TS.is_extensional; eauto.
  Qed.

  Theorem mem_eq_refl_left {τ A M0 M1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A ∋ M0 ∼ M1
    → τ ⊧ A ∋ M0 ∼ M0.
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


  Theorem open_mem_eq_refl_left {Ψ} {Γ : Prectx Ψ} {τ A A' M0 M1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ Γ ctx
    → τ ⊧ Γ ≫ A ∼ A'
    → τ ⊧ Γ ≫ A ∋ M0 ∼ M1
    → τ ⊧ Γ ≫ A ∋ M0 ∼ M0.
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
    - by induction Γ.
  Qed.


  Lemma open_inversion {Ψ} {Γ : Prectx Ψ} {i A0 A1} :
    τω ⊧ Γ ≫ 𝕌[i] ∋ A0 ∼ A1
    → τ[i] ⊧ Γ ≫ A0 ∼ A1.
  Proof.
    move=> 𝒟 γ0 γ1 γ01.
    specialize (𝒟 γ0 γ1).
    apply: inversion.
    apply: 𝒟.
    apply: Level.eq_env_from_level.
    eauto.
  Qed.

  Theorem spine_inversion {n i R} :
    τ[n] (Prog.univ i, R)
    → Spine.t n (Prog.univ i, R).
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
    τω ⊧ 𝟚 ∋ Prog.tt ∼ Prog.tt.
  Proof.
    unshelve Tac.prove; constructor.
  Qed.

  Theorem ff_equality :
    τω ⊧ 𝟚 ∋ Prog.ff ∼ Prog.ff.
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

  Local Hint Extern 40 => Program.simplify_subst.
  Local Hint Resolve General.mem_eq_refl_left General.mem_eq_symm.


  (* This is a very bad proof, sorry. *)
  Theorem family_choice {τ A0 A1 B0 B1} `{TS.cper_valued τ} `{TS.extensional τ} :
    τ ⊧ A0 ∼ A1
    → τ ⊧ ⋄ ∙ A0 ≫ B0 ∼ B1
    → ∃ (R : Prog.t 0 → rel),
      ∀ M0 M1,
        τ ⊧ A0 ∋ M0 ∼ M1
        → R M0 = R M1
          ∧ τ ((B0 ⫽ Sub.inst0 M0)%prog, R M0)
          ∧ τ ((B1 ⫽ Sub.inst0 M1)%prog, R M0)
          ∧ τ ((B0 ⫽ Sub.inst0 M1)%prog, R M0)
          ∧ τ ((B1 ⫽ Sub.inst0 M0)%prog, R M0).
  Proof.
    move=> 𝒟 ℰ.
    set R := (fun M =>
         fun es =>
           τ ⊧ A0 ∋ M ∼ M
           → τ ⊧ B0 ⫽ Sub.inst0 M ∋ (π₁ es) ∼ (π₂ es)).

    exists R.

    move=> M0 M1 ℱ.
    destruct (ℰ (Sub.inst0 M1) (Sub.inst0 M0)) as [Rℰ [ℰ0 ℰ1]]; eauto.
    destruct (ℰ (Sub.inst0 M0) (Sub.inst0 M0)) as [Rℰ' [ℰ0' ℰ1']]; eauto.

    suff: R M0 = R M1.
    - move=> Q; repeat split; auto.
      + T.use ℰ0'; repeat f_equal.
        T.eqcd; case => M'0 M'1 //=.
        apply: propositional_extensionality; split.
        * move=> M'0M'1 M0M0 //=.
          eexists; split; eauto.
        * move=> //= 𝒢.
          destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
          replace Rℰ' with R𝒢; eauto.
          apply: TS.is_extensional; eauto.

      + destruct (ℰ (Sub.inst0 M1) (Sub.inst0 M1)) as [Rℰ'' [ℰ0'' ℰ1'']]; eauto.
        T.use ℰ1''; repeat f_equal.
        rewrite Q.
        T.eqcd; case => M'0 M'1 //=.
        apply: propositional_extensionality; split.
        * move=> M'0M'1 M1M1 //=.
          eexists; split; eauto.
        * move=> //= 𝒢.
          destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
          replace Rℰ'' with R𝒢; eauto.
          apply: TS.is_extensional; eauto.
      +  destruct (ℰ (Sub.inst0 M1) (Sub.inst0 M1)) as [Rℰ'' [ℰ0'' ℰ1'']]; eauto.
         T.use ℰ0''; repeat f_equal.
         rewrite Q.
         T.eqcd; case => M'0 M'1 //=.
         apply: propositional_extensionality; split.
         * move=> M'0M'1 M1M1 //=.
           exists Rℰ''; split; auto.
         * move=> //= 𝒢.
           destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
           replace Rℰ'' with R𝒢; eauto.
           apply: TS.is_extensional; eauto.

      + T.use ℰ1'; repeat f_equal.
        T.eqcd; case => M'0 M'1 //=.
        apply: propositional_extensionality; split.

        * move=> M'0M'1 M1M1 //=.
          eexists; split; eauto.
        * move=> //= 𝒢.
          destruct 𝒢 as [R𝒢 [𝒢0 𝒢1]]; eauto.
          replace Rℰ' with R𝒢; eauto.
          apply: TS.is_extensional; eauto.

    - T.eqcd; case => M'0 M'1 //=.
      apply: propositional_extensionality; split => 𝒢 ℋ.
      + case: 𝒢 => [|S [𝒢1 𝒢2]]; eauto.
        eexists; split; eauto.
        replace Rℰ with S; eauto.
        apply: TS.is_extensional; eauto; simpl.
        replace Rℰ with Rℰ'; eauto.
        apply: TS.is_extensional; eauto.
      + case: 𝒢 => [|S [𝒢1 𝒢2]]; eauto.
        eexists; split; eauto.
        replace Rℰ' with S; eauto.
        apply: TS.is_extensional; eauto; simpl.
        replace Rℰ' with Rℰ; eauto.
        apply: TS.is_extensional; eauto.
  Qed.

End Fam.

Module Arr.
  Theorem formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ (⋄ ∙ A0) ≫ B0 ∼ B1
    → τ[n] ⊧ (A0 ⇒ B0) ∼ (A1 ⇒ B1).
  Proof.
    move=> 𝒟 /(Fam.family_choice 𝒟) [ℰ Rℰsp].
    case: 𝒟 => R𝒟 [𝒟0 𝒟1].

    eexists; split; Tac.tower_intro;
    (apply: Sig.conn; first by eauto);
    (econstructor; first by eauto).
    - move=> M0 M1 M0M1;
      (case: (Rℰsp M0 M1); first by [exists R𝒟]).
      move=> Q [? [? [? ?]]];
      repeat split; eauto;
      rewrite -Q; eauto.
    - move=> M0 M1 M0M1;
      (case: (Rℰsp M0 M1); first by [exists R𝒟]).
      move=> Q [? [? [? ?]]];
      repeat split; eauto; by rewrite -Q.
  Qed.

  Theorem univ_eq {i A0 A1 B0 B1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ ⋄ ∙ A0 ≫ 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ 𝕌[i] ∋ (A0 ⇒ B0) ∼ (A1 ⇒ B1).
  Proof.
    move=> /Univ.inversion 𝒟 /Univ.open_inversion ℰ.
    apply: Univ.intro.
    apply: formation; auto.
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
      move=> M0 M1 M0M1.
      case: (ℱsp M0 M1); auto.
      + eexists; eauto.
      + move=> Q [? [? [? ?]]].
        repeat T.split; eauto;
        by rewrite -Q.
    - econstructor=> M0 M1 M0M1.
      suff ? : is_cper (Rℱ M0).
      + apply: crel.
        * destruct (ℱsp M0 M1); auto.
          by exists Rℰ.
        * by apply: OpSem.app_lam.
        * apply: symmetric.
          ** by apply: per.
          ** apply: crel; first by auto.
             *** by apply: OpSem.app_lam.
             *** edestruct (𝒟 (Sub.inst0 M0) (Sub.inst0 M1)) as [R𝒟 [𝒟0 𝒟1]]; eauto.
                 **** simpl; split; auto.
                      simplify_subst.
                      exists Rℰ; split; eauto.
                      eexists; eauto.
                 **** replace (Rℱ M0) with R𝒟.
                      ***** apply: symmetric; auto.
                            apply: per; apply: TS.is_cper_valued; eauto.
                      ***** edestruct ℱsp; first by [exists Rℰ; eauto].
                            T.destruct_conjs.
                            apply: TS.is_extensional; eauto.
                            eexists; eauto.
      + edestruct ℱsp; eauto.
        * eexists Rℰ; eauto.
        * T.destruct_conjs.
          apply: TS.is_cper_valued; eauto.
          eexists; eauto.
  Qed.

  Theorem elim {i A B f0 f1 M0 M1} :
    τ[i] ⊧ A ∼ A
    → τ[i] ⊧ ⋄ ∙ A ≫ B ∼ B
    → τω ⊧ (A ⇒ B) ∋ f0 ∼ f1
    → τω ⊧ A ∋ M0 ∼ M1
    → τω ⊧ (B ⫽ Sub.inst0 M0) ∋ (f0 ⋅ M0) ∼ (f1 ⋅ M1).
  Proof.
    move=> 𝒟 /(Fam.family_choice 𝒟) [Rℰ Rℰsp] /Level.eq_mem_to_level [nℱ ℱ] /Level.eq_mem_to_level [n𝒢 𝒢].
    case: ℱ => Rℱ [ℱ0 ℱ1].
    case: (Rℰsp M0 M1).
    - apply: Level.mem_eq_at_lvl_of_typehood; eauto.
    - Tower.destruct_tower.
      dependent destruction ℱ1.
      move=> Q [ℰ0 [ℰ1 [ℰ2 ℰ3]]].
      eexists; split.
      + eexists; eauto.
      + replace (Rℰ M0) with (R1 M0).
        * apply: H; eauto.
          case: 𝒢 => R𝒢 [𝒢0 𝒢1].
          replace R0 with R𝒢; auto.
          apply: TS.is_extensional; eexists; eauto.
        * edestruct H1; eauto.
          ** case: 𝒢 => R𝒢 [𝒢0 𝒢1].
             replace R0 with R𝒢; eauto.
             apply: TS.is_extensional; eexists; eauto.
          ** T.destruct_conjs.
             apply: TS.is_extensional; eexists; eauto.
  Qed.
End Arr.


Module Prod.
  Local Hint Extern 40 => simplify_subst.
  Local Hint Resolve General.mem_eq_refl_left General.mem_eq_symm.


  Theorem formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ (⋄ ∙ A0) ≫ B0 ∼ B1
    → τ[n] ⊧ (A0 × B0) ∼ (A1 × B1).
  Proof.
    move=> 𝒟 /(Fam.family_choice 𝒟) [ℰ Rℰsp].
    case: 𝒟 => R𝒟 [𝒟0 𝒟1].

    eexists; split; Tac.tower_intro;
    (apply: Sig.conn; first by eauto);
    (econstructor; first by eauto).
    - move=> M0 M1 M0M1;
      (case: (Rℰsp M0 M1); first by [exists R𝒟]).
      move=> Q [? [? [? ?]]];
      repeat split; eauto;
      rewrite -Q; eauto.
    - move=> M0 M1 M0M1;
      (case: (Rℰsp M0 M1); first by [exists R𝒟]).
      move=> Q [? [? [? ?]]];
      repeat split; eauto; by rewrite -Q.
  Qed.


  Theorem univ_eq {i A0 A1 B0 B1} :
    τω ⊧ 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ ⋄∙A0 ≫ 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ 𝕌[i] ∋ (A0 × B0) ∼ (A1 × B1).
  Proof.
    move=> /Univ.inversion 𝒟 /Univ.open_inversion ℰ.
    apply: Univ.intro.
    apply: formation; auto.
  Qed.


  Theorem intro i {A B M00 M01 M10 M11} :
    τω ⊧ A ∋ M00 ∼ M10
    → τω ⊧ B ⫽ Sub.inst0 M00 ∋ M01 ∼ M11
    → τ[i] ⊧ A ∼ A
    → τ[i] ⊧ ⋄∙A ≫ B ∼ B
    → τω ⊧ (A × B) ∋ ⟨M00, M01⟩ ∼ ⟨M10, M11⟩.
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
        constructor; eauto.
        * Tac.tower_mono.
        * move=> M0 M1 p.
          specialize (𝒢 M0 M1).
          suff ℋ: τ[i] ⊧ A ∋ M0 ∼ M1.
          ** case: (𝒢 ℋ) => Q [? [? [? ?]]].
             repeat split; auto; (rewrite -Q; Tac.tower_mono) || Tac.tower_mono.
          ** apply: Level.mem_eq_at_lvl_of_typehood; eauto.
             exists R𝒟; split; eauto.
      + constructor.
        * apply: crel.
          ** apply: TS.is_cper_valued; eexists; eauto.
          ** apply: OpSem.fst_pair.
          ** apply: symmetric; first by [apply: per; apply: TS.is_cper_valued; eexists; eauto].
             apply: crel.
             *** apply: TS.is_cper_valued; eexists; eauto.
             *** apply: OpSem.fst_pair.
             *** apply: symmetric; auto.
                 apply: per; apply: TS.is_cper_valued; eexists; eauto.
        * case: ℰ => Rℰ [ℰ0 ℰ1].
          replace (R𝒢 (⟨M00, M01⟩.1)%prog) with Rℰ; auto.
          ** apply: crel.
             *** apply: TS.is_cper_valued; eexists; eauto.
             *** apply: OpSem.snd_pair.
             *** apply: symmetric; first by [apply: per; apply: TS.is_cper_valued; eexists; eauto].
                 apply: crel.
                 **** apply: TS.is_cper_valued; eexists; eauto.
                 **** apply: OpSem.snd_pair.
                 **** apply: symmetric; auto.
                      apply: per; apply: TS.is_cper_valued; eexists; eauto.
          ** edestruct (𝒢 M00(⟨M10, M11⟩.1)%prog).
             *** apply: General.mem_eq_conv_both.
                 **** auto.
                 **** apply: OpSem.fst_pair.
                 **** apply: Level.mem_eq_at_lvl_of_typehood; first (exists R𝒟); eauto.
             *** edestruct (𝒢 (⟨M00, M01⟩.1)%prog (⟨M10, M11⟩.1)%prog).
                 **** apply: General.mem_eq_conv_both.
                      ***** apply: OpSem.fst_pair.
                      ***** apply: OpSem.fst_pair.
                      ***** apply: Level.mem_eq_at_lvl_of_typehood; first (exists R𝒟); eauto.
                 **** destruct H0 as [H01 [H02 [H03 H04]]].
                      destruct H2 as [H21 [H22 [H23 H24]]].
                      apply: (TS.is_extensional τω); eauto.
                      ***** eexists; eauto.
                      ***** exists i; simpl.
                            rewrite H in H04.
                            by rewrite H1.
  Qed.
End Prod.

Module TowerChoice.
  Lemma ty_eq {n : nat} {A1 A2 : 𝕂 → Prog.t 0} :
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

  Lemma mem_eq {n : nat} {A : 𝕂 → Prog.t 0} {M0 M1} :
    (∀ κ, ∃ Rκ, τ[n] (A κ, Rκ) ∧ Rκ (M0, M1))
    → ∃ S, ∀ κ, τ[n] (A κ, S κ) ∧ S κ (M0, M1).
  Proof.
    move=> X.
    apply (@unique_choice _ _ (fun κ R => τ[n] (A κ, R) ∧ R (M0, M1))) => κ.
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

  Theorem intro_at_lvl {n A M0 M1} :
    (∀ κ, τ[n] ⊧ (A κ) ∋ M0 ∼ M1)
    → τ[n] ⊧ ⋂ A ∋ M0 ∼ M1.
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
  Theorem intro {A M0 M1} :
    τω ⊧ (⋂ A) ∼ (⋂ A)
    → (∀ κ, τω ⊧ (A κ) ∋ M0 ∼ M1)
    → τω ⊧ ⋂ A ∋ M0 ∼ M1.
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
      + move=> ? ? ?; repeat T.split; Program.simplify_subst; eauto.

    - Tac.ts_flex_rel.
      + Tac.tower_intro.
        apply: Sig.conn; auto.
        evar (R : rel).
        apply: (@Connective.has_prod _ _ _ _ (fun _ => R)); rewrite /R; clear R.
        * Tac.tower_intro.
          apply: Sig.conn; auto.
          apply: Connective.has_isect => κ.
          T.specialize_hyps; T.destruct_conjs; Tac.prove.
        * move=> M0 M1 //= M0M1;
          repeat T.split; auto;
          Tac.tower_intro; Program.simplify_subst;
          Tac.prove; T.specialize_hyps;
          T.destruct_conjs; Program.simplify_subst; eauto.

      + T.eqcd; case => M0 M1.
        apply: propositional_extensionality; (split => H; first constructor) => κ;
        T.specialize_hyps; by dependent destruction H.
  Qed.

  Theorem irrelevance {i A B}:
    τ[i] ⊧ A ∼ B
    → τ[i] ⊧ A ∼ ⋂[_] B.
  Proof.
    Tac.prove.

    match goal with
    | |- Connective.has _ _ (_, ?R) =>
      replace R with (fun M0M1 => ∀ κ:𝕂, R M0M1)
    end.

    + Tac.prove.
    + T.eqcd => ?.
      apply: propositional_extensionality.
      case: LocalClock => ? _.
      T.split; eauto.
  Qed.
End Isect.

Module Later.
  Ltac prove_pick_eq :=
    match goal with
    | |- ?τ @ ?A = ?R => by [eapply TS.Pick_lemma; eauto]
    | |- ?R = ?τ @ ?A => by [symmetry; eapply TS.Pick_lemma; eauto]
    end.

  Hint Extern 5 => prove_pick_eq.

  Theorem formation {κ n} {A B} :
    ▷[κ] (τ[n] ⊧ A ∼ B)
    → τ[n] ⊧ ▶[κ] A ∼ ▶[κ] B.
  Proof.
    move => 𝒟.
    unfold atomic_eq_ty in 𝒟.
    exists (fun es => ▷[κ] (τ[n] @ A es)); split.
    - Tac.tower_intro; apply: Sig.conn; eauto.
      apply: Connective.has_later.
      Later.gather; case=> R' [AR' BR'].
      T.use AR'.
      rewrite /Tower.t Clo.roll; repeat f_equal; eauto.

    - Tac.tower_intro; apply: Sig.conn; eauto.
      apply: Connective.has_later.
      Later.gather; case=> R' [AR' BR'].
      T.use BR'.
      rewrite /Tower.t Clo.roll; repeat f_equal; eauto.
  Qed.

  Lemma level_commute_eq_ty {A B} :
    τω ⊧ A ∼ B
    → ∃ n, τ[n] ⊧ A ∼ B.
  Proof.
    case => R [[n1 AR] [n2 BR]].
    exists (n1 + n2).
    exists R; split;
    Tac.tower_mono.
  Qed.

  Lemma level_commute_eq_mem {A M0 M1} :
    τω ⊧ A ∋ M0 ∼ M1
    → ∃ n, τ[n] ⊧ A ∋ M0 ∼ M1.
  Proof.
    case => R [[n AR] M0M1].
    exists n; exists R; auto.
  Qed.

  Theorem intro {κ} {A M1 M2} :
    ▷[κ] (τω ⊧ A ∋ M1 ∼ M2)
    → τω ⊧ ▶[κ] A ∋ M1 ∼ M2.
  Proof.
    move=> /(Later.map level_commute_eq_mem).
    move=> /Later.yank_existential; case; auto => n 𝒟.
    exists (fun es => ▷[κ] (τ[n] @ A es)).
    split.
    - exists n; Tac.tower_intro.
      apply: Sig.conn; eauto.
      apply: Connective.has_later.
      Later.gather; case => R' [AR' M0M1].
      T.use AR'; rewrite /Tower.t Clo.roll; repeat f_equal; eauto.
    - Later.gather; case=> R' [AR' M0M1].
      T.use M0M1; repeat f_equal.
      apply: equal_f; eauto.
  Qed.

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
      + apply: (Later.map (functional_extensionality R R0)).
        apply: Later.push_universal.
        move=> M0M1.
        apply: Later.commute_eq.
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
        * move=> 𝒟.
          exists (fun es => ▷[κ0] (τ[i] @ A0 es)); split; simpl.
          ** Tac.tower_intro; apply: Sig.conn; eauto.
             apply: Connective.has_later.
             rewrite Clo.roll.
             Later.gather; case=> A0A1 [UiR0 [UiR0' [S [A0S A1S]]]].
             T.use A0S; rewrite /Tower.t; repeat f_equal; eauto.
          ** rewrite -Clo.roll; apply: Sig.conn; eauto.
             apply: Connective.has_later.
             Later.gather; case => A0A1 [UiR0 [UiR0' [S [A0S A1S]]]].
             T.use A1S; rewrite /Tower.t; repeat f_equal; eauto.
        * Later.gather; case => H1 [H2 H3].
          Spine.simplify; simpl in *.
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
    replace (fun M0M1 => ∀ κ, S κ M0M1) with (fun M0M1 => ∀ κ, ▷[κ] (S κ M0M1)).
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


  Theorem loeb_induction_closed κ i {A B M0 M1} :
    τ[i] ⊧ A ∼ B
    → τω ⊧ ⋄ ∙ ▶[κ]A ≫ A.[^1] ∋ M0 ∼ M1
    → τω ⊧ A ∋ 𝛍{ M0 } ∼ 𝛍{ M1 }.
  Proof.
    move=> [R [AR _]] ℰ.
    apply: (@Later.loeb κ).

    move=> ℱ.
    T.efwd ℰ.
    - apply: General.mem_eq_conv_both.
      + move=> V; case: (fix_unfold M0 V) => _; apply.
      + move=> V; case: (fix_unfold M1 V) => _; apply.
      + T.use ℰ; f_equal; by Program.simplify_subst.
    - simpl; split; auto.
      exists (fun M0M1 => ▷[κ] (R M0M1)); split.
      + exists i.
        Tac.prove.
        Later.gather.
        move=> [? ?].
          by rewrite Prog.subst_ret.
      + Later.gather; case => R' [AR' mue0mue1].
        replace R with R'; auto.
        apply: TS.is_extensional.
        * exact AR'.
        * eexists; eauto.
  Qed.

  Lemma fun_ty_inversion {i A B R} :
    τ[i] ((A ⇒ B)%prog, R)
    → ∃ (RA : rel) (RB : Prog.t 0 → rel),
      τ[i] (A, RA)
      ∧ (∀ M0 M1 : Prog.t 0,
            RA (M0, M1)
            → τ[i] ((B ⫽ Sub.inst0 M0)%prog, RB M0)
              ∧ τ[i] ((B ⫽ Sub.inst0 M0)%prog, RB M1)
              ∧ τ[i] ((B ⫽ Sub.inst0 M1)%prog, RB M1)
              ∧ τ[i] ((B ⫽ Sub.inst0 M1)%prog, RB M0))
      ∧ R = Connective.fun_el RA RB.
  Proof.
    move=> 𝒟.
    Tower.destruct_tower.
    eauto.
  Qed.

  Theorem apply κ {A B f0 f1} :
    τω ⊧ ▶[κ] (A ⇒ B) ∋ f0 ∼ f1
    → τω ⊧ (▶[κ] A) ⇒ (▶[κ] B) ∋ f0 ∼ f1.
  Proof.
    move=> /Level.eq_mem_to_level [n𝒟 [R𝒟 [𝒟0 𝒟1]]].
    apply: (Level.eq_mem_from_level n𝒟).
    Tower.destruct_tower.

    exists (Connective.fun_el (fun es => ▷[κ0] (τ[n𝒟] @ A es)) (fun x => fun es => ▷[κ0] (τ[n𝒟] @ (B ⫽ Sub.inst0 x)%prog es))).
    split.
    - Tac.tower_intro; apply: Sig.conn; eauto.
      apply: Connective.has_arr.
      + rewrite !Clo.roll.
        Tac.tower_intro; apply: Sig.conn; eauto.
        apply: Connective.has_later.
        Later.gather; case=> M0M1 ABR.
        rewrite Clo.roll.
        Tower.destruct_tower.
        T.use H1; repeat f_equal; eauto.
      + rewrite !Clo.roll.
        move=> M0 M1 M0M1; repeat split;
        Tac.tower_intro;
        (apply: Sig.conn; first by [simpl; eauto]);
        apply: Connective.has_later; rewrite !Clo.roll;
        Later.gather; case=> X1 [X2 X3]; Tower.destruct_tower;
        specialize (H2 M0 M1); (edestruct H2 as [H3 [H4 [H5 H6]]]; first by [T.use X3; apply: equal_f; eauto]).
        * T.use H4; repeat f_equal; eauto.
        * T.use H4; repeat f_equal; eauto.
        * T.use H5; repeat f_equal; eauto.
        * T.use H6; repeat f_equal; eauto.

    - split=> M0 M1 M0M1.
      Later.gather; case=> f0f1 [H1 H2].
      Tower.destruct_tower.
      dependent destruction f0f1.
      specialize (H M0 M1).
      T.efwd_thru H.
      + apply: equal_f.
        edestruct H3 as [H5 [H6 [H7 H8]]]; eauto.
      + T.use H2; apply: equal_f; eauto.
  Qed.

  Lemma existential_trickery {A} {P Q : A → Prop} :
    (∀ (x : {x : A | P x}), Q (proj1_sig x))
    → (∀ x : A, P x → Q x).
  Proof.
    move=> H x px.
    apply: (H (exist _ x px)).
  Defined.

  Theorem pi_later_univ_eq i κ {A0 A1 B0 B1} :
    τω ⊧ ▶[κ] 𝕌[i] ∋ A0 ∼ A1
    → τω ⊧ ⋄ ∙ A0 ≫ ▶[κ] 𝕌[i] ∋ B0 ∼ B1
    → τω ⊧ ▶[κ] 𝕌[i] ∋ (A0 ⇒ B0) ∼ (A1 ⇒ B1).
  Proof.
    move=> [R𝒟 [𝒟0 𝒟1]] ℰ.
    exists R𝒟; split; eauto.
    case: 𝒟0 => n 𝒟0.
    Tower.destruct_tower.

    suff ℱ : ▷[κ0] (τω ⊧ ⋄ ∙ A0 ≫ 𝕌[i] ∋ B0 ∼ B1).
    - Later.gather.
      case => X [Y Z].
      rewrite -Clo.roll in Y.
      dependent induction n.
      + Clo.destruct_sig.
        * contradiction.
        * OpSem.destruct_evals.
          Clo.destruct_has.
      + Clo.destruct_sig; Spine.simplify.
        * case: H => //= [j [? [? Q]]].
          OpSem.destruct_evals.
          rewrite Q //=; rewrite Q //= in X.

          ecase (@Fam.family_choice τ[j]); try by [typeclasses eauto].
          ** eauto.
          ** apply: Univ.open_inversion; eauto.
          ** move=> Rℰ Rℰsp.
             case: X => RA [X0 X1].
             eexists; split; Tac.tower_intro;
             (apply: Sig.conn; first by [auto]);
             (constructor; first by [eassumption]);
             move=> M0 M1 M0M1;
             (case: (Rℰsp M0 M1); first by [eexists; split; eauto]);
             move=> Q' ?; T.destruct_conjs; repeat split; eauto; by rewrite -Q'.
        * OpSem.destruct_evals.
          dependent induction H1.

    - apply: Later.push_universal => γ0.
      apply: (Later.map existential_trickery).
      apply: Later.push_universal; case => γ1 γ01 //=.
      apply: mem_univ_inversion.
      apply: univ_eq.
      by apply: ℰ.
  Qed.


  Theorem preserves_sigma i κ {A0 A1 B0 B1} :
    ▷[κ] (τ[i] ⊧ A0 ∼ A1)
    → ▷[κ] (τ[i] ⊧ ⋄ ∙ A0 ≫ B0 ∼ B1)
    → τ[i] ⊧ ▶[κ] (A0 × B0) ∼ ((▶[κ] A1) × (▶[κ] B1)).
  Proof.
    move=> 𝒟 ℰ.
    apply: General.ty_eq_symm.

    exists (Connective.prod_el (fun es => ▷[κ] (τ[i] @ A1 es)) (fun x => fun es => ▷[κ] (τ[i] @ (B1 ⫽ Sub.inst0 x)%prog es))).
    split.

    - Tac.tower_intro; apply: Sig.conn; eauto.
      constructor; rewrite !Clo.roll.
      + Tac.tower_intro; apply: Sig.conn; eauto.
        apply: Connective.has_later.
        Later.gather; case=> 𝒟 _.
(*        move=> /(Fam.family_choice 𝒟); case=> RB ℰ.*)
        rewrite !Clo.roll.
        case: 𝒟 => RA [𝒟0 𝒟1].
        T.use 𝒟1; rewrite /Tower.t; repeat f_equal; eauto.
      + move=> M0 M1 M0M1; repeat split;
        Tac.tower_intro; (apply: Sig.conn; first by [simpl; eauto]);
        apply: Connective.has_later; Later.gather; case=> 𝒟 [/(Fam.family_choice 𝒟)] => ℰ ℱ;
        rewrite !Clo.roll; case: ℰ => R ℰ; specialize (ℰ M0 M1);
        (destruct ℰ as [H1 [H2 [H3 [H4 H5]]]];
          first by
              [ exists (τ[i] @ A0); split; case 𝒟=> RA [𝒟0 𝒟1];
                [ T.use 𝒟0; repeat f_equal; eauto
                | T.use ℱ; apply: equal_f; apply: (TS.is_extensional τ[i]); simpl; T.use 𝒟1; repeat f_equal; eauto
                ]
              ]);
        [T.use H5 | T.use H5 | T.use H3 | T.use H3];
        rewrite /Tower.t; repeat f_equal; eauto.

    - Tac.ts_choose_rel (fun Ms => ▷[κ] (Connective.prod_el (τ[i] @ A1) (fun x => τ[i] @ (B1 ⫽ Sub.inst0 x)%prog) Ms)).
      + Tac.tower_intro; apply: Sig.conn; eauto.
        apply: Connective.has_later.
        Later.gather; case=> 𝒟 /(Fam.family_choice 𝒟) [RB ℰ]; rewrite !Clo.roll.
        Tac.tower_intro; apply: Sig.conn; eauto.
        apply: Connective.has_prod; rewrite !Clo.roll.
        * case: 𝒟 => RA [𝒟0 𝒟1].
          T.use 𝒟0; rewrite /Tower.t; repeat f_equal; eauto.
        * move=> M0 M1 M0M1; specialize (ℰ M0 M1).
          destruct ℰ as [ℰ1 [ℰ2 [ℰ3 [ℰ4 ℰ5]]]].
          ** exists (τ[i] @ A1); split; eauto.
             case: 𝒟 => RA [𝒟0 𝒟1]; T.use 𝒟0; repeat f_equal; eauto.
          ** repeat split; [T.use ℰ2 | T.use ℰ2 | T.use ℰ4 | T.use ℰ4];
             rewrite /Tower.t; repeat f_equal; eauto.
      + apply: binrel_extensionality => M0 M1; split.
        * move=> H.
          dependent destruction H.
          Later.gather; case=> ? [? [? ?]].
          constructor; eauto.
        * move=> H.
          constructor; Later.gather; case=> 𝒟 [ℰ X];
          dependent destruction X; eauto.
  Qed.
End Later.


Module Canonicity.
  Definition quote_bool (b : bool) : Prog.t 0 :=
    match b with
    | true => Prog.tt
    | false => Prog.ff
    end.

  Notation "⌊ b ⌋𝔹" := (quote_bool b).

  Theorem canonicity {M} :
    τω ⊧ 𝟚 ∋ M ∼ M
    → ∃ b : bool, M ⇓ ⌊b⌋𝔹.
  Proof.
    move=> /Level.eq_mem_to_level [n [R [𝒟 ?]]].
    Tower.destruct_tower.
    Connective.destruct_cext.
    dependent destruction H1.
    - by exists true.
    - by exists false.
  Qed.
End Canonicity.