Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Term.
From gctt Require Import Closure.
From gctt Require Import Tower.
From gctt Require Import Sequent.

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.omega.Omega.
Open Scope program_scope.


Set Implicit Arguments.

Module Closed.
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

    Ltac tower_ext :=
      let n := fresh in
      accum_lvl n;
      apply: (@Tower.extensionality n).

    Ltac tower_mono :=
      apply: Tower.monotonicity; last by [eassumption];
      cbn; omega.

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
      | |- _ val => econstructor
      | |- _ ⇓ _ => econstructor
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

  Theorem unit_formation {n : nat} :
    τ[n] ⊧ Tm.unit ∼ Tm.unit.
  Proof.
    Tac.prove.
  Qed.

  Theorem unit_ax_equality {n : nat} :
    τ[n] ⊧ Tm.unit ∋ Tm.ax ∼ Tm.ax.
  Proof.
    Tac.prove.
  Qed.

  Lemma univ_formation_S {n : nat} :
    τ[S n] ⊧ (Tm.univ n) ∼ (Tm.univ n).
  Proof.
    Tac.prove.
  Qed.

  Theorem univ_formation {n i : nat} :
    i < n
    → τ[n] ⊧ (Tm.univ i) ∼ (Tm.univ i).
  Proof.
    case => [| j q ].
    + apply: univ_formation_S.
    + Tac.prove.
  Qed.

  Theorem prod_formation {n A0 A1 B0 B1} :
    τ[n] ⊧ A0 ∼ A1
    → τ[n] ⊧ B0 ∼ B1
    → τ[n] ⊧ (Tm.prod A0 B0) ∼ (Tm.prod A1 B1).
  Proof.
    Tac.prove.
  Qed.

  Theorem prod_intro {n A B e00 e01 e10 e11} :
    τ[n] ⊧ A ∋ e00 ∼ e10
    → τ[n] ⊧ B ∋ e01 ∼ e11
    → τ[n] ⊧ (Tm.prod A B) ∋ (Tm.pair e00 e01) ∼ (Tm.pair e10 e11).
  Proof.
    Tac.prove.
  Qed.


  Lemma TowerChoice {n : nat} {A1 A2 : CLK → Tm.t 0} :
    (∀ κ, ∃ Rκ, τ[n] (A1 κ, Rκ) ∧ τ[n] (A2 κ, Rκ))
    → ∃ S, ∀ κ, τ[n] (A1 κ, S κ) ∧ τ[n] (A2 κ, S κ).
  Proof.
    move=> X.
    apply: (unique_choice (fun κ R => τ[n] (A1 κ, R) ∧ τ[n] (A2 κ, R))) => κ.
    case: (X κ) => S T.
    eexists; split; eauto => S' T';
    apply: Tower.extensionality; eauto;
    T.destruct_conjs; eauto.
  Qed.

  Theorem isect_formation {n B0 B1} :
    (∀ κ, τ[n] ⊧ (B1 κ) ∼ (B0 κ))
    → τ[n] ⊧ (Tm.isect B0) ∼ (Tm.isect B1).
  Proof.
    move=> 𝒟.
    case: (TowerChoice 𝒟) => S ℰ.
    Tac.prove;
      T.specialize_hyps;
      rewrite /Tower.t in ℰ;
      T.destruct_conjs; eauto.
  Qed.

  Theorem isect_irrelevance {A B}:
    τω ⊧ A ∼ B
    → τω ⊧ A ∼ (Tm.isect (fun _ => B)).
  Proof.
    Tac.prove.

    match goal with
    | |- Connective.has _ _ (_, ?R) =>
      replace R with (fun e0e1 => ∀ κ:CLK, R e0e1)
    end.

    + Tac.prove.
    + T.eqcd => ?.
      apply: propositional_extensionality.
      case: LocalClock => ? _.
      T.split; eauto.
  Qed.

  Theorem eq_ty_from_level {n A B} :
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

  Theorem eq_mem_from_level {n A e1 e2} :
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

  Theorem behavior_total : Later.Total Matrix.behavior.
  Proof.
    by rewrite /Matrix.behavior.
  Qed.

  Theorem behavior_inh : Later.Inh Matrix.behavior.
    by rewrite /Matrix.behavior.
  Qed.

  Hint Resolve behavior_total behavior_inh.

  Theorem later_formation {κ n} {A B} :
    ▷[κ] (τ[n] ⊧ A ∼ B)
    → τ[n] ⊧ (Tm.ltr κ A) ∼ (Tm.ltr κ B).
  Proof.
    move=> /Later.yank_existential;
    case=> *; eauto.
    Tac.prove; Later.gather; case; Tac.prove.
  Qed.

  Theorem later_intro {κ} {A e1 e2} :
    ▷[κ] (τω ⊧ A ∋ e1 ∼ e2)
    → τω ⊧ (Tm.ltr κ A) ∋ e1 ∼ e2.
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

  (* This proof is really horrific! *)
  Theorem later_mem_univ_inversion {κ i} {A0 A1} :
    τω ⊧ (Tm.univ i) ∋ (Tm.ltr κ A0) ∼ (Tm.ltr κ A1)
    → ▷[κ] (τω ⊧ (Tm.univ i) ∋ A0 ∼ A1).
  Proof.
    move=> /eq_mem_to_level [n [R [𝒟 A0A1]]].
    Tower.destruct_tower.
    induction n; Spine.simplify; try by [contradiction].
    case: H => //= [j [? [? [Rspec]]]].
    Term.destruct_evals.
    apply: Later.push_existential.
    exists R.
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
        exists R.
        split; first by [auto].
        by rewrite -E in H5.
      + refine (Later.map (functional_extensionality R R0) _).
        apply: Later.push_universal.
        move=> e0e1.
        rewrite -Later.commute_eq.
        have x' := equal_f x.
        by specialize (x' e0e1).
  Qed.


  Theorem later_force {A} :
    τω ⊧ (Tm.isect A) ∼ (Tm.isect A)
    → τω ⊧ (Tm.isect (λ κ, Tm.ltr κ (A κ))) ∼ (Tm.isect A).
  Proof.
    move=> [R [[nH H] _]].
    exists R; T.split; auto; exists nH.
    Tower.destruct_tower.
    replace (fun e0e1 => ∀ κ, S κ e0e1) with (fun e0e1 => ∀ κ, ▷[κ] (S κ e0e1)).
    - Tac.prove.
      T.specialize_hyps.
      rewrite -Clo.roll.
      by Tac.prove; apply: Later.next.
    - T.eqcd => ?.
      apply: Later.force.
    - auto.
  Qed.


  Theorem rewrite_ty_in_mem {A0 A1 e1 e2} :
    τω ⊧ A0 ∋ e1 ∼ e2
    → τω ⊧ A0 ∼ A1
    → τω ⊧ A1 ∋ e1 ∼ e2.
  Proof.
    Tac.prove.

    match goal with
    | _ : ?R0 ?X |- ?R1 ?X =>
      replace R1 with R0; auto
    end.

    Tac.tower_ext; Tac.tower_mono.
  Qed.

  Theorem later_force_mem {A e0 e1} :
    τω ⊧ (Tm.isect A) ∼ (Tm.isect A)
    → τω ⊧ (Tm.isect (λ κ, Tm.ltr κ (A κ))) ∋ e0 ∼ e1
    → τω ⊧ Tm.isect A ∋ e0 ∼ e1.
  Proof.
    move=> 𝒟 ℰ.
    apply: rewrite_ty_in_mem.
    - eauto.
    - by apply: later_force.
  Qed.

  Theorem ty_eq_refl_left {A B} :
    τω ⊧ A ∼ B
    → τω ⊧ A ∼ A.
  Proof.
    Tac.prove.
  Qed.

  Theorem ty_eq_symm {A B} :
    τω ⊧ A ∼ B
    → τω ⊧ B ∼ A.
  Proof.
    Tac.prove.
  Qed.

  Theorem ty_eq_trans {A B C} :
    τω ⊧ B ∼ C
    → τω ⊧ A ∼ B
    → τω ⊧ A ∼ C.
  Proof.
    move=> [R1 [[? 𝒟0] [? 𝒟1]]] [R2 [[? ℰ0] [? ℰ1]]].
    exists R2; T.split.
    - eexists; eauto.
    - replace R2 with R1.
      + eexists; eauto.
      + symmetry; Tac.tower_ext; Tac.tower_mono.
  Qed.

  Theorem env_eq_sym {Ψ} {Γ : Prectx Ψ} {γ0 γ1} :
    τω ⊧ Γ ctx
    → τω ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τω ⊧ Γ ∋⋆ γ1 ∼ γ0.
  Proof.
    move=> Γctx γ01.
    induction Γ; eauto.
    split; simplify_eqs.
    - apply: IHΓ; eauto.
      + by case: Γctx.
      + by case: γ01.
    - have: τω ⊧ t ⫽ (γ1 ∘ Fin.FS) ∼ (t ⫽ (γ0 ∘ Fin.FS)).
      + case: Γctx => _ 𝒟.
        apply: ty_eq_symm.
        apply: 𝒟.
        by case: γ01.
      + move=> [R [[? 𝒟0] [? 𝒟1]]].
        case: γ01 => [_ [S [[n ℰ] γ01]]].
        destruct (Tower.per_valued ℰ) as [symm _].
        exists R; T.split.
        * eexists; eauto.
        * replace R with S.
          ** by apply: symm.
          ** Closed.Tac.tower_ext; Closed.Tac.tower_mono.
  Qed.

  Theorem env_eq_refl_left {Ψ} {Γ : Prectx Ψ} {γ0 γ1} :
    τω ⊧ Γ ctx
    → τω ⊧ Γ ∋⋆ γ0 ∼ γ1
    → τω ⊧ Γ ∋⋆ γ0 ∼ γ0.
  Proof.
    move=> Γctx γ01.
    induction Γ; eauto.
    split; simplify_eqs.
    - apply: IHΓ.
      + by case: Γctx.
      + case: γ01; eauto.
    - have: τω ⊧ t ⫽ (γ0 ∘ Fin.FS) ∼ (t ⫽ (γ0 ∘ Fin.FS)).
      + case: Γctx => _ 𝒟.
        apply: ty_eq_refl_left.
        apply: 𝒟.
        case: γ01.
        eauto.
      + move=> [R [[? 𝒟0] [? 𝒟1]]].
        case: γ01 => [_ [S [[n ℰ] γ01]]].
        destruct (Tower.per_valued ℰ) as [symm trans].
        exists R; T.split.
        * eexists; eauto.
        * move: ℰ γ01; simplify_eqs; move=> ℰ γ01.
          replace R with S.
          ** apply: trans; eauto.
          ** Closed.Tac.tower_ext; Closed.Tac.tower_mono.
  Qed.

  Hint Resolve unit_formation univ_formation eq_ty_from_level eq_mem_from_level prod_formation isect_formation isect_irrelevance unit_ax_equality later_formation later_intro later_force ty_eq_refl_left ty_eq_trans ty_eq_symm rewrite_ty_in_mem.

  Theorem test : τω ⊧ (Tm.prod Tm.unit (Tm.univ 0)) ∼ (Tm.prod Tm.unit (Tm.univ 0)).
  Proof.
    eauto.
  Qed.

  Theorem test2 : τω ⊧ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)).
    eauto.
  Qed.

End Closed.