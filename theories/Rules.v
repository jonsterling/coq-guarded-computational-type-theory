Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
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

  Theorem later_intro {κ n} {A e1 e2} :
    ▷[κ] (τ[n] ⊧ A ∋ e1 ∼ e2)
    → τ[n] ⊧ (Tm.ltr κ A) ∋ e1 ∼ e2.
  Proof.
    move=> /Later.yank_existential;
    case=> *; eauto.
    Tac.prove; simpl; Later.gather; Tac.prove.
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

  (* TODO !*)
  Theorem ty_eq_symm {A B} :
    τω ⊧ A ∼ B
    → τω ⊧ B ∼ A.
  Proof.
  Admitted.

  Theorem ty_eq_trans {A B C} :
    τω ⊧ B ∼ C
    → τω ⊧ A ∼ B
    → τω ⊧ A ∼ C.
  Proof.
  Admitted.



  Hint Resolve unit_formation univ_formation eq_ty_from_level eq_mem_from_level prod_formation isect_formation isect_irrelevance unit_ax_equality later_formation later_intro later_force ty_eq_refl_left ty_eq_trans ty_eq_symm.

  Theorem test : τω ⊧ (Tm.prod Tm.unit (Tm.univ 0)) ∼ (Tm.prod Tm.unit (Tm.univ 0)).
  Proof.
    eauto.
  Qed.

  Theorem test2 : τω ⊧ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)).
    eauto.
  Qed.

End Closed.