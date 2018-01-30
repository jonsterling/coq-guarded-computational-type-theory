From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8 Program.Equality Logic.FunctionalExtensionality.
From gctt Require Import Var Program Expression Elaborate Sequent Tower.
From gctt Require Theorems.
Module Th := Theorems.

Definition quote_bool (b : bool) {Λ} : Expr.t Λ 0 :=
  match b with
  | true => Expr.tt
  | false => Expr.ff
  end.

Notation "⌊ b ⌋𝔹" := (quote_bool b).

(* TODO: improve this proof. *)
Theorem canonicity {M} :
  ⟦ 0 ∣ ⋄ ≫ 𝟚 ∋ M ≐ M ⟧
  → ∃ b : bool, ⟦ 0 ∣ 0 ⊢ M ≃ ⌊ b ⌋𝔹 ⟧.
Proof.
  move=> 𝒟.
  suff κs: Env.t 0; last by [move=> x; dependent destruction x].
  suff: τω ⊧ 𝟚 ∋ ⟦ M ⟧ κs ∼ ⟦ M ⟧ κs.
  - case=> R [[n ℰ0] ℰ1].
    Tower.destruct_tower.
    dependent destruction ℰ1.
    dependent destruction H1.
    + exists true; simpl.
      move=> κs' //=.
      replace κs' with κs.
      * split.
        ** replace ((⟦ M ⟧ κs) ⫽ γ)%prog with (⟦ M ⟧ κs)%prog.
           *** move=> H1.
               replace V with (@Prog.tt 0); eauto.
                 by OpSem.evals_to_eq.
           *** simplify_subst.
        ** replace ((⟦ M ⟧ κs) ⫽ γ)%prog with (⟦ M ⟧ κs)%prog; eauto.
           move=> //= H1.
           replace V with (@Prog.tt 0); eauto.
           dependent destruction H1.
           dependent destruction eval_steps; eauto.
           dependent destruction H1.
           simplify_subst.
      * apply: functional_extensionality => x.
        dependent destruction x.
    + exists false.
      move=> κs' //=.
      replace κs' with κs.
      * split.
        ** replace ((⟦ M ⟧ κs) ⫽ γ)%prog with (⟦ M ⟧ κs)%prog.
           *** move=> H1.
               replace V with (@Prog.ff 0); eauto.
                 by OpSem.evals_to_eq.
           *** simplify_subst.
        ** replace ((⟦ M ⟧ κs) ⫽ γ)%prog with (⟦ M ⟧ κs)%prog; eauto.
           move=> //= H1.
           replace V with (@Prog.ff 0); eauto.
           dependent destruction H1.
           dependent destruction eval_steps; eauto.
           dependent destruction H1.
           simplify_subst.
      * apply: functional_extensionality => x.
        dependent destruction x.
  - specialize (𝒟 κs); simpl in 𝒟.
    suff: τω ⊧ ⋄ ≫ 𝟚 ∼ 𝟚 ∧ (∃ γ0 : @Sub.t Prog.t 0 0, atomic_eq_env τω ⋄%ictx γ0 γ0).
    + case=> ℰ [γ0 γ00].
      specialize (𝒟 I ℰ γ0 γ0 γ00).
      T.use 𝒟.
      simplify_subst.
    + split.
      * move=> ? ? ? //=.
        apply: (Th.Level.eq_ty_from_level 0).
        apply: Th.Bool.formation.
      * unshelve esplit.
        ** move=> x.
           dependent destruction x.
        ** by simplify_subst.
Qed.
