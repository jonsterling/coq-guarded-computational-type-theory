Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.
From gctt Require Import Closure.

From gctt Require Tactic.

Module M := Matrix.
Module T := Tactic.


Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


Set Implicit Arguments.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Module Univ.
  Local Obligation Tactic := firstorder.
  Program Fixpoint Spine (n : nat) {measure n (lt)} : M.matrix :=
    match n with
    | 0 => Clo.t M.empty
    | S n =>
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Tm.univ j
          ∧ snd X = fun es =>
                      ∃ S, Clo.t (@Spine j _) (fst es, S) ∧ Clo.t (@Spine j _) (snd es, S)
    end.

  Theorem Unfold_Spine_S :
    ∀ X n,
      Spine (S n) X =
      ∃ (j : nat) (p : j ≤ n),
        fst X ⇓ Tm.univ j
        ∧ snd X =
          fun es =>
            ∃ S, Clo.t (Spine j) (fst es, S) ∧ Clo.t (Spine j) (snd es, S).
  Proof.
    move=> X n.
    by [Wf.WfExtensionality.unfold_sub Spine (Spine (S n) X)].
  Qed.

  Theorem Unfold_Spine_0 :
    ∀ X, Spine 0 X = Clo.t M.empty X.
  Proof.
    move=> X.
      by [Wf.WfExtensionality.unfold_sub Spine (Spine 0 X)].
  Qed.

  Definition Nuprl (i : nat) : M.matrix :=
    Clo.t (Spine i).

  Ltac simpl_Spine :=
    repeat match goal with
    | X : Spine 0 _ |- _ => rewrite Unfold_Spine_0 in X
    | X : Spine (S _) _ |- _ => rewrite Unfold_Spine_S in X
    | _ => rewrite Unfold_Spine_S || rewrite Unfold_Spine_0
    end.


  Theorem Nuprl_functional : ∀ i, M.functional (Nuprl i).
  Proof.
    case => *.
    + rewrite /Nuprl //= Clo.idempotence.
      apply: Clo.functionality; eauto.
    + elim; rewrite /M.based_functional /Nuprl;
      move=> *; Clo.destruct_clos;
      simpl_Spine; Clo.noconfusion.
      ++ congruence.
      ++ congruence.
      ++ T.reorient.
         Clo.specialize_functionality_ih => p q.
         rewrite p q.
         congruence.
      ++ T.reorient.
         repeat T.eqcd => *.
         Later.gather => *; destruct_conjs.
         Clo.specialize_functionality_ih.
         congruence.
      ++ T.reorient.
         repeat T.eqcd => *.
         T.specialize_hyps; Clo.specialize_functionality_ih.
         congruence.

      ++ congruence.
  Qed.


  Definition Nuprlω : M.matrix :=
    fun X => ∃ n, Nuprl n X.


  Theorem Roll {i : nat} : Sig.t (Spine i) (Nuprl i) = Nuprl i.
  Proof.
    apply: binrel_extensionality => A R.
    split => H.
    + rewrite /Nuprl /Clo.t.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x)
      end.
      auto.
    + rewrite /Nuprl /Clo.t in H.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point M.matrix (PowerSetCompleteLattice (Tm.t 0 * M.behavior)) m x) => _
      end.
      apply.
      auto.
  Qed.

  Definition Nuprl_monotone_case (i j : nat) (A : Tm.t 0) : Prop :=
    ∀ R,
      i ≤ j
      → Nuprl i (A, R)
      → Nuprl j (A, R).

  Theorem Nuprl_unit_monotone : ∀ i j, Nuprl_monotone_case i j Tm.unit.
  Proof.
    move=> i j R p; rewrite /Nuprl; Clo.destruct_clo; Clo.noconfusion; rewrite -Clo.roll.
    + induction i as [|i' ih].
      ++ apply: Sig.unit.
         simpl_Spine.
         Clo.destruct_clos; Clo.noconfusion.
      ++ apply: ih; first omega.
         simpl_Spine.
         Clo.noconfusion.
    + by [apply: Sig.unit].
  Qed.

  Theorem Nuprl_bool_monotone : ∀ i j, Nuprl_monotone_case i j Tm.bool.
  Proof.
    move=> i j R p; rewrite /Nuprl;
    Clo.destruct_clo => //= *.
    + induction i as [| i' ih].
      ++ rewrite -Clo.roll; apply: Sig.bool.
         simpl_Spine.
         Clo.destruct_clos.
      ++ apply: ih; first omega.
         simpl_Spine.
         Clo.noconfusion.

    + rewrite -Clo.roll.
      induction i as [| i' ih ].
      ++ by [apply: Sig.bool].
      ++ apply: ih.
         omega.
  Qed.

  Theorem Nuprl_prod_monotone :
    ∀ i j A B,
      Nuprl_monotone_case i j A
      → Nuprl_monotone_case i j B
      → Nuprl_monotone_case i j (Tm.prod A B).
  Proof.
    move=> i j A B ihA ihB R p; rewrite /Nuprl => Nprod.
    rewrite -Clo.roll.
    apply: Sig.prod.
    Clo.destruct_clos; Clo.noconfusion.
    + induction i; Clo.noconfusion; simpl_Spine.
      Clo.destruct_clos; Clo.noconfusion; simpl_Spine;
      repeat T.split; eauto.
      ++ apply: ihA; auto.
         rewrite /Nuprl Clo.idempotence; eauto.
      ++ apply: ihB; auto.
         rewrite /Nuprl Clo.idempotence; eauto.
      ++ Clo.noconfusion.
    + repeat T.split; eauto.
      ++ by [apply: ihA].
      ++ by [apply: ihB].
  Qed.


  Theorem Nuprl_ltr_monotone :
    ∀ i j κ A,
      Nuprl_monotone_case i j A
      → Nuprl_monotone_case i j (Tm.ltr κ A).
  Proof.
    move=> i ? ? ? ihA ? ?; rewrite /Nuprl => ?; rewrite -Clo.roll.
    apply: Sig.later.
    Clo.destruct_clos; Clo.noconfusion; simpl_Spine.
    + induction i; Clo.noconfusion; simpl_Spine.
      Clo.destruct_clos; Clo.noconfusion; simpl_Spine.
      repeat T.split; eauto.
      apply: Later.map => [X|]; last eauto.
      apply: ihA; eauto.
      rewrite /Nuprl Clo.idempotence.
      eauto.
      Clo.noconfusion.
    + repeat T.split; eauto.
      apply: Later.map => *; last eauto.
      by [apply: ihA].
  Qed.


  Theorem Nuprl_isect_monotone :
    ∀ i j A,
      (∀ κ, Nuprl_monotone_case i j (A κ))
      → Nuprl_monotone_case i j (Tm.isect A).
  Proof.
    move=> i ? ? ihA ? ?; rewrite /Nuprl => Nisect.
    rewrite -Clo.roll.
    apply: Sig.isect.
    Clo.destruct_clos; Clo.noconfusion; simpl_Spine.
    + induction i; Clo.noconfusion; simpl_Spine;
      Clo.destruct_clos; Clo.noconfusion.
      repeat T.split; eauto => *.
      T.specialize_hyps.
      apply: ihA; auto.
      rewrite /Nuprl Clo.idempotence.
      eauto.

    + repeat T.split; eauto => *.
      T.specialize_hyps.
      by [apply: ihA].
  Qed.

  Theorem Nuprl_monotone :
    ∀ A i j, Nuprl_monotone_case i j A.
  Proof.
    elim.
    + intros.
      omega.
    + apply: Nuprl_unit_monotone.
    + apply: Nuprl_bool_monotone.

    + move=> i j R; rewrite /Nuprl_monotone_case /Nuprl => *.
      Clo.destruct_clos; induction i; simpl_Spine => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + move=> i j R; rewrite /Nuprl_monotone_case /Nuprl => *.
      Clo.destruct_clos; induction i; simpl_Spine => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + move=> i j R; rewrite /Nuprl_monotone_case /Nuprl => *.
      Clo.destruct_clos; induction i; simpl_Spine => *;
      Clo.destruct_clos;
      Clo.noconfusion.

    + intros; apply: Nuprl_prod_monotone; eauto.

    + rewrite /Nuprl_monotone_case /Nuprl => ? ? ? ? i *.
      Clo.destruct_clos; Clo.noconfusion.
      induction i; simpl_Spine; Clo.destruct_clos; Clo.noconfusion.

    + rewrite /Nuprl_monotone_case /Nuprl => ? ? ? ? i *.
      Clo.destruct_clos; Clo.noconfusion.
      induction i; simpl_Spine; Clo.destruct_clos; Clo.noconfusion.

    + intros; apply: Nuprl_ltr_monotone; eauto.
    + intros; apply: Nuprl_isect_monotone; eauto.
    + induction n as [|n' ihn].
      ++ move=> i j; rewrite /Nuprl_monotone_case /Nuprl => R p.
         Clo.destruct_clo => *.
         induction i.
         +++ simpl_Spine.
             Clo.destruct_clos.
         +++ simpl_Spine.
             T.destruct_conjs.
             T.destruct_evals.

             have: ∃ j', j = S j'.
             induction j; omega || eauto.
             move=> [j' q].
             rewrite q.
             rewrite -Clo.roll.
             apply: Sig.init.
             simpl_Spine.
             exists 0; repeat T.split; eauto.
             ++++ omega.

      ++ move=> i j; rewrite /Nuprl_monotone_case /Nuprl => R p.
         Clo.destruct_clo => *.
         induction i.
         +++ simpl_Spine.
             Clo.destruct_clos.
         +++ simpl_Spine.
             T.destruct_conjs.
             T.destruct_evals.
             simpl in *.
             have: ∃ j', j = S j'.
             induction j; omega || eauto.
             move=> [j' q].
             rewrite q.
             rewrite -Clo.roll.
             apply: Sig.init.
             simpl_Spine.
             exists (S n'); repeat T.split; eauto.
             ++++ omega.
  Qed.

  (* TODO: move to a general location *)
  Theorem nat_max_leq :
    ∀ i j,
      i ≤ max i j.
  Proof.
    case => j.
    + omega.
    + case; firstorder.
  Qed.

  Theorem nat_max_commutative :
    ∀ i j,
      max i j = max j i.
  Proof.
    elim.
    + case; auto.
    + move=> n IH; elim.
      ++ auto.
      ++ move=> n' p.
         simpl.
         rewrite IH.
         auto.
  Qed.

  (* To show that the maximal refinement matrix is functional, we need
      to deal with type-behavior assignments at different levels.
      However, we can take the maximum of these levels, by
      monotonicity bring the assignments up to a common level. *)
  Theorem Nuprlω_functional : M.functional Nuprlω.
  Proof.
    move=> A R1 R2 [n1 AR1] [n2 AR2].
    apply: Nuprl_functional.
    + apply: Nuprl_monotone;
      first (apply: nat_max_leq; shelve);
      eauto.
    + apply: Nuprl_monotone;
      first (rewrite nat_max_commutative; apply: nat_max_leq);
      eauto.
  Qed.


  Notation "n ⊩ A type" := (∃ R, Nuprl n (A, R)) (at level 0, A at level 0, only parsing).
  Notation "n ⊩ A ∼ B type" := (∃ R, Nuprl n (A, R) ∧ Nuprl n (B, R)) (at level 0, A at level 0, B at level 0, only parsing).
  Notation "ω⊩ A type" := (∃ R, Nuprlω (A, R)) (at level 0, A at level 0, only parsing).

  Module ClosedRules.

    (* A nice hack from Adam Chlipala Theory, to force the resolution of *)
(*        some existential variables. *)
    Ltac equate M N :=
      let r := constr:(eq_refl M : M = N)
      in idtac.

    Ltac simplify :=
      simpl; simpl_Spine; simpl;
      repeat
        (match goal with
         | |- ∃ (R : M.behavior), Nuprl ?n ?X => eexists; rewrite -Roll
         | |- ?i ≤ ?j => omega
         | |- ∃ (x : ?A), ?P => eexists
         | |- ?P ∧ ?Q => split
         | |- ?P ↔ ?Q => split
         end); eauto.

    (* A tactic to prove a rule by appealing to one of the *)
(*        constructors of the refinement matrix closure operator. *)
    Ltac prove_rule con :=
      match goal with
      | |- ?n ⊩ ?A type => eexists; rewrite -Roll; apply: con; simplify; try reflexivity
      end.

    Theorem unit_formation {n : nat} : n ⊩ Tm.unit type.
    Proof.
      prove_rule Sig.unit.
    Qed.

    Lemma univ_formation_S {n : nat}
      : (S n) ⊩ (Tm.univ n) type.
    Proof.
      prove_rule Sig.init.
    Qed.

    Theorem univ_formation {n i : nat} :
      i < n
      → n ⊩ (Tm.univ i) type.
    Proof.
      case => [| j q ].
      + apply: univ_formation_S.
      + eexists.
        rewrite -Roll.
        apply: Sig.init.
        simpl_Spine.
        exists i. repeat split.
        ++ omega.
        ++ constructor.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      move=> A B [R1 D] [R2 E].
      prove_rule Sig.prod.
    Qed.

    Lemma NuprlChoice {n : nat} {A : CLK → Tm.t 0} :
      (∀ κ, ∃ Rκ, Nuprl n (A κ, Rκ))
      → ∃ S, ∀ κ, Nuprl n (A κ, S κ).
    Proof.
      move=> X.
      apply: (unique_choice (fun κ R => Nuprl n (A κ, R))) => κ.
      case: (X κ) => S T.
      eexists; split; eauto => S' T'.
      apply: Nuprl_functional; eauto.
    Qed.

    Theorem isect_formation {n : nat} :
      forall B,
        (∀ κ, n ⊩ (B κ) type)
        → n ⊩ (Tm.isect B) type.
    Proof.
      move=> B Q.
      case: (NuprlChoice Q) => S Q'.
      prove_rule Sig.isect.
    Qed.

    Theorem isect_irrelevance :
      forall n A,
        n ⊩ A type
        → n ⊩ A ∼ (Tm.isect (fun _ => A)) type.
    Proof.
      move=> n A [R AR].
      eexists; split; eauto.
      rewrite -Roll; apply: Sig.isect.
      exists (fun _ => A), (fun _ => R).
      repeat T.split; eauto.
      T.eqcd => *.
      case: LocalClock => ? _.
      apply: propositional_extensionality.
      split; auto.
    Qed.

    Hint Resolve unit_formation univ_formation prod_formation isect_formation isect_irrelevance.
  End ClosedRules.

  Theorem test : ∃ n, n ⊩ (Tm.prod Tm.unit (Tm.univ 0)) type.
  Proof.
    eauto.
  Qed.

  Theorem test2 : ∃ n, n ⊩ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)) type.
    eauto.
  Qed.

End Univ.
