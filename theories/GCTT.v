Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Import Matrix.
From gctt Require Import Axioms.
From gctt Require Import Terms.
From gctt Require Import Closure.

Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

From gctt Require Tactic.
Module T := Tactic.

Set Implicit Arguments.

Hint Resolve Later.map.

Definition Empty : matrix :=
  fun _ => False.

Ltac specialize_clocks κ :=
  repeat match goal with
  | X : ∀ (κ : CLK), ?P |- _ => specialize (X κ)
  end.



Ltac destruct_evals :=
  repeat
    match goal with
      | H : ?A ⇓ ?B |- _ => dependent destruction H
    end.


Ltac destruct_eval :=
  match goal with
  | |- _ ⇓ _ → _ => let x := fresh in move=> x; dependent destruction x
  end.


Ltac noconfusion :=
  try by [contradiction];
  rewrite /Empty;
  move=> *; simpl in *;
  destruct_conjs;
  destruct_evals.


Ltac destruct_CTyF :=
  let x := fresh in move=> x; apply: (Clo.ind x); clear x;
  try by [noconfusion].

Ltac destruct_CTyFs :=
  repeat
    match goal with
    | T : Clo.t _ _ |- _ =>
      move: T;
      destruct_CTyF
    end.


Ltac backthruhyp :=
  let H := fresh in
  match goal with
  | H : _ → ?P |- ?P => apply H
  end.

Ltac specialize_hyps :=
  repeat
    match goal with
    | H : ∀ κ : CLK, ?P, κ : CLK |- _ => specialize (H κ)
    | H : ?R (?e1, ?e2) -> ?P, H' : ?R (?e1, ?e2) |- _ => specialize (H H')
    end.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Ltac specialize_functionality_ih :=
  repeat
    match goal with
    | H : ∀ R1 R2 : behavior, Clo.t _ (?X, _) → Clo.t _ (?X, _) → _ = _, H' : Clo.t _ (?X, ?R1), H'' : Clo.t _ (?X, ?R2) |- _ => specialize (H _ _ H' H''); move: H
    end.


Theorem universal_extensionality :
  ∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x = Q x)
    → (∀ x, P x) = (∀ x, Q x).
Proof.
  move=> A P Q E.
  apply: propositional_extensionality; T.split => *.
  ++ rewrite -E. auto.
  ++ rewrite E. auto.
Qed.

Theorem later_extensionality :
  ∀ κ (P Q : Prop),
    (▷[κ] (P = Q))
    → (▷[κ] P) = (▷[κ] Q).
Proof.
  move=> κ P Q E.
  apply: propositional_extensionality.
  T.split => *; Later.gather; move=> [X Y].
  ++ rewrite -X; auto.
  ++ rewrite X; auto.
Qed.


Ltac reorient :=
  match goal with
  | H : ?Y = _ |- ?X = ?Y => symmetry; etransitivity; first eassumption
  end.

Ltac eqcd :=
  apply: universal_extensionality
  || apply: later_extensionality
  || apply: functional_extensionality.

Theorem CTyF_Empty_functional : matrix_functional (Clo.t Empty).
Proof.
  elim; rewrite /based_matrix_functional;
  move=> *; try by [destruct_CTyFs => //= *; noconfusion];
  destruct_CTyFs => *; noconfusion.
  + congruence.
  + congruence.
  + specialize_functionality_ih => p1 p2.
    rewrite p1 p2.
    congruence.
  + reorient.
    repeat eqcd => *.
    Later.gather => *; destruct_conjs.
    specialize_functionality_ih => p;
    congruence.
  + reorient.
    repeat eqcd => *.
    specialize_hyps.
    specialize_functionality_ih => *.
    congruence.
Qed.

Theorem CTyF_idempotent : Clo.t (Clo.t Empty) = Clo.t Empty.
Proof.
  apply: functional_extensionality.
  case; elim; try by [move=> *; apply: propositional_extensionality; T.split; destruct_CTyF];

  move=> *; apply: propositional_extensionality.

  + T.split; destruct_CTyF => *; rewrite -Clo.roll;
    apply: Sig.unit; by [noconfusion].

  + T.split; destruct_CTyF => *; rewrite -Clo.roll;
    apply: Sig.bool; by [noconfusion].


  + T.split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -Clo.roll; apply: Sig.prod;
    repeat T.split; eauto; destruct_evals;
    by [congruence].

  + T.split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -Clo.roll;
    apply: Sig.later;
    repeat T.split; destruct_evals; eauto.
    ++ by [congruence].
    ++ by [congruence].

  + T.split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -Clo.roll;
    apply: Sig.isect;
    repeat T.split; auto; destruct_evals; eauto => *;
    specialize_hyps; by [congruence].
Qed.


Module Univ.

  Lemma lt_wf_tp: well_founded lt.
  Proof.
    intro n; induction n; constructor; intros; inversion H; eauto;
      destruct IHn; eauto.
  Defined.
  Hint Resolve lt_wf_tp : arith.

  Local Obligation Tactic := firstorder.
  Program Fixpoint Spine (n : nat) {measure n (lt)} : matrix :=
    match n with
    | 0 => Clo.t Empty
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
    ∀ X, Spine 0 X = Clo.t Empty X.
  Proof.
    move=> X.
      by [Wf.WfExtensionality.unfold_sub Spine (Spine 0 X)].
  Qed.

  Definition Nuprl (i : nat) : matrix :=
    Clo.t (Spine i).

  Ltac simpl_Spine :=
    repeat match goal with
    | X : Spine 0 _ |- _ => rewrite Unfold_Spine_0 in X
    | X : Spine (S _) _ |- _ => rewrite Unfold_Spine_S in X
    | _ => rewrite Unfold_Spine_S || rewrite Unfold_Spine_0
    end.


  Theorem Nuprl_functional : ∀ i, matrix_functional (Nuprl i).
  Proof.
    case => *.
    + rewrite /Nuprl //= CTyF_idempotent.
      apply: CTyF_Empty_functional; eauto.
    + elim; rewrite /based_matrix_functional /Nuprl;
      move=> *; destruct_CTyFs;
      simpl_Spine; noconfusion.
      ++ congruence.
      ++ congruence.
      ++ reorient.
         specialize_functionality_ih => p q.
         rewrite p q.
         congruence.
      ++ reorient.
         repeat eqcd => *.
         Later.gather => *; destruct_conjs.
         specialize_functionality_ih.
         congruence.
      ++ reorient.
         repeat eqcd => *.
         specialize_hyps; specialize_functionality_ih.
         congruence.

      ++ congruence.
  Qed.


  Definition Nuprlω : matrix :=
    fun X => ∃ n, Nuprl n X.


  Theorem Roll {i : nat} : Sig.t (Spine i) (Nuprl i) = Nuprl i.
  Proof.
    apply: binrel_extensionality => A R.
    split => H.
    + rewrite /Nuprl /Clo.t.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
      end.
      auto.
    + rewrite /Nuprl /Clo.t in H.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _
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
    move=> i j R p; rewrite /Nuprl; destruct_CTyF; noconfusion; rewrite -Clo.roll.
    + induction i as [|i' ih].
      ++ apply: Sig.unit.
         simpl_Spine.
         destruct_CTyFs; noconfusion.
      ++ apply: ih; first omega.
         simpl_Spine.
         noconfusion.
    + by [apply: Sig.unit].
  Qed.

  Theorem Nuprl_bool_monotone : ∀ i j, Nuprl_monotone_case i j Tm.bool.
  Proof.
    move=> i j R p; rewrite /Nuprl;
    destruct_CTyF => //= *.
    + induction i as [| i' ih].
      ++ rewrite -Clo.roll; apply: Sig.bool.
         simpl_Spine.
         destruct_CTyFs.
      ++ apply: ih; first omega.
         simpl_Spine.
         noconfusion.

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
    destruct_CTyFs; noconfusion.
    + induction i; noconfusion; simpl_Spine.
      destruct_CTyFs; noconfusion; simpl_Spine;
      repeat T.split; eauto.
      ++ apply: ihA; auto.
         rewrite /Nuprl CTyF_idempotent; eauto.
      ++ apply: ihB; auto.
         rewrite /Nuprl CTyF_idempotent; eauto.
      ++ noconfusion.
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
    destruct_CTyFs; noconfusion; simpl_Spine.
    + induction i; noconfusion; simpl_Spine.
      destruct_CTyFs; noconfusion; simpl_Spine.
      repeat T.split; eauto.
      apply: Later.map => [X|]; last eauto.
      apply: ihA; eauto.
      rewrite /Nuprl CTyF_idempotent.
      eauto.
      noconfusion.
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
    destruct_CTyFs; noconfusion; simpl_Spine.
    + induction i; noconfusion; simpl_Spine;
      destruct_CTyFs; noconfusion.
      repeat T.split; eauto => *.
      specialize_hyps.
      apply: ihA; auto.
      rewrite /Nuprl CTyF_idempotent.
      eauto.

    + repeat T.split; eauto => *.
      specialize_hyps.
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
      destruct_CTyFs; induction i; simpl_Spine => *;
      destruct_CTyFs;
      noconfusion.

    + move=> i j R; rewrite /Nuprl_monotone_case /Nuprl => *.
      destruct_CTyFs; induction i; simpl_Spine => *;
      destruct_CTyFs;
      noconfusion.

    + move=> i j R; rewrite /Nuprl_monotone_case /Nuprl => *.
      destruct_CTyFs; induction i; simpl_Spine => *;
      destruct_CTyFs;
      noconfusion.

    + intros; apply: Nuprl_prod_monotone; eauto.

    + rewrite /Nuprl_monotone_case /Nuprl => ? ? ? ? i *.
      destruct_CTyFs; noconfusion.
      induction i; simpl_Spine; destruct_CTyFs; noconfusion.

    + rewrite /Nuprl_monotone_case /Nuprl => ? ? ? ? i *.
      destruct_CTyFs; noconfusion.
      induction i; simpl_Spine; destruct_CTyFs; noconfusion.

    + intros; apply: Nuprl_ltr_monotone; eauto.
    + intros; apply: Nuprl_isect_monotone; eauto.
    + induction n as [|n' ihn].
      ++ move=> i j; rewrite /Nuprl_monotone_case /Nuprl => R p.
         destruct_CTyF => *.
         induction i.
         +++ simpl_Spine.
             destruct_CTyFs.
         +++ simpl_Spine.
             destruct_conjs.
             destruct_evals.

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
         destruct_CTyF => *.
         induction i.
         +++ simpl_Spine.
             destruct_CTyFs.
         +++ simpl_Spine.
             destruct_conjs.
             destruct_evals.
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
  Theorem Nuprlω_functional : matrix_functional Nuprlω.
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
         | |- ∃ (R : behavior), Nuprl ?n ?X => eexists; rewrite -Roll
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
      eqcd => *.
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
