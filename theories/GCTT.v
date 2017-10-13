Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Import Axioms.
From gctt Require Import Terms.

Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


Set Implicit Arguments.



Hint Resolve Later.map.


Ltac mysplit :=
  simpl;
  match goal with
  | |- _ ∧ _ => split
  | |- ∃ _: _, _ => esplit
  | |- _ ↔ _ => split
  end.


(* A behavior is a binary relations on terms; later we will show this to be symmetric
     and transitive. *)
Definition behavior := ℘ (Tm.t 0 * Tm.t 0).

(* A 'refinement matrix' (called 'type system' by Allen) is a relation between terms and behaviors. *)
Definition matrix := ℘ (Tm.t 0 * behavior).


Ltac make_morphism :=
  unshelve refine {| mon_func := _ |}.

Ltac morphism_monotone :=
  match goal with
  | |- @mon_func _ _ _ _ ?m _ _ =>
    apply: (@mon_prop _ _ _ _ m);
    eauto
  end.

Module Close.
  Notation "[ e1 , e2 ] ⇓ e3" := (e1 ⇓ e3 ∧ e2 ⇓ e3) (at level 0).

  Ltac prove_monotone :=
    simpl; move=> *; destruct_conjs;
    repeat mysplit; eauto.

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ R = fun e12 => [fst e12, snd e12] ⇓ Tm.ax).
    + prove_monotone.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ R = fun e12 => ([fst e12, snd e12] ⇓ Tm.tt ∨ [fst e12, snd e12] ⇓ Tm.ff)).
    + prove_monotone.
  Defined.

  Definition later : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ κ B R',
            A ⇓ Tm.ltr κ B
            ∧ ▷[ κ ] (τ (B, R'))
            /\ R = fun e12 => ▷[ κ ] (R' e12)).
    + prove_monotone.
  Defined.

  Definition prod : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B C R1 R2,
            A ⇓ Tm.prod B C
            ∧ τ (B, R1)
            ∧ τ (C, R2)
            ∧ R = fun es =>
                    ∃ e11 e12 e21 e22,
                      (fst es ⇓ Tm.pair e11 e12)
                      ∧ (snd es ⇓ Tm.pair e21 e22)
                      ∧ R1 (e11, e21)
                      ∧ R2 (e12, e22)).
    + prove_monotone.
  Defined.

  Definition isect : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (∃ B S,
            A ⇓ Tm.isect B
            ∧ (∀ κ, τ (B κ, S κ))
            ∧ R = fun es => ∀ κ, S κ es).
    + prove_monotone.
  Defined.
End Close.

Module TyF.
  (* For each refinement matrix σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/behaviors. *)
  Inductive t (σ τ : matrix) (X : Tm.t 0 * behavior) : Prop :=
  | init of σ X
  | unit of Close.unit τ X
  | bool of Close.bool τ X
  | prod of Close.prod τ X
  | isect of Close.isect τ X
  | later of Close.later τ X.

  (* The map defined above really is monotone. *)
  Definition mono (σ : matrix) : monotone matrix matrix.
  Proof.
    make_morphism.
    + exact (t σ).
    + move=> τ1 τ2 P X tQ; case tQ => Q;
      [ apply: init; eauto
      | apply: unit
      | apply: bool
      | apply: prod
      | apply: isect
      | apply: later
      ]; morphism_monotone.
  Defined.
End TyF.


(* Because the map is monotone, we can take its least fixed point to
   get a closure operator on refinement matrices.*)
Definition CTyF (σ : matrix) := lfp (TyF.mono σ).

Definition based_matrix_functional (σ : matrix) (A : Tm.t 0) : Prop :=
  ∀ R1 R2,
    σ (A, R1)
    → σ (A, R2)
    → R1 = R2.

Definition matrix_functional (σ : matrix) : Prop :=
  ∀ A, based_matrix_functional σ A.


Theorem CTyF_Roll:
  ∀ σ,
    TyF.t σ (CTyF σ)
    = CTyF σ.
Proof.
  move=> σ.
  apply: binrel_extensionality => [A R].
  mysplit => [X | X].
  + rewrite /CTyF.
    match goal with
    | |- lfp ?m ?x =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
    end.
    auto.
  + rewrite /CTyF in X.
    match goal with
    | H : lfp ?m ?x |- _ =>
      case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ Q'
    end.
    apply: Q'.
    auto.
Qed.


Theorem CTyF_ind :
  ∀ (σ : matrix) (X : Tm.t 0 * behavior) (P : Prop),
    CTyF σ X
    → (σ X → P)
    → (Close.unit (CTyF σ) X → P)
    → (Close.bool (CTyF σ) X → P)
    → (Close.prod (CTyF σ) X → P)
    → (Close.isect (CTyF σ) X → P)
    → (Close.later (CTyF σ) X → P)
    → P.
Proof.
  move=> σ [A R] P C init unit bool prod isect later.
  rewrite -CTyF_Roll in C.
  case: C; auto.
Qed.


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


Ltac destruct_conjs :=
  repeat match goal with
  | H : ∃ _:_,_ |- _ => case: H => *
  | H : _ ∧ _ |- _ => case: H => *
  end.

Ltac noconfusion :=
  try by [contradiction];
  rewrite /Empty;
  move=> *; simpl in *;
  destruct_conjs;
  destruct_evals.


Ltac destruct_CTyF :=
  let x := fresh in move=> x; apply: (CTyF_ind x); clear x;
  try by [noconfusion].

Ltac destruct_CTyFs :=
  repeat
    match goal with
    | T : CTyF _ _ |- _ =>
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

Ltac use_matrix_functionality_ih :=
  match goal with
  | IH : ∀ R1 R2 : behavior, CTyF _ (?A, R1) → CTyF _ (?A, R2) → R1 = R2, U : ?R' (?e1, ?e2) |- ?R (?e1, ?e2) =>
      by rewrite (IH R R'); auto
  end.

Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.

Ltac specialize_functionality_ih :=
  repeat
    match goal with
    | H : ∀ R1 R2 : behavior, CTyF _ (?X, _) → CTyF _ (?X, _) → _ = _, H' : CTyF _ (?X, ?R1), H'' : CTyF _ (?X, ?R2) |- _ => specialize (H _ _ H' H''); move: H
    end.


Theorem universal_extensionality :
  ∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x = Q x)
    → (∀ x, P x) = (∀ x, Q x).
Proof.
  move=> A P Q E.
  apply: propositional_extensionality; mysplit => *.
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
  mysplit => *; Later.gather; move=> [X Y].
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

Theorem CTyF_Empty_functional : matrix_functional (CTyF Empty).
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

Theorem CTyF_idempotent : CTyF (CTyF Empty) = CTyF Empty.
Proof.
  apply: functional_extensionality.
  case; elim; try by [move=> *; apply: propositional_extensionality; mysplit; destruct_CTyF];

  move=> *; apply: propositional_extensionality.

  + mysplit; destruct_CTyF => *; rewrite -CTyF_Roll;
    apply: TyF.unit; by [noconfusion].

  + mysplit; destruct_CTyF => *; rewrite -CTyF_Roll;
    apply: TyF.bool; by [noconfusion].


  + mysplit; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll; apply: TyF.prod;
    repeat mysplit; eauto; destruct_evals;
    by [congruence].

  + mysplit; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll;
    apply: TyF.later;
    repeat mysplit; destruct_evals; eauto.
    ++ by [congruence].
    ++ by [congruence].

  + mysplit; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll;
    apply: TyF.isect;
    repeat mysplit; auto; destruct_evals; eauto => *;
    specialize_hyps; by [congruence].
Qed.


Module Univ.

  Lemma lt_wf_tp: well_founded lt.
  Proof.
    intro n; induction n; constructor; intros; inversion H; eauto;
      destruct IHn; eauto.
  Defined.
  Hint Resolve lt_wf_tp : arith.

  Obligation Tactic := idtac.
  Program Fixpoint Spine (n : nat) {measure n (lt)} : matrix :=
    match n with
    | 0 => CTyF Empty
    | S n =>
      fun X =>
        ∃ (j : nat) (p : j ≤ n),
          fst X ⇓ Tm.univ j
          ∧ snd X = fun es =>
                      ∃ S, CTyF (@Spine j _) (fst es, S) ∧ CTyF (@Spine j _) (snd es, S)
    end.

  Next Obligation.
  Proof.
    firstorder.
  Defined.
  Next Obligation.
  Proof.
    firstorder.
  Defined.
  Next Obligation.
    apply: lt_wf_tp.
  Defined.


  Theorem Unfold_Spine_S :
    ∀ X n,
      Spine (S n) X =
      ∃ (j : nat) (p : j ≤ n),
        fst X ⇓ Tm.univ j
        ∧ snd X =
          fun es =>
            ∃ S, CTyF (Spine j) (fst es, S) ∧ CTyF (Spine j) (snd es, S).
  Proof.
    move=> X n.
    by [Wf.WfExtensionality.unfold_sub Spine (Spine (S n) X)].
  Qed.

  Theorem Unfold_Spine_0 :
    ∀ X, Spine 0 X = CTyF Empty X.
  Proof.
    move=> X.
      by [Wf.WfExtensionality.unfold_sub Spine (Spine 0 X)].
  Qed.

  Definition Nuprl (i : nat) : matrix :=
    CTyF (Spine i).

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


  Theorem Roll {i : nat} : TyF.t (Spine i) (Nuprl i) = Nuprl i.
  Proof.
    apply: binrel_extensionality => A R.
    split => H.
    + rewrite /Nuprl /CTyF.
      match goal with
      | |- lfp ?m ?x =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x)
      end.
      auto.
    + rewrite /Nuprl /CTyF in H.
      match goal with
      | H : lfp ?m ?x |- _ =>
        case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _
      end.
      apply.
      auto.
  Qed.

  Ltac obvious := admit.



  Definition Nuprl_monotone_case (i j : nat) (A : Tm.t 0) : Prop :=
    ∀ R,
      i ≤ j
      → Nuprl i (A, R)
      → Nuprl j (A, R).

  Theorem Nuprl_unit_monotone : ∀ i j, Nuprl_monotone_case i j Tm.unit.
  Proof.
    move=> i j R p; rewrite /Nuprl; destruct_CTyF; noconfusion; rewrite -CTyF_Roll.
    + induction i as [|i' ih].
      ++ apply: TyF.unit.
         simpl_Spine.
         destruct_CTyFs; noconfusion.
      ++ apply: ih; first omega.
         simpl_Spine.
         noconfusion.
    + by [apply: TyF.unit].
  Qed.

  Theorem Nuprl_bool_monotone : ∀ i j, Nuprl_monotone_case i j Tm.bool.
  Proof.
    move=> i j R p; rewrite /Nuprl;
    destruct_CTyF => //= *.
    + induction i as [| i' ih].
      ++ rewrite -CTyF_Roll; apply: TyF.bool.
         simpl_Spine.
         destruct_CTyFs.
      ++ apply: ih; first omega.
         simpl_Spine.
         noconfusion.

    + rewrite -CTyF_Roll.
      induction i as [| i' ih ].
      ++ by [apply: TyF.bool].
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
    rewrite -CTyF_Roll.
    apply: TyF.prod.
    destruct_CTyFs; noconfusion.
    + induction i; noconfusion; simpl_Spine.
      destruct_CTyFs; noconfusion; simpl_Spine;
      repeat mysplit; eauto.
      ++ apply: ihA; auto.
         rewrite /Nuprl CTyF_idempotent; eauto.
      ++ apply: ihB; auto.
         rewrite /Nuprl CTyF_idempotent; eauto.
      ++ noconfusion.
    + repeat mysplit; eauto.
      ++ by [apply: ihA].
      ++ by [apply: ihB].
  Qed.


  Theorem Nuprl_ltr_monotone :
    ∀ i j κ A,
      Nuprl_monotone_case i j A
      → Nuprl_monotone_case i j (Tm.ltr κ A).
  Proof.
    move=> i ? ? ? ihA ? ?; rewrite /Nuprl => ?; rewrite -CTyF_Roll.
    apply: TyF.later.
    destruct_CTyFs; noconfusion; simpl_Spine.
    + induction i; noconfusion; simpl_Spine.
      destruct_CTyFs; noconfusion; simpl_Spine.
      repeat mysplit; eauto.
      apply: Later.map => [X|]; last eauto.
      apply: ihA; eauto.
      rewrite /Nuprl CTyF_idempotent.
      eauto.
      noconfusion.
    + repeat mysplit; eauto.
      apply: Later.map => *; last eauto.
      by [apply: ihA].
  Qed.


  Theorem Nuprl_isect_monotone :
    ∀ i j A,
      (∀ κ, Nuprl_monotone_case i j (A κ))
      → Nuprl_monotone_case i j (Tm.isect A).
  Proof.
    move=> i ? ? ihA ? ?; rewrite /Nuprl => Nisect.
    rewrite -CTyF_Roll.
    apply: TyF.isect.
    destruct_CTyFs; noconfusion; simpl_Spine.
    + induction i; noconfusion; simpl_Spine;
      destruct_CTyFs; noconfusion.
      repeat mysplit; eauto => *.
      specialize_hyps.
      apply: ihA; auto.
      rewrite /Nuprl CTyF_idempotent.
      eauto.

    + repeat mysplit; eauto => *.
      specialize_hyps.
      by [apply: ihA].
  Qed.

  (* TODO: fill in the obvious goals *)
  Theorem Nuprl_monotone :
    ∀ A i j, Nuprl_monotone_case i j A.
  Proof.
    elim.
    + intros.
      omega.
    + apply: Nuprl_unit_monotone.
    + apply: Nuprl_bool_monotone.
    + obvious.
    + obvious.
    + obvious.
    + intros; apply: Nuprl_prod_monotone; eauto.
    + obvious.
    + obvious.
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
             rewrite -CTyF_Roll.
             apply: TyF.init.
             simpl_Spine.
             exists 0; repeat mysplit; eauto.
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
             rewrite -CTyF_Roll.
             apply: TyF.init.
             simpl_Spine.
             exists (S n'); repeat mysplit; eauto.
             ++++ omega.
  Admitted.


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

  (* To show that the maximal refinement matrix is functional, *)
(*      we need to deal with type-behavior assignments at different levels. *)
(*      However, we can take the maximum of these levels, by monotonicity, *)
(*      bring the assignments up to a common level. *)
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
      simpl;
      repeat
        (match goal with
         | |- ∃ (R : behavior), Nuprl ?n ?X => eexists; rewrite -Roll
         | |- ?i ≤ ?j => omega
         | |- ∃ (x : ?A), ?P => eexists
         | |- ?P ∧ ?Q => split

         (* We will often encounter a semantic specification for a relation *)
(*             before we have even filled it in (i.e. it is an existential variable). *)
(*             So, we can force it to be instantiated to exactly the right thing. *)
         | |- ∀ e1 e2, ?R (e1, e2) ↔ @?S e1 e2 =>
           equate R (fun e12 => S (fst e12) (snd e12));
           intros

         | |- ?P ↔ ?Q => split
         end); eauto.

    (* A tactic to prove a rule by appealing to one of the *)
(*        constructors of the refinement matrix closure operator. *)
    Ltac prove_rule con :=
      match goal with
      | |- ?n ⊩ ?A type => eexists; rewrite -Roll; apply: con; simplify
      end.

    Theorem unit_formation {n : nat} : n ⊩ Tm.unit type.
    Proof.
      prove_rule TyF.unit.
      reflexivity.
    Qed.

    Lemma univ_formation_S {n : nat}
      : (S n) ⊩ (Tm.univ n) type.
    Proof.
      prove_rule TyF.init.
      simpl_Spine.
      repeat mysplit; eauto.
      reflexivity.
    Qed.

    Theorem univ_formation {n i : nat} :
      i < n
      → n ⊩ (Tm.univ i) type.
    Proof.
      case => [| j q ].
      + apply: univ_formation_S.
      + eexists.
        rewrite -Roll.
        apply: TyF.init.
        simpl_Spine.
        exists i. repeat split.
        ++ omega.
        ++ auto.
           simpl.
           auto.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      move=> A B [R1 D] [R2 E].
      prove_rule TyF.prod.
      reflexivity.
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
      prove_rule TyF.isect.
      reflexivity.
    Qed.

    Theorem isect_irrelevance :
      forall n A,
        n ⊩ A type
        → n ⊩ A ∼ (Tm.isect (fun _ => A)) type.
    Proof.
      move=> n A [R AR].
      eexists; split; eauto.
      rewrite -Roll; apply: TyF.isect.
      exists (fun _ => A).
      exists (fun _ => R).
      repeat mysplit; eauto.
      eqcd => *.
      apply: propositional_extensionality.
      split.
      + auto.
      + case: LocalClock.
        auto.
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
