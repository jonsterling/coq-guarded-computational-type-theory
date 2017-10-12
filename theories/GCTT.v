Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect.

Set Bullet Behavior "Strict Subproofs".

From gctt Require Import OrderTheory.
From gctt Require Import Axioms.
From gctt Require Import Terms.

Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Axiom propositional_extensionality :
  ∀ (P Q : Prop),
    (P ↔ Q)
    -> P = Q.

Theorem binrel_extensionality :
  ∀ (T1 T2 : Type) (R1 R2 : T1 * T2 → Prop),
    (∀ x y, R1 (x, y) ↔ R2 (x, y))
    → R1 = R2.
Proof.
  move=> T1 T2 R1 R2 F.
  apply: functional_extensionality.
  move=> [x y].
  apply: propositional_extensionality.
  eauto.
Qed.




Hint Resolve Later.map.



Theorem later_join : ∀ κ P Q, ▷[κ] P → ▷[κ] Q → ▷[κ] (P ∧ Q).
Proof.
  move=> κ ? ? X Y.
  by [rewrite Later.cart].
Qed.


Ltac later_elim_aux y :=
  lazymatch goal with
  | H1 : ▷[?κ] _, H2 : ▷[?κ] _ |- _ =>
    let x := fresh in
    have := later_join H1 H2 => x;
    clear H1; clear H2;
    later_elim_aux x
  | |- ▷[?κ] _ => apply: Later.map y
  end.

Ltac later_elim :=
  let x := fresh in later_elim_aux x.

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
    repeat
      match goal with
      | |- ?P ∧ ?Q => split
      | |- ∃ (x : ?A), ?P => esplit
      end;
    eauto.

  Definition unit : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
        (A ⇓ Tm.unit
         ∧ ∀ e1 e2,
            R (e1, e2) ↔ [e1, e2] ⇓ Tm.ax).
    + prove_monotone.
  Defined.

  Definition bool : monotone matrix matrix.
  Proof.
    make_morphism.
    + move=> τ [A R].
      exact
       (A ⇓ Tm.bool
        ∧ ∀ e1 e2,
           R (e1, e2) ↔ ([e1, e2] ⇓ Tm.tt ∨ [e1, e2] ⇓ Tm.ff)).
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
            /\ ∀ e1 e2, R (e1, e2) ↔ ▷[ κ ] (R' (e1, e2))).
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
            ∧ ∀ e1 e2,
                R (e1, e2) ↔ ∃ e11 e12 e21 e22,
                  (e1 ⇓ Tm.pair e11 e12)
                  ∧ (e2 ⇓ Tm.pair e21 e22)
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
            ∧ ∀ e1 e2, R (e1, e2) ↔ ∀ κ, S κ (e1, e2)).
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
  split => [X | X].
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


(* Ltac destruct_CTyFs := *)
(*   repeat match goal with *)
(*   | T : CTyF _ _ |- _ => *)
(*     apply: (CTyF_ind T); clear T; try by [noconfusion] *)
(*   end. *)

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

Ltac mysplit :=
  match goal with
  | |- _ ∧ _ => split
  | |- ∃ _: _, _ => esplit
  | |- _ ↔ _ => split
  end.

Ltac mytac :=
  backthruhyp; move=> *;
  specialize_hyps;
  destruct_conjs;
  repeat esplit; eauto;
  use_matrix_functionality_ih.

Ltac destruct_rel_spec e1 e2:=
  let H := fresh in
  let F := fresh in
  let G := fresh in
  move=> H; destruct (H e1 e2) as [F G]; clear H; move: F G.

Ltac destruct_rel_specs e1 e2 :=
  repeat
    match goal with
    | H : ∀ (e1 e2 : Tm.t 0), ?R1 (e1, e2) ↔ @?Q e1 e2 |- _ =>
      move: H; destruct_rel_spec e1 e2
    end.


Ltac print_goal :=
  match goal with
  | |- ?G => idtac G; idtac "----------------------------------------------"
  end.


Theorem CTyF_Empty_functional : matrix_functional (CTyF Empty).
Proof.
  elim; rewrite /based_matrix_functional;
  try by [move=> *; destruct_CTyFs; simpl => *; noconfusion].
  + move=> R1 R2 ? ?.
    destruct_CTyFs => //= => *.
    destruct_conjs.
    apply: binrel_extensionality => e1 e2.
    destruct_rel_specs e1 e2 => *.
    split; eauto.
  + move=> R1 R2 ? ?.
    destruct_CTyFs => //= => *.
    destruct_conjs.
    apply: binrel_extensionality => e1 e2.
    destruct_rel_specs e1 e2 => *.
    split; eauto.
  + move=> A ihA B ihB R1 R2 *.
    destruct_CTyFs => //= [[? [? [R11 [R12 ?]]]] [? [? [R21 [R22 ?]]]]]; noconfusion.
    apply: binrel_extensionality => e1 e2.
    destruct_rel_specs e1 e2 => F1 G1 F2 G2.
    split => *.
    ++ apply: G1; case: F2; eauto => *; noconfusion.
       repeat mysplit; eauto.
       +++ rewrite (ihA R21 R11); auto.
       +++ rewrite (ihB R22 R12); auto.
    ++ apply: G2; case: F1; eauto => *; noconfusion.
       repeat mysplit; eauto.
       +++ rewrite (ihA R11 R21); auto.
       +++ rewrite (ihB R12 R22); auto.
  + move=> κ A ihA R1 R2 *.
    destruct_CTyFs => [[? [? [R1' [? [H1 ?]]]]] [? [? [R2' [? [H2 ?]]]]]]; noconfusion.
    apply: binrel_extensionality => e1 e2.
    destruct_rel_specs e1 e2 => F1 G1 F2 G2.
    split => e1e2.
    ++ specialize (F1 e1e2).
       apply: G2.
       later_elim => *; destruct_conjs.
       by [rewrite (ihA R2' R1')].
    ++ specialize (F2 e1e2).
       apply: G1.
       later_elim => *; destruct_conjs.
       by [rewrite (ihA R1' R2')].
  + move=> A ihA R1 R2 *.
    destruct_CTyFs => [[? [R1' ?]] [? [R2' ?]]]; noconfusion.
    apply: binrel_extensionality => e1 e2.
    destruct_rel_specs e1 e2 => F1 G1 F2 G2.
    split => *.
    ++ apply: G1 => κ.
       rewrite (ihA κ (R2' κ) (R1' κ)); auto.
    ++ apply: G2 => κ.
       rewrite (ihA κ (R1' κ) (R2' κ)); auto.
Qed.


Theorem CTyF_idempotent : CTyF (CTyF Empty) = CTyF Empty.
Proof.
  apply: functional_extensionality.
  case; elim; try by [move=> *; apply: propositional_extensionality; split; destruct_CTyF].
  + move=> *.
    apply: propositional_extensionality.
    split; destruct_CTyF => *; rewrite -CTyF_Roll;
    apply: TyF.unit; by [noconfusion].

  + move=> R.
    apply: propositional_extensionality;
    split; destruct_CTyF => *; rewrite -CTyF_Roll;
    apply: TyF.bool; by [noconfusion].


  + move=> A ihA B ihB R.
    apply: propositional_extensionality.
    split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll; apply: TyF.prod;
    simpl; repeat mysplit; eauto; destruct_evals.
    ++ by [rewrite -ihA].
    ++ by [rewrite -ihB].
    ++ by [rewrite ihA].
    ++ by [rewrite ihB].

  + move=> κ A ihA R.
    apply: propositional_extensionality.
    split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll;
    apply: TyF.later;
    simpl; repeat mysplit; destruct_evals; eauto.
    ++ by [rewrite -ihA].
    ++ by [rewrite ihA].

  + move=> A ihA R.
    apply: propositional_extensionality.
    split; destruct_CTyF => //= *;
    destruct_conjs; rewrite -CTyF_Roll;
    apply: TyF.isect;
    simpl; repeat mysplit; auto; destruct_evals; eauto => *.
    ++ by [rewrite -ihA].
    ++ by [rewrite ihA].
Qed.


Module Univ.

  Definition Spine: nat → matrix.
  Proof.
    elim => [|i'].
    + exact (CTyF Empty).
    + move=> τ [A R].
      exact
        (∃ j,
            j <= i'
            ∧ A ⇓ Tm.univ j
            ∧ ∀ e1 e2,
                R (e1, e2) ↔
                  ∃ S, CTyF τ (e1, S) ∧ CTyF τ (e2, S)).
  Defined.

  Definition Nuprl (i : nat) : matrix :=
    CTyF (Spine i).



  Ltac simpl_Spine :=
    match goal with
    | X : Spine 0 _ |- _ => simpl in X
    | X : Spine (S _) _ |- _ => simpl in X
    end.

  Theorem Nuprl_functional : ∀ i, matrix_functional (Nuprl i).
  Proof.
    case => [A | n].

    + rewrite /Nuprl /Spine //= /based_matrix_functional; move=> ? ? Y Z.
      rewrite CTyF_idempotent in Y, Z.
      apply: CTyF_Empty_functional; eauto.

    + elim; rewrite /based_matrix_functional /Nuprl;
      try by [move=> *; destruct_CTyFs].

      ++ move=> *; destruct_CTyFs => *; noconfusion.
         apply: binrel_extensionality => e1 e2.
         split => *; destruct_rel_specs e1 e2; eauto.

      ++ move=> *; destruct_CTyFs => *; noconfusion.
         apply: binrel_extensionality => e1 e2.
         split => *; destruct_rel_specs e1 e2; eauto.

      ++ move=> A ihA B ihB R1 R2 ? ?.
         destruct_CTyFs => //= [[? [? [R1' [R2' ?]]]] [? [? [R1'' [R2'' ?]]]]].
         apply: binrel_extensionality => e1 e2;
         split => e1e2; destruct_evals; destruct_conjs;
         destruct_rel_specs e1 e2 => F1 G1 F2 G2.
         +++ case: F2; eauto => *.
             apply: G1.
             destruct_conjs; destruct_evals.
             repeat mysplit; eauto.
             ++++ rewrite (ihA R1'' R1'); eauto.
             ++++ rewrite (ihB R2'' R2'); eauto.
         +++ case: F1; eauto => *.
             apply: G2.
             destruct_conjs; destruct_evals.
             repeat mysplit; eauto.
             ++++ rewrite (ihA R1' R1''); eauto.
             ++++ rewrite (ihB R2' R2''); eauto.

      ++ move=> κ A ihA R1 R2 *.
         destruct_CTyFs => [[? [? [R1' [? [H1 sp1]]]]] [? [? [R2' [? [H2 sp2]]]]]].
         destruct_conjs; destruct_evals.
         apply: binrel_extensionality => e1 e2.
         destruct_rel_specs e1 e2 => F1 G1 F2 G2.
         split => e1e2.
         +++ apply: G2.
             specialize (F1 e1e2).
             later_elim => *; destruct_conjs.
             by [rewrite (ihA R2' R1')].
         +++ apply: G1.
             specialize (F2 e1e2).
             later_elim => *; destruct_conjs.
             by [rewrite (ihA R1' R2')].

      ++ move=> A ihA R1 R2 *.
         destruct_CTyFs => [[? [R1' ?]] [? [R2' ?]]].
         destruct_conjs; destruct_evals.
         apply: binrel_extensionality => e1 e2.
         split => e1e2.
         +++ destruct_rel_specs e1 e2 => ? G1 *.
             apply: G1 => κ.
             rewrite (ihA κ (R2' κ) (R1' κ)); eauto.
         +++ destruct_rel_specs e1 e2 => ? ? ? G2.
             apply: G2 => κ.
             rewrite (ihA κ (R1' κ) (R2' κ)); eauto.

      ++ move=> i R1 R2 *.
         destruct_CTyFs => //= [[j1 [p1 [? sp1]]] [j2 [p2 [? sp2]]]].
         destruct_evals.
         apply: binrel_extensionality => e1 e2.
         destruct_rel_specs e1 e2 => *.
         split; eauto.
  Qed.

(*   Definition Nuprlω : matrix := *)
(*     fun X => ∃ n, Nuprl n X. *)


(*   Theorem Roll {i : nat} : TyF.t (Spine i) (Nuprl i) = Nuprl i. *)
(*   Proof. *)
(*     apply: binrel_extensionality => A R. *)
(*     split => H. *)
(*     + rewrite /Nuprl /CTyF. *)
(*       match goal with *)
(*       | |- lfp ?m ?x => *)
(*         case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) *)
(*       end. *)
(*       auto. *)
(*     + rewrite /Nuprl /CTyF in H. *)
(*       match goal with *)
(*       | H : lfp ?m ?x |- _ => *)
(*         case: (lfp_fixed_point matrix (PowerSetCompleteLattice (Tm.t 0 * behavior)) m x) => _ *)
(*       end. *)
(*       apply. *)
(*       auto. *)
(*   Qed. *)

(*   Ltac obvious := admit. *)

(*   (* Theorem Nuprl_monotone_S : *) *)
(*   (*   ∀ i A R, *) *)
(*   (*     Nuprl i (A, R) *) *)
(*   (*     → Nuprl (S i) (A, R). *) *)
(*   (* Proof. *) *)
(*   (*   move=> i. *) *)
(*   (*   rewrite /Nuprl. *) *)
(*   (*   elim; intros; rewrite -CTyF_Roll; destruct_CTyF; noconfusion. *) *)
(*   (*   + omega. *) *)
(*   (*   + apply: TyF.unit. *) *)
(*   (*     simpl. *) *)
(*   (*     destruct i; noconfusion. *) *)
(*   (*     destruct_CTyF; noconfusion. *) *)
(*   (*     constructor; eauto. *) *)
(*   (*   + apply: TyF.unit. *) *)
(*   (*     simpl. *) *)
(*   (*     constructor; eauto. *) *)
(*   (*   + apply: TyF.bool. *) *)
(*   (*     destruct i; noconfusion. *) *)
(*   (*     destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion. *) *)
(*   (*     destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*     apply: TyF.prod. *) *)
(*   (*     simpl in *. *) *)
(*   (*     exists H1, H2, H3, H4. *) *)
(*   (*     constructor; auto. *) *)
(*   (*     repeat constructor. *) *)
(*   (*     ++ apply: H. *) *)
(*   (*        rewrite CTyF_idempotent. *) *)
(*   (*        auto. *) *)
(*   (*     ++ apply: H0. *) *)
(*   (*        rewrite CTyF_idempotent. *) *)
(*   (*        auto. *) *)
(*   (*     ++ move=> e1e2. *) *)
(*   (*        specialize (H8 e1 e2). *) *)
(*   (*        destruct H8. *) *)
(*   (*        specialize_hyps. *) *)
(*   (*        auto. *) *)
(*   (*     ++ intro. *) *)
(*   (*        destruct (H8 e1 e2). *) *)
(*   (*        apply: H10. *) *)
(*   (*        auto. *) *)
(*   (*   + apply: TyF.prod. *) *)
(*   (*     simpl in *. *) *)
(*   (*     exists H1, H2, H3, H4. *) *)
(*   (*     constructor; auto. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*     (* This is only easy because I don't have a clause for function *) *)
(*   (*        types yet ;-) *) *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *) *)
(*   (*     apply: TyF.isect. *) *)
(*   (*     simpl in *. *) *)
(*   (*     exists H0, H1. *) *)
(*   (*     constructor; eauto. *) *)
(*   (*     constructor; eauto. *) *)
(*   (*     move=> κ. *) *)
(*   (*     specialize (H κ (H1 κ)). *) *)
(*   (*     apply: H. *) *)
(*   (*     rewrite CTyF_idempotent. *) *)
(*   (*     apply: H3. *) *)
(*   (*   + apply: TyF.isect. *) *)
(*   (*     exists H0, H1. *) *)
(*   (*     eauto. *) *)
(*   (*   + induction i; simpl in H. *) *)
(*   (*     ++ destruct_CTyF; noconfusion. *) *)
(*   (*     ++ apply: TyF.init. *) *)
(*   (*        destruct_conjs. *) *)
(*   (*        dependent induction H1. *) *)
(*   (*        exists H. *) *)
(*   (*        repeat split; eauto. *) *)
(*   (*        +++ move=> e1e2. *) *)
(*   (*            specialize (H2 e1 e2). *) *)
(*   (*            destruct H2. *) *)
(*   (*            specialize_hyps. *) *)
(*   (*            destruct H1. *) *)
(*   (*            exists x. *) *)
(*   (*            destruct H1. *) *)
(*   (*            clear H2. *) *)
(*   (*            split. *) *)
(*   (*            ++++ *) *)


(*   (* Abort. *) *)






(*   Definition Nuprl_monotone_case (i j : nat) (A : Tm.t 0) : Prop := *)
(*     ∀ R, *)
(*       i ≤ j *)
(*       → Nuprl i (A, R) *)
(*       → Nuprl j (A, R). *)

(*   Theorem Nuprl_unit_monotone : ∀ i j, Nuprl_monotone_case i j Tm.unit. *)
(*   Proof. *)
(*     move=> i j R p; rewrite /Nuprl => N. *)
(*     destruct_CTyF; noconfusion; rewrite -CTyF_Roll. *)
(*     + induction i as [|i' ih]. *)
(*       ++ apply: TyF.unit. *)
(*          simpl_Spine. *)
(*          destruct_CTyF; noconfusion. *)
(*          eauto. *)
(*       ++ apply: ih. *)
(*          +++ omega. *)
(*          +++ simpl_Spine. *)
(*              destruct_conjs. *)
(*              destruct_evals. *)
(*     + by [apply: TyF.unit]. *)
(*   Qed. *)

(*   Theorem Nuprl_bool_monotone : ∀ i j, Nuprl_monotone_case i j Tm.bool. *)
(*   Proof. *)
(*     move=> i j R p; rewrite /Nuprl => N. *)
(*     destruct_CTyF; noconfusion. *)
(*     + rewrite -CTyF_Roll. *)
(*       induction i as [| i' ih ]. *)
(*       ++ apply: TyF.bool. *)
(*          simpl_Spine. *)
(*          destruct_CTyF; noconfusion. *)
(*       ++ apply: ih. *)
(*          +++ omega. *)
(*          +++ simpl_Spine. *)
(*              destruct_conjs. *)
(*              destruct_evals. *)
(*   Qed. *)

(*   Theorem Nuprl_prod_monotone : *)
(*     ∀ i j A B, *)
(*       Nuprl_monotone_case i j A *)
(*       → Nuprl_monotone_case i j B *)
(*       → Nuprl_monotone_case i j (Tm.prod A B). *)
(*   Proof. *)
(*     move=> i j A B ihA ihB R p; rewrite /Nuprl => Nprod. *)
(*     rewrite -CTyF_Roll. *)
(*     apply: TyF.prod. *)
(*     destruct_CTyF; noconfusion. *)
(*     + induction i; noconfusion. *)
(*       destruct_CTyF; noconfusion. *)
(*       do 4 eexists; repeat split; eauto. *)
(*       ++ apply: ihA; eauto. *)
(*          rewrite /Nuprl CTyF_idempotent; eauto. *)
(*       ++ apply: ihB; eauto. *)
(*          rewrite /Nuprl CTyF_idempotent; eauto. *)
(*       ++ destruct_rel_specs => F _; apply: F. *)
(*       ++ destruct_rel_specs => _; apply. *)
(*     + do 4 eexists; repeat split; eauto. *)
(*       ++ apply: ihA; eauto. *)
(*       ++ apply: ihB; eauto. *)
(*       ++ destruct_rel_spec => F _; apply: F. *)
(*       ++ destruct_rel_spec => _; apply. *)
(*   Qed. *)


(*   Theorem Nuprl_ltr_monotone : *)
(*     ∀ i j κ A, *)
(*       Nuprl_monotone_case i j A *)
(*       → Nuprl_monotone_case i j (Tm.ltr κ A). *)
(*   Proof. *)
(*     move=> i j κ A ihA R p; rewrite /Nuprl => Nltr; rewrite -CTyF_Roll. *)
(*     apply: TyF.later. *)
(*     destruct_CTyF; noconfusion. *)
(*     + induction i; noconfusion. *)
(*       destruct_CTyF; noconfusion. *)
(*       do 3 eexists; repeat split. *)
(*       ++ eauto. *)
(*       ++ apply: Later.map => [X|]; last eauto. *)
(*          apply: ihA; eauto. *)
(*          rewrite /Nuprl CTyF_idempotent. *)
(*          eauto. *)
(*       ++ destruct_rel_spec => F _; apply: F. *)
(*       ++ destruct_rel_spec => _; apply. *)
(*     + do 3 eexists; repeat split. *)
(*       ++ eauto. *)
(*       ++ apply: Later.map => [X|]; last eauto. *)
(*          apply: ihA; eauto. *)
(*       ++ destruct_rel_spec => F _; apply: F. *)
(*       ++ destruct_rel_spec => _; apply. *)
(*   Qed. *)


(*   Theorem Nuprl_isect_monotone : *)
(*     ∀ i j A, *)
(*       (∀ κ, Nuprl_monotone_case i j (A κ)) *)
(*       → Nuprl_monotone_case i j (Tm.isect A). *)
(*   Proof. *)
(*     move=> i j A ihA R p; rewrite /Nuprl => Nisect. *)
(*     rewrite -CTyF_Roll. *)
(*     apply: TyF.isect. *)
(*     destruct_CTyF; noconfusion. *)
(*     + induction i; noconfusion. *)
(*       destruct_CTyF; noconfusion. *)
(*       do 2 eexists; repeat split; eauto. *)
(*       ++ move=> κ. *)
(*          specialize_clocks κ. *)
(*          apply: ihA; eauto. *)
(*          rewrite /Nuprl CTyF_idempotent. *)
(*          eauto. *)
(*       ++ destruct_rel_spec => F _; apply: F. *)
(*       ++ destruct_rel_spec => _; apply. *)
(*     + do 2 eexists; repeat split; eauto. *)
(*       ++ move=> κ. *)
(*          specialize_clocks κ. *)
(*          apply: ihA; eauto. *)
(*       ++ destruct_rel_spec => F _; apply: F. *)
(*       ++ destruct_rel_spec => _; apply. *)
(*   Qed. *)

(*   Theorem Welp : *)
(*     ∀ i n R, *)
(*       Spine i (Tm.univ n, R) *)
(*       → n < i. *)
(*   Proof. *)
(*     elim. *)
(*     + move=> n R S. *)
(*       simpl in S. *)
(*       destruct_CTyF; noconfusion. *)
(*     + move=> n ih n' R X. *)
(*       simpl in X. *)
(*       destruct_conjs. *)
(*       destruct_evals. *)
(*       omega. *)
(*   Qed. *)

(*   (* TODO *) *)
(*   Theorem Nuprl_monotone : *)
(*     ∀ A i j, Nuprl_monotone_case i j A. *)
(*   Proof. *)
(*     elim. *)
(*     + intros. *)
(*       omega. *)
(*     + apply: Nuprl_unit_monotone. *)
(*     + apply: Nuprl_bool_monotone. *)
(*     + obvious. *)
(*     + obvious. *)
(*     + obvious. *)
(*     + intros; apply: Nuprl_prod_monotone; eauto. *)
(*     + obvious. *)
(*     + obvious. *)
(*     + intros; apply: Nuprl_ltr_monotone; eauto. *)
(*     + intros; apply: Nuprl_isect_monotone; eauto. *)
(*     + admit. (* This one is hard, not sure how to do it. *) *)
(*   Admitted. *)











(*   (* TODO: move to a general location *) *)
(*   Theorem nat_max_leq : *)
(*     ∀ i j, *)
(*       i ≤ max i j. *)
(*   Proof. *)
(*     case => j. *)
(*     + omega. *)
(*     + case; firstorder. *)
(*   Qed. *)

(*   Theorem nat_max_commutative : *)
(*     ∀ i j, *)
(*       max i j = max j i. *)
(*   Proof. *)
(*     elim. *)
(*     + case; auto. *)
(*     + move=> n IH; elim. *)
(*       ++ auto. *)
(*       ++ move=> n' p. *)
(*          simpl. *)
(*          rewrite IH. *)
(*          auto. *)
(*   Qed. *)

(*   (* To show that the maximal refinement matrix is functional, *)
(*      we need to deal with type-behavior assignments at different levels. *)
(*      However, we can take the maximum of these levels, by monotonicity, *)
(*      bring the assignments up to a common level. *) *)
(*   Theorem Nuprlω_functional : matrix_functional Nuprlω. *)
(*   Proof. *)
(*     move=> A R1 R2 [n1 AR1] [n2 AR2]. *)
(*     apply: Nuprl_functional. *)
(*     + apply: Nuprl_monotone; *)
(*       first (apply: nat_max_leq; shelve); *)
(*       eauto. *)
(*     + apply: Nuprl_monotone; *)
(*       first (rewrite nat_max_commutative; apply: nat_max_leq); *)
(*       eauto. *)
(*   Qed. *)


(*   Notation "n ⊩ A type" := (∃ R, Nuprl n (A, R)) (at level 0, A at level 0, only parsing). *)
(*   Notation "n ⊩ A ∼ B type" := (∃ R, Nuprl n (A, R) ∧ Nuprl n (B, R)) (at level 0, A at level 0, B at level 0, only parsing). *)
(*   Notation "ω⊩ A type" := (∃ R, Nuprlω (A, R)) (at level 0, A at level 0, only parsing). *)

(*   Module ClosedRules. *)

(*     (* A nice hack from Adam Chlipala Theory, to force the resolution of *)
(*        some existential variables. *) *)
(*     Ltac equate M N := *)
(*       let r := constr:(eq_refl M : M = N) *)
(*       in idtac. *)

(*     Ltac simplify := *)
(*       simpl; *)
(*       repeat *)
(*         (match goal with *)
(*          | |- ∃ (R : behavior), Nuprl ?n ?X => eexists; rewrite -Roll *)
(*          | |- ?i ≤ ?j => omega *)
(*          | |- ∃ (x : ?A), ?P => eexists *)
(*          | |- ?P ∧ ?Q => split *)

(*          (* We will often encounter a semantic specification for a relation *)
(*             before we have even filled it in (i.e. it is an existential variable). *)
(*             So, we can force it to be instantiated to exactly the right thing. *) *)
(*          | |- ∀ e1 e2, ?R (e1, e2) ↔ @?S e1 e2 => *)
(*            equate R (fun e12 => S (fst e12) (snd e12)); *)
(*            intros *)

(*          | |- ?P ↔ ?Q => split *)
(*          end); eauto. *)

(*     (* A tactic to prove a rule by appealing to one of the *)
(*        constructors of the refinement matrix closure operator. *) *)
(*     Ltac prove_rule con := *)
(*       match goal with *)
(*       | |- ?n ⊩ ?A type => eexists; rewrite -Roll; apply: con; simplify *)
(*       end. *)

(*     Theorem unit_formation {n : nat} : n ⊩ Tm.unit type. *)
(*     Proof. *)
(*       prove_rule TyF.unit. *)
(*     Qed. *)

(*     Lemma univ_formation_S {n : nat} *)
(*       : (S n) ⊩ (Tm.univ n) type. *)
(*     Proof. *)
(*       prove_rule TyF.init. *)
(*     Qed. *)

(*     Theorem univ_formation {n i : nat} : *)
(*       i < n *)
(*       → n ⊩ (Tm.univ i) type. *)
(*     Proof. *)
(*       case => [| j q ]. *)
(*       + apply: univ_formation_S. *)
(*       + eexists. *)
(*         rewrite -Roll. *)
(*         apply: TyF.init. *)
(*         eexists. *)
(*         split; [ idtac | simplify ]. *)
(*         omega. *)
(*     Qed. *)

(*     Theorem prod_formation {n : nat} : *)
(*       ∀ A B, *)
(*         n ⊩ A type *)
(*         → n ⊩ B type *)
(*         → n ⊩ (Tm.prod A B) type. *)
(*     Proof. *)
(*       move=> A B [R1 D] [R2 E]. *)
(*       prove_rule TyF.prod. *)
(*     Qed. *)

(*     Lemma NuprlChoice {n : nat} {A : CLK → Tm.t 0} : *)
(*       (∀ κ, ∃ Rκ, Nuprl n (A κ, Rκ)) *)
(*       → ∃ S, ∀ κ, Nuprl n (A κ, S κ). *)
(*     Proof. *)
(*       move=> X. *)
(*       apply: (unique_choice (fun κ R => Nuprl n (A κ, R))) => κ. *)
(*       case: (X κ) => S T. *)
(*       eexists; split; eauto => S' T'. *)
(*       apply: Nuprl_functional; eauto. *)
(*     Qed. *)

(*     Theorem isect_formation {n : nat} : *)
(*       forall B, *)
(*         (∀ κ, n ⊩ (B κ) type) *)
(*         → n ⊩ (Tm.isect B) type. *)
(*     Proof. *)
(*       move=> B Q. *)
(*       case: (NuprlChoice Q) => S Q'. *)
(*       prove_rule TyF.isect. *)
(*     Qed. *)

(*     Theorem isect_irrelevance : *)
(*       forall n A, *)
(*         n ⊩ A type *)
(*         → n ⊩ A ∼ (Tm.isect (fun _ => A)) type. *)
(*     Proof. *)
(*       move=> n A [R AR]. *)
(*       eexists; split; eauto. *)
(*       rewrite -Roll; apply: TyF.isect. *)
(*       do 2 eexists; repeat split; *)
(*       first by [constructor]; *)
(*       intros. *)
(*       + exact AR. *)
(*       + assumption. *)
(*       + case: LocalClock; auto. *)
(*     Qed. *)

(*     Hint Resolve unit_formation univ_formation prod_formation isect_formation isect_irrelevance. *)
(*   End ClosedRules. *)

(*   Theorem test : ∃ n, n ⊩ (Tm.prod Tm.unit (Tm.univ 0)) type. *)
(*   Proof. *)
(*     eauto. *)
(*   Qed. *)

(*   Theorem test2 : ∃ n, n ⊩ (Tm.univ 0) ∼ (Tm.isect (fun _ => Tm.univ 0)) type. *)
(*     eauto. *)
(*   Qed. *)

(* End Univ. *)
