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
    simpl; intros; destruct_conjs;
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

Ltac destruct_CTyF :=
  repeat match goal with
  | T : CTyF _ _ |- _ =>
    apply: (CTyF_ind T); clear T
  end.

Ltac destruct_evals :=
  repeat
    match goal with
      | H : ?A ⇓ ?B |- _ => dependent destruction H
    end.

Ltac noconfusion :=
  try by [contradiction];
  intros; simpl in *;
  destruct_conjs;
  destruct_evals.


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


Ltac mytac :=
  backthruhyp; intros;
  specialize_hyps;
  destruct_conjs;
  repeat esplit; eauto;
  use_matrix_functionality_ih.

Theorem CTyF_Empty_functional : matrix_functional (CTyF Empty).
Proof.
  elim;
  rewrite /based_matrix_functional; intros;
  destruct_CTyF; intros;
  noconfusion;
  apply: binrel_extensionality; intros;
  split; intros;

  repeat
    match goal with
    | H : ∀ (e1 e2 : Tm.t 0), ?P |- ?R (?e1, ?e2) => specialize (H e1 e2); destruct H
    end.

  + firstorder.
  + firstorder.
  + mytac.
  + mytac.
  + backthruhyp.
    specialize_hyps.
    have welp : ▷[ H0] (CTyF Empty (H7, H8) /\ CTyF Empty (H7, H3) /\ H8 (x, y)).
    ++ repeat rewrite Later.cart; eauto.
    ++ apply: Later.map welp.
       move=> [X [Y Z]].
       specialize (H H8 H3 X Y).
       rewrite -H.
       auto.
  + backthruhyp.
    specialize_hyps.
    have welp : ▷[ H0 ] (CTyF Empty (H7, H8) ∧ CTyF Empty (H7, H3) ∧ H3 (x, y)).
    ++ repeat rewrite Later.cart; eauto.
    ++ apply: Later.map welp.
       move=> [X [Y Z]].
       specialize (H H8 H3 X Y).
       rewrite H.
       auto.
  + mytac.
  + mytac.
Qed.


Theorem CTyF_idempotent : CTyF (CTyF Empty) = CTyF Empty.
Proof.
  apply: functional_extensionality.
  case; elim; intros;
  apply: propositional_extensionality;
  split=> AR; destruct_CTyF; noconfusion; auto; rewrite -CTyF_Roll.
  + apply: TyF.unit.
    split; auto.
  + apply: TyF.unit.
    split; auto.
  + apply: TyF.prod.
    do 4 esplit; repeat split; eauto.
    ++ rewrite -H; eauto.
    ++ rewrite -H0; eauto.
    ++ move=> e1e2.
       edestruct H8.
       eauto.
    ++ move=> P.
       edestruct H8.
       eauto.
  + apply: TyF.prod.
    do 4 esplit; repeat split; eauto.
    ++ rewrite H; eauto.
    ++ rewrite H0; eauto.
    ++ move=> e1e2.
       edestruct H8.
       eauto.
    ++ move=> N.
       edestruct H8.
       eauto.
  + apply: TyF.later.
    exists H0, H1, H2; repeat split; eauto.
    ++ rewrite -H; eauto.
    ++ move=> e1e2.
       edestruct H5.
       eauto.
    ++ move=> N.
       edestruct H5.
       eauto.
  + apply: TyF.later.
    exists H0, H1, H2; repeat split; eauto.
    ++ rewrite H; eauto.
    ++ move=> e1e2.
       edestruct H5.
       eauto.
    ++ move=> N.
       edestruct H5.
       eauto.
  + apply: TyF.isect.
    do 2 esplit; repeat split; eauto; intros.
    ++ rewrite -H.
       eauto.
    ++ edestruct H4.
       eauto.
    ++ edestruct H4.
       eauto.
  + apply: TyF.isect.
    do 2 esplit; repeat split; eauto; intros.
    ++ rewrite H.
       eauto.
    ++ edestruct H4.
       eauto.
    ++ edestruct H4.
       eauto.
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


  Theorem Nuprl_functional : ∀ i, matrix_functional (Nuprl i).
  Proof.
    case => [A | n].
    + rewrite /Nuprl /Spine //=.
      rewrite /based_matrix_functional; intros.
      rewrite CTyF_idempotent in H, H0.
      apply: CTyF_Empty_functional; eauto.
    + elim;
      rewrite /based_matrix_functional /Nuprl; intros;
      destruct_CTyF => C1 C2;
      noconfusion;
      apply: binrel_extensionality => e1 e2;
      repeat
        match goal with
        | H : ∀ (e1 e2 : Tm.t 0), ?P |- _ => specialize (H e1 e2); destruct H
        end;

      intros;
      split; intros;
      backthruhyp;
      specialize_hyps; eauto.

      ++ destruct_conjs;
         repeat esplit; eauto;
         use_matrix_functionality_ih.

      ++ destruct_conjs;
         repeat esplit; eauto;
         use_matrix_functionality_ih.

      ++ match type of H8 with
         | ▷[ _ ] ?tyH8 =>
           match type of H3 with
           | ▷[ _ ] ?tyH3 =>
             match type of H4 with
             | ▷[ _ ] ?tyH4 =>
               have welp : ▷[ C1 ] (tyH8 ∧ tyH4 ∧ tyH3)
             end
           end
         end.
         +++ repeat rewrite Later.cart. eauto.
         +++ apply: Later.map welp.
             move=> [X [Y Z]].
             use_matrix_functionality_ih.

      ++ match type of H8 with
         | ▷[ _ ] ?tyH8 =>
           match type of H3 with
           | ▷[ _ ] ?tyH3 =>
             match type of H0 with
             | ▷[ _ ] ?tyH0 =>
               have welp : ▷[ C1 ] (tyH8 ∧ tyH0 ∧ tyH3)
             end
           end
         end.
         +++ repeat rewrite Later.cart. eauto.
         +++ apply: Later.map welp.
             move=> [X [Y Z]].
             use_matrix_functionality_ih.

      ++ intros.
         specialize_hyps.
         use_matrix_functionality_ih.
      ++ intros.
         specialize_hyps.
         use_matrix_functionality_ih.
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

  (* Theorem Nuprl_monotone_S : *)
  (*   ∀ i A R, *)
  (*     Nuprl i (A, R) *)
  (*     → Nuprl (S i) (A, R). *)
  (* Proof. *)
  (*   move=> i. *)
  (*   rewrite /Nuprl. *)
  (*   elim; intros; rewrite -CTyF_Roll; destruct_CTyF; noconfusion. *)
  (*   + omega. *)
  (*   + apply: TyF.unit. *)
  (*     simpl. *)
  (*     destruct i; noconfusion. *)
  (*     destruct_CTyF; noconfusion. *)
  (*     constructor; eauto. *)
  (*   + apply: TyF.unit. *)
  (*     simpl. *)
  (*     constructor; eauto. *)
  (*   + apply: TyF.bool. *)
  (*     destruct i; noconfusion. *)
  (*     destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion. *)
  (*     destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*     apply: TyF.prod. *)
  (*     simpl in *. *)
  (*     exists H1, H2, H3, H4. *)
  (*     constructor; auto. *)
  (*     repeat constructor. *)
  (*     ++ apply: H. *)
  (*        rewrite CTyF_idempotent. *)
  (*        auto. *)
  (*     ++ apply: H0. *)
  (*        rewrite CTyF_idempotent. *)
  (*        auto. *)
  (*     ++ move=> e1e2. *)
  (*        specialize (H8 e1 e2). *)
  (*        destruct H8. *)
  (*        specialize_hyps. *)
  (*        auto. *)
  (*     ++ intro. *)
  (*        destruct (H8 e1 e2). *)
  (*        apply: H10. *)
  (*        auto. *)
  (*   + apply: TyF.prod. *)
  (*     simpl in *. *)
  (*     exists H1, H2, H3, H4. *)
  (*     constructor; auto. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*     (* This is only easy because I don't have a clause for function *)
  (*        types yet ;-) *) *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*   + destruct i; noconfusion; destruct_CTyF; noconfusion. *)
  (*     apply: TyF.isect. *)
  (*     simpl in *. *)
  (*     exists H0, H1. *)
  (*     constructor; eauto. *)
  (*     constructor; eauto. *)
  (*     move=> κ. *)
  (*     specialize (H κ (H1 κ)). *)
  (*     apply: H. *)
  (*     rewrite CTyF_idempotent. *)
  (*     apply: H3. *)
  (*   + apply: TyF.isect. *)
  (*     exists H0, H1. *)
  (*     eauto. *)
  (*   + induction i; simpl in H. *)
  (*     ++ destruct_CTyF; noconfusion. *)
  (*     ++ apply: TyF.init. *)
  (*        destruct_conjs. *)
  (*        dependent induction H1. *)
  (*        exists H. *)
  (*        repeat split; eauto. *)
  (*        +++ move=> e1e2. *)
  (*            specialize (H2 e1 e2). *)
  (*            destruct H2. *)
  (*            specialize_hyps. *)
  (*            destruct H1. *)
  (*            exists x. *)
  (*            destruct H1. *)
  (*            clear H2. *)
  (*            split. *)
  (*            ++++ *)


  (* Abort. *)






  Definition Nuprl_monotone_case (i j : nat) (A : Tm.t 0) : Prop :=
    ∀ R,
      i ≤ j
      → Nuprl i (A, R)
      → Nuprl j (A, R).


  Theorem Nuprl_unit_monotone : ∀ i j, Nuprl_monotone_case i j Tm.unit.
  Proof.
    move=> i j R p N.
    unfold Nuprl in *.
    destruct_CTyF; noconfusion.
    + rewrite -CTyF_Roll.
      induction i.
      ++ apply: TyF.unit.
         simpl in H.
         destruct_CTyF; noconfusion.
         split; eauto.
      ++ apply: IHi.
         +++ omega.
         +++ simpl in H.
             destruct_conjs.
             destruct_evals.
    + rewrite -CTyF_Roll.
      apply: TyF.unit.
      split; auto.
  Qed.


  Theorem Nuprl_bool_monotone : ∀ i j, Nuprl_monotone_case i j Tm.bool.
  Proof.
    move=> i j R p N.
    unfold Nuprl in *.
    destruct_CTyF; noconfusion.
    + rewrite -CTyF_Roll.
      induction i.
      ++ apply: TyF.bool.
         simpl in H.
         destruct_CTyF; noconfusion.
      ++ apply: IHi.
         +++ omega.
         +++ simpl in H.
             destruct_conjs.
             destruct_evals.
  Qed.

  Theorem Nuprl_prod_monotone :
    ∀ i j A B,
      Nuprl_monotone_case i j A
      → Nuprl_monotone_case i j B
      → Nuprl_monotone_case i j (Tm.prod A B).
  Proof.
    move=> i j A B ihA ihB R p Nprod.
    rewrite /Nuprl.
    rewrite -CTyF_Roll.
    apply: TyF.prod.
    rewrite /Nuprl in Nprod.
    destruct_CTyF; noconfusion.
    + induction i; noconfusion.
      destruct_CTyF; noconfusion.
      exists H, H0, H1, H2.
      repeat split; eauto.
      ++ apply: ihA; eauto.
         rewrite /Nuprl CTyF_idempotent; auto.
      ++ apply: ihB; eauto.
         rewrite /Nuprl CTyF_idempotent; auto.
      ++ move=> e1e2.
         destruct (H6 e1 e2).
         backthruhyp.
         auto.
      ++ move=> P.
         destruct (H6 e1 e2).
         backthruhyp.
         auto.
    + exists H, H0, H1, H2.
      repeat split; eauto.
      ++ apply: ihA; eauto.
      ++ apply: ihB; eauto.
      ++ move=> e1e2.
         destruct (H6 e1 e2).
         backthruhyp.
         eauto.
      ++ move=> P.
         destruct (H6 e1 e2).
         backthruhyp.
         eauto.
  Qed.

  Theorem Nuprl_ltr_monotone :
    ∀ i j κ A,
      Nuprl_monotone_case i j A
      → Nuprl_monotone_case i j (Tm.ltr κ A).
  Proof.
    move=> i j κ A ihA  R p Nltr.
    rewrite /Nuprl -CTyF_Roll.
    apply: TyF.later.
    rewrite /Nuprl in Nltr.
    destruct_CTyF; noconfusion.
    induction i; noconfusion.
    destruct_CTyF; noconfusion.
    + exists H, H0, H1.
      repeat split; eauto.
      ++ apply: Later.map H3 => X.
         apply: ihA; eauto.
         rewrite /Nuprl.
         rewrite CTyF_idempotent.
         auto.
      ++ move=> e1e2.
         edestruct H4.
         apply: H2.
         auto.
      ++ move=> X.
         edestruct H4.
         apply: H5.
         auto.
    + exists H, H0, H1; repeat split; eauto.
      ++ apply: Later.map H3.
         apply: ihA.
         auto.
      ++ edestruct H4.
         apply: H2.
      ++ edestruct H4.
         eauto.
  Qed.

  Theorem Nuprl_isect_monotone :
    ∀ i j A,
      (∀ κ, Nuprl_monotone_case i j (A κ))
      → Nuprl_monotone_case i j (Tm.isect A).
  Proof.
    move=> i j A ihA R p Nisect.
    rewrite /Nuprl -CTyF_Roll.
    apply: TyF.isect.
    rewrite /Nuprl in Nisect.
    destruct_CTyF; noconfusion.
    + induction i; noconfusion.
      destruct_CTyF; noconfusion.
      exists H, H0; repeat split; eauto.
      ++ move=> κ.
         specialize (ihA κ).
         apply: ihA; eauto.
         rewrite /Nuprl.
         rewrite CTyF_idempotent.
         apply: H2.
      ++ move=> e1e2 κ.
         specialize (H2 κ).
         edestruct H3.
         apply: H1.
         auto.
      ++ move=> X.
         edestruct H3.
         apply: H4.
         auto.
    + exists H, H0.
      repeat split; eauto.
      ++ move=> κ.
         apply: ihA; eauto.
         apply: H2.
      ++ move=> e1e2 κ.
         specialize (H2 κ).
         edestruct H3.
         apply: H1.
         auto.
      ++ move=> X.
         edestruct H3.
         apply: H4.
         auto.
  Qed.

  Eval simpl in (Spine 1).
  Theorem Welp :
    ∀ i n R,
      Spine i (Tm.univ n, R)
      → n < i.
  Proof.
    elim.
    + move=> n R S.
      simpl in S.
      destruct_CTyF; noconfusion.
    + move=> n ih n' R X.
      simpl in X.
      destruct_conjs.
      destruct_evals.
      omega.
  Qed.

  (* TODO *)
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
    + admit. (* This one is hard, not sure how to do it. *)
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

  (* To show that the maximal refinement matrix is functional,
     we need to deal with type-behavior assignments at different levels.
     However, we can take the maximum of these levels, by monotonicity,
     bring the assignments up to a common level. *)
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

    (* A nice hack from Adam Chlipala Theory, to force the resolution of
       some existential variables. *)
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

         (* We will often encounter a semantic specification for a relation
            before we have even filled it in (i.e. it is an existential variable).
            So, we can force it to be instantiated to exactly the right thing. *)
         | |- ∀ e1 e2, ?R (e1, e2) ↔ @?S e1 e2 =>
           equate R (fun e12 => S (fst e12) (snd e12));
           intros

         | |- ?P ↔ ?Q => split
         end); eauto.

    (* A tactic to prove a rule by appealing to one of the
       constructors of the refinement matrix closure operator. *)
    Ltac prove_rule con :=
      match goal with
      | |- ?n ⊩ ?A type => eexists; rewrite -Roll; apply: con; simplify
      end.

    Theorem unit_formation {n : nat} : n ⊩ Tm.unit type.
    Proof.
      prove_rule TyF.unit.
    Qed.

    Lemma univ_formation_S {n : nat}
      : (S n) ⊩ (Tm.univ n) type.
    Proof.
      prove_rule TyF.init.
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
        eexists.
        split; [ idtac | simplify ].
        omega.
    Qed.

    Theorem prod_formation {n : nat} :
      ∀ A B,
        n ⊩ A type
        → n ⊩ B type
        → n ⊩ (Tm.prod A B) type.
    Proof.
      move=> A B [R1 D] [R2 E].
      prove_rule TyF.prod.
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
    Qed.

    Theorem isect_irrelevance :
      forall n A,
        n ⊩ A type
        → n ⊩ A ∼ (Tm.isect (fun _ => A)) type.
    Proof.
      move=> n A [R AR].
      eexists; split; eauto.
      rewrite -Roll; apply: TyF.isect.
      do 2 eexists; repeat split;
      first by [constructor];
      intros.
      + exact AR.
      + assumption.
      + case: LocalClock; auto.
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
