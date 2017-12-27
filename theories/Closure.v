Require Import Unicode.Utf8 Program.Equality Logic.FunctionalExtensionality Classes.Morphisms Coq.omega.Omega.
From gctt Require Import Notation OrderTheory Axioms Var Term OpSem TypeSystem.
From gctt Require Tactic.
Module T := Tactic.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Module Connective.
  Inductive ctor := unit | bool | prod | arr | later | isect.

  Inductive unit_val : rel :=
  | ax : unit_val (Tm.ax, Tm.ax).

  Inductive bool_val : rel :=
  | tt : bool_val (Tm.tt, Tm.tt)
  | ff : bool_val (Tm.ff, Tm.ff).

  Inductive prod_el (R0 : rel) (R1 : Tm.t 0 → rel) : rel :=
  | pair :
      ∀ e0 e1,
        R0 (Tm.fst e0, Tm.fst e1)
        ∧ R1 (Tm.fst e0) (Tm.snd e0, Tm.snd e1)
        → prod_el R0 R1 (e0, e1).

  Inductive fun_val (R0 : rel) (R1 : Tm.t 0 → rel) : rel :=
  | lam :
      ∀ f0 f1,
        (∀ e0 e1,
            R0 (e0, e1)
            → R1 e0 ((f0 ⫽ Sub.inst0 e0)%tm, (f1 ⫽ Sub.inst0 e1)%tm))
        → fun_val R0 R1 (Tm.lam f0, Tm.lam f1).

  Inductive cext (R : rel) : rel :=
  | mk_cext :
      ∀ e0 e1 v0 v1,
        e0 ⇓ v0
        → e1 ⇓ v1
        → R (v0, v1)
        → cext R (e0, e1).

  Inductive has (τ : cts) : ctor → Tm.t 0 × rel → Ω :=
  | has_unit : has τ unit (Tm.unit, cext unit_val)
  | has_bool : has τ bool (Tm.bool, cext bool_val)
  | has_prod :
      ∀ A0 A1 R0 R1,
        τ (A0, R0)
        → (∀ e0 e1,
              R0 (e0, e1)
              → τ ((A1 ⫽ Sub.inst0 e0)%tm, R1 e0)
                ∧ τ ((A1 ⫽ Sub.inst0 e0)%tm, R1 e1)
                ∧ τ ((A1 ⫽ Sub.inst0 e1)%tm, R1 e1)
                ∧ τ ((A1 ⫽ Sub.inst0 e1)%tm, R1 e0))
        → has τ prod (Tm.prod A0 A1, prod_el R0 R1)
  | has_arr :
      ∀ A0 A1 R0 R1,
        τ (A0, R0)
        → (∀ e0 e1,
              R0 (e0, e1)
              → τ ((A1 ⫽ Sub.inst0 e0)%tm, R1 e0)
                ∧ τ ((A1 ⫽ Sub.inst0 e0)%tm, R1 e1)
                ∧ τ ((A1 ⫽ Sub.inst0 e1)%tm, R1 e1)
                ∧ τ ((A1 ⫽ Sub.inst0 e1)%tm, R1 e0))

        → has τ arr (Tm.arr A0 A1, cext (fun_val R0 R1))

  | has_later :
      ∀ κ B R,
        ▷[κ] (τ (B, R))
        → has τ later (Tm.ltr κ B, fun e0e1 => ▷[κ] (R e0e1))
  | has_isect :
      ∀ B S,
        (∀ κ, τ (B κ, S κ))
        → has τ isect (Tm.isect B, fun e0e1 => ∀ κ, S κ e0e1).

  Hint Constructors has cext prod_el bool_val unit_val.

  Local Hint Resolve Later.map.
  Theorem monotone : ∀ ι, Proper (Poset.order ==> Poset.order) (fun τ => has τ ι).
  Proof.
    move=> ι τ0 τ1 τ01 [A R] H.
    dependent destruction H;
    try by [eauto].

    constructor.
    + auto.
    + move=> e0 e1 e0e1.
      edestruct H0; eauto.
      T.destruct_conjs.
      repeat split; eauto.
    + constructor; eauto.
      move=> e0 e1 e0e1.
      edestruct H0; eauto;
      T.destruct_conjs;
      repeat split; eauto.
  Qed.

  Hint Resolve monotone.

  Ltac destruct_cext :=
    match goal with
    | H : cext _ _ |- _ => dependent destruction H
    end.
End Connective.

Module Sig.
  (* For each refinement cts σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/rels. *)
  Inductive t (σ τ : cts) : (Tm.t 0 × rel) → Ω :=
  | init :
      ∀ X,
        σ X
        → t σ τ X

  | conn :
      ∀ ι A A0 R,
        A ⇓ A0
        → Connective.has τ ι (A0, R)
        → t σ τ (A, R).

  Instance monotonicity {σ : cts} : Monotone (t σ).
  Proof.
    constructor => τ1 τ2 p [A R].
    case => *.
    + by econstructor.
    + econstructor; try by [eauto];
      apply: Connective.monotone;
      eauto.
  Qed.
End Sig.


Module Clo.
  Program Definition t (σ : cts) := LFP.t (Sig.t σ).

  Theorem roll : ∀ σ, Sig.t σ (t σ) = t σ.
  Proof.
    move=> σ.
    apply: binrel_extensionality => [A R].
    T.split => [X | X]; [rewrite /t|];
    edestruct (LFP.roll (Sig.t σ));
    auto.
  Qed.

  Lemma map_has {σ ρ ι A R} :
    ρ ⊑ σ
    → Connective.has ρ ι (A, R)
    → Connective.has σ ι (A, R).
  Proof.
    move=> sub has.
    dependent destruction has; eauto.
    - constructor; eauto.
      move=> e0 e1 e01.
      edestruct H0; T.destruct_conjs; repeat split; eauto.
    - constructor; eauto.
      move=> e0 e1 e01.
      edestruct H0; T.destruct_conjs; repeat split; eauto.
    - constructor.
      Later.gather; eauto.
  Qed.

  Theorem ind :
    ∀ Y (σ ρ : cts),
      t σ Y
      → (∀ X, σ X → ρ X)
      → (∀ ι A A0 R, A ⇓ A0 → Connective.has ρ ι (A0, R) → ρ (A, R))
      → ρ Y.
  Proof.
    move=> [A R] σ ρ AcloR init conn.
    rewrite /t /LFP.t in AcloR.
    simpl in AcloR.
    rewrite -/cts in AcloR.

    destruct AcloR.
    destruct H.
    apply: H; auto.
    move=> [A' R']; elim; eauto.
  Qed.

  Local Hint Constructors Sig.t.

  Ltac elim_clo :=
    let x := fresh in
    move=> x;
    apply: (ind x).

  Instance monotonicity : Monotone t.
  Proof.
    split; move=> ? ? ? ?.
    elim_clo => *; rewrite -roll; eauto.
  Qed.

  Ltac use_universe_system :=
    match goal with
    | H : TS.universe_system ?σ, H' : ?σ ?X |- _ =>
      destruct H as [H]; destruct (H X H')
    end.


  Local Ltac rewrite_functionality_ih :=
    repeat match goal with
    | ih : TS.extensional_at _ _ |- _ =>
      rewrite /TS.extensional_at in ih;
      simpl in ih;
      erewrite ih
    end.

  Local Ltac moves :=
    move=> *.

  Ltac destruct_sig :=
    match goal with
    | H : Sig.t _ _ _ |- _ => dependent destruction H
    end.

  Ltac ind_sig :=
    match goal with
    | H : Sig.t _ _ _ |- _ => dependent induction H
    end.

  Ltac destruct_has :=
    match goal with
    | H : Connective.has _ _ _ |- _ => dependent destruction H
    end.

  Ltac destruct_clo :=
    match goal with
    | H : t _ _ |- _ => rewrite -roll in H; dependent destruction H
    end.


  Theorem connective_not_universe {τ i ι A' A R} {P : Ω} :
    Connective.has τ ι (A', R)
    → A ⇓ A'
    → A ⇓ Tm.univ i
    → P.
  Proof.
    move=> has eval1 eval2.
    dependent destruction has;
    by OpSem.evals_to_eq.
  Qed.


  Local Ltac cleanup :=
    simpl in *;
    try use_universe_system;
    OpSem.evals_to_eq;
    T.destruct_eqs;
    auto.

  Instance extensionality {σ} :
    TS.universe_system σ
    → TS.extensional σ
    → TS.extensional (t σ).
  Proof.
    move=> ? [ext]; constructor => ? ?; elim_clo; clear H.

    - move=> [? ?] ? ? ?.
      destruct_clo.
      + by apply: ext.
      + use_universe_system.
        destruct_has; by OpSem.evals_to_eq.

    - move=> ? ? ? ? ? ?; simpl in *.
      destruct_has => ? ?;
      destruct_clo; try by [cleanup];
      destruct_has; cleanup.
      + T.eqcd; case => e0 e1; apply: propositional_extensionality; split => e0e1.
        * dependent destruction e0e1.
          destruct H1.
          constructor; split.
          ** replace R2 with R0; eauto.
          ** replace (R3 (e0 .1)%tm) with (R1 (e0 .1)%tm); eauto.
             destruct (H0 (e0.1)%tm (e1.1)%tm) as [H01 [H02 [H03 H04]]]; auto.
             replace R2 with R0 in H3; eauto.
             destruct (H3 (e0.1)%tm (e1.1)%tm); eauto.
        * dependent destruction e0e1.
          destruct H1.
          constructor; split.
          ** replace R0 with R2; auto.
             symmetry; eauto.
          ** replace (R1 (e0.1)%tm) with (R3 (e0.1)%tm); eauto.
             destruct (H0 (e0.1)%tm (e1.1)%tm) as [H01 [H02 [H03 H04]]]; eauto.
             *** replace R0 with R2; eauto.
                 symmetry; eauto.
             *** symmetry.
                 apply: H01; eauto.
                 destruct (H3 (e0.1)%tm (e1.1)%tm); eauto.
      + f_equal.
        T.eqcd; case => e0 e1.
        apply: propositional_extensionality; split => Q.
        * dependent destruction Q.
          constructor => e0 e1 e0e1.
          replace (R3 e0) with (R1 e0).
          ** apply: H1.
             replace R0 with R2; auto.
             symmetry.
             by apply: H.
          ** edestruct H0 as [H01 H02].
             *** replace R0 with R2; eauto.
                 symmetry.
                 by apply: H.
             *** apply: H01; simpl.
                 edestruct H3 as [? [? ?]]; eauto.
        * dependent destruction Q.
          constructor => e0 e1 e0e1.
          ** replace (R1 e0) with (R3 e0).
             *** apply: H1.
                 replace R2 with R0; auto.
             *** edestruct (H0 e0 e1) as [H00 H01]; eauto.
                 symmetry.
                 apply: H00; simpl.
                 edestruct H3.
                 **** replace R2 with R0.
                      eauto.
                      apply: H; auto.
                 **** auto.
      + do ? (T.eqcd; moves).
        Later.gather => *; T.destruct_conjs.
        rewrite_functionality_ih; eauto.
      + do ? (T.eqcd; moves).
        T.specialize_hyps.
        rewrite_functionality_ih; eauto.
  Qed.

  Theorem cext_per {R} :
    is_per R
    → is_per (Connective.cext R).
  Proof.
    move=> [ihSm ihTr].
    constructor.
    - move=> e0 e1 H1.
      dependent destruction H1.
      econstructor; eauto.
    - move=> e0 e1 e2 H1 H2.
      dependent destruction H1.
      dependent destruction H2.
      OpSem.evals_to_eq.
      T.destruct_eqs.
      econstructor; eauto.
  Qed.

  Theorem unit_val_per : is_per Connective.unit_val.
  Proof.
    constructor.
    - move=> e0 e1 H1.
      by dependent destruction H1.
    - move=> ? ? ? H1 H2.
      by [dependent destruction H1;
          dependent destruction H2].
  Qed.

  Theorem bool_val_per : is_per Connective.bool_val.
  Proof.
    constructor.
    - move=> e0 e1 H1.
      by dependent destruction H1.
    - move=> ? ? ? H1 H2.
      by [dependent destruction H1;
          dependent destruction H2].
  Qed.
(*
  Theorem prod_val_per {R0 R1} :
    is_per R0
    → (∀ e0 e1, R0 (e0, e1) → R1 e0 = R1 e1 ∧ is_per (R1 e1))
    → is_per (Connective.prod_val R0 R1).
  Proof.
    move=> [ihSm0 ihTr0] ihper1.
    constructor.
    - move=> e0 e1 H1.
      dependent destruction H1.
      constructor; eauto.
      destruct (ihper1 e10 e00); eauto.
      apply: symmetric; eauto; by rewrite H1.
    - move=> ? ? ? H1 H2.
      dependent destruction H1.
      dependent destruction H2.
      constructor; eauto.
      destruct (ihper1 e10 e00); eauto.
      apply: transitive; rewrite -H3; eauto;
      rewrite H3; auto.
  Qed.

*)

  Theorem fun_val_per {R0 R1} :
    is_per R0
    → (∀ e0 e1, R0 (e0, e1) → R1 e0 = R1 e1 ∧ is_per (R1 e1))
    → is_per (Connective.fun_val R0 R1).
  Proof.
    move=> R0per ihper1.
    constructor.
    - move=> f0 f1 H1.
      dependent destruction H1.
      constructor => e0 e1 H2.
      edestruct ihper1; eauto.
      apply: symmetric; rewrite H0; auto.
      apply: H.
      by apply: symmetric.
    - move=> f0 f1 f2 H1 H2.
      dependent destruction H1.
      dependent destruction H2.
      constructor => e0 e1 H3.
      edestruct ihper1; eauto.
      apply: transitive.
      + by rewrite H1.
      + apply: H; eauto.
      + rewrite H1.
        apply: H0.
        apply: transitive; auto.
        * apply: symmetric; eauto.
        * auto.
  Qed.

  Theorem cext_computational {R} :
    rel_computational (Connective.cext R).
  Proof.
    move=> e0 e1 e2 e01 cext.
    Connective.destruct_cext.
    econstructor; eauto.
  Qed.

  Hint Resolve cext_per cext_computational unit_val_per bool_val_per cext_per.
  Hint Constructors is_cper.

  Ltac destruct_cper :=
    repeat
      match goal with
      | H : is_cper _ |- _ => destruct H
      end.

  Ltac destruct_per :=
    repeat
      match goal with
      | H : is_per _ |- _ => destruct H
      end.

  Theorem fst_eval :
    ∀ e e0 e1 v0,
      e ⇓ ⟨e0,e1⟩
      → e0 ⇓ v0
      → e.1 ⇓ v0.
  Proof.
    move=> e e0 e1 v0 H0 H1.
    dependent induction H0.
    dependent induction eval_steps.
    - constructor; auto.
      + econstructor.
        * by apply: step_fst_pair.
        * by dependent destruction H1.
      + by destruct H1.
    - dependent destruction H1.
      constructor; auto.
      econstructor.
      * apply: step_fst_cong; eauto.
      * edestruct IHeval_steps; eauto.
  Qed.

  Theorem snd_eval :
    ∀ e e0 e1 v,
      e ⇓ ⟨e0,e1⟩
      → e1 ⇓ v
      → e.2 ⇓ v.
  Proof.
    move=> e e0 e1 v H0 H1.
    dependent induction H0.
    dependent induction eval_steps.
    - constructor; auto.
      + econstructor.
        * by apply: step_snd_pair.
        * by dependent destruction H1.
      + by destruct H1.
    - dependent destruction H1.
      constructor; auto.
      econstructor.
      * apply: step_snd_cong; eauto.
      * edestruct IHeval_steps; eauto.
  Qed.

  Theorem fst_eval_inv :
    ∀ e v1,
      e.1 ⇓ v1
      → ∃ e1 e2, e1 ⇓ v1 ∧ e ⇓ ⟨e1, e2⟩.
  Proof.
    move=> e e1 H.
    dependent induction H.
    dependent induction eval_steps.
    - dependent induction eval_val.
    - dependent induction H.
      + edestruct IHeval_steps; eauto.
        case: H0 => [z [zz zzz]].
        exists x, z; split; auto.
        constructor; auto.
        econstructor; eauto.
        dependent destruction zzz.
        eauto.
      + by exists e1, e2.
  Qed.

  Theorem snd_eval_inv :
    ∀ e v,
      e.2 ⇓ v
      → ∃ e1 e2, e2 ⇓ v ∧ e ⇓ ⟨e1,e2⟩.
  Proof.
    move=> e e1 H.
    dependent induction H.
    dependent induction eval_steps.
    - dependent induction eval_val.
    - dependent induction H.
      + edestruct IHeval_steps; eauto.
        case: H0 => [z [zz zzz]].
        exists x, z; split; auto.
        constructor; auto.
        econstructor; eauto.
        dependent destruction zzz.
        eauto.
      + by exists e1, e2.
  Qed.

  Theorem fst_cong_approx :
    ∀ e0 e1,
      e0 ≼₀ e1
      → Tm.fst e0 ≼₀ Tm.fst e1.
  Proof.
    move=> e0 e1 e01 p1 ℰ.
    have := fst_eval_inv ℰ.
    move=> [e' [p2 [H0 H1]]].
    apply: fst_eval; eauto.
  Qed.

  Theorem snd_cong_approx :
    ∀ e0 e1,
      e0 ≼₀ e1
      → Tm.snd e0 ≼₀ Tm.snd e1.
  Proof.
    move=> e0 e1 e01 p1 ℰ.
    have := snd_eval_inv ℰ.
    move=> [e' [p2 [H0 H1]]].
    apply: snd_eval; eauto.
  Qed.

  (* HORRIFIC *)
  Instance cper_valued {σ} :
    TS.cper_valued σ
    → TS.extensional σ
    → TS.universe_system σ
    → TS.cper_valued (t σ).
  Proof.
    move=> [IH] ext uni; constructor => A R 𝒟.
    destruct (@ind (A, R) σ (fun X => t σ X ∧ is_cper (snd X))); auto; move {𝒟 A R}.
    - move=> [A R] 𝒟.
      split.
      + rewrite -roll.
        by apply: Sig.init.
      + eauto.

    - move=> ι A' A'0 R' 𝒟' ℰ //=; split.
      + rewrite -roll.
        apply: Sig.conn; eauto.
        apply: map_has; eauto.
        move=> ? [? ?] //=.
      + destruct_has; simpl; destruct_cper; simpl in *; try by [constructor; eauto]; cleanup.
        * constructor.
          ** constructor.
             *** move=> e0 e1 e01.
                 dependent destruction e01.
                 econstructor; eauto.
                 destruct H1; destruct H.
                 split; eauto.
                 **** apply: symmetric; auto.
                      by apply: per.
                 **** replace (R1 (e1.1)%tm) with (R1 (e0.1)%tm).
                      ***** apply: symmetric; auto.
                            edestruct H0; eauto.
                            T.destruct_conjs.
                            by apply: per.
                      ***** edestruct H0; eauto.
                            T.destruct_conjs.
                            eapply (TS.is_extensional (t σ)); eauto.

             *** move=> e0 e1 e2 e01 e12.
                 dependent destruction e01.
                 destruct H1.
                 dependent destruction e12.
                 destruct H3.
                 econstructor; eauto; split.

                 **** apply: transitive; eauto.
                      edestruct H0; eauto.
                      T.destruct_conjs.
                      by apply: per.
                 **** replace (R1 (e1.1)%tm) with (R1 (e0.1)%tm) in H4.
                      ***** apply: transitive; eauto.
                            edestruct (H0 (e0.1)%tm); eauto.
                            T.destruct_conjs.
                            by apply: per.
                      ***** edestruct (H0 (e0.1)%tm); eauto.
                            T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.

          ** move=> e0 e1 e2 e0e1 el.
             dependent destruction el.
             destruct H.
             destruct H1.
             constructor; split.
             *** apply: crel; first by [auto]; last by eauto.
                 by apply: fst_cong_approx.
             *** replace (R1 (e1.1)%tm) with (R1 (e0.1)%tm).
                 **** apply: crel; last by eauto.
                      ***** edestruct H0; eauto; T.destruct_conjs; eauto.
                      ***** by apply: snd_cong_approx.
                 **** edestruct (H0 (e1.1)%tm (e0.1)%tm); eauto.
                      ***** suff H4: R0 ((e0.1)%tm, (e0.1)%tm).
                            ****** apply: crel; [auto|apply: fst_cong_approx e0e1|eauto].
                            ****** apply: transitive; first by [apply: per].
                            ******* eauto.
                            ******* apply: symmetric; first by [apply: per]; eauto.
                      ***** T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.


        * constructor.
          ** constructor.
             *** move=> e0 e1 e01.
                 dependent destruction e01.
                 econstructor; eauto.
                 dependent destruction H3.
                 constructor.
                 move=> e2 e3 e23.
                 apply: symmetric.
                 **** edestruct H0; eauto.
                      T.destruct_conjs.
                      apply: per; eauto.
                 **** replace (R1 e2) with (R1 e3).
                      ***** apply: H3; eauto.
                            apply: symmetric; auto.
                            apply: per; T.destruct_conjs; eauto.
                      ***** edestruct H0; eauto.
                            T.destruct_conjs.
                            eapply (@TS.is_extensional (t σ)); eauto.
                            apply: extensionality.

             *** move=> e0 e1 e2 e01 e12.
                 dependent destruction e01.
                 dependent destruction e12.
                 econstructor; eauto.
                 dependent destruction H3.
                 dependent destruction H6.
                 OpSem.evals_to_eq.
                 T.destruct_eqs.
                 constructor => e3 e4 e34.
                 destruct (H0 e3 e4); auto.
                 T.destruct_conjs.
                 apply: transitive; first by apply: per; eauto.
                 **** apply: H3; eauto.
                 **** replace (R1 e3) with (R1 e4).
                      ***** apply: H6; eauto.
                            apply: transitive; first by [apply: per; eauto]; eauto.
                            apply: symmetric; first by [apply: per; eauto]; eauto.
                      *****
                      match goal with
                      | H1 : t σ (?A, ?R1), H2 : t σ (?A, ?R2) |- ?R1 = ?R2 =>
                        eapply (@TS.is_extensional (t σ));
                          [ apply: extensionality; eauto
                          | exact H1
                          | exact H2]
                      end.

          ** eauto.

        * constructor.
          ** constructor.
             *** move=> e0 e1 H1.
                 Later.gather.
                 move=> //= [[ihR0 ?] e0e1].
                 apply: symmetric; eauto; apply: per; eauto.

             *** move=> e0 e1 e2 H1 H2.
                 Later.gather.
                 move=> //= [[? ?] [e0e1 e1e2]].
                 apply: transitive; eauto.
                 by apply: per.
          ** move=> ? ? ? ? ?.
             Later.gather.
             move=> [[? ?] ?].
             apply: crel; eauto.

        * constructor.
          ** constructor.
             *** move=> ? ? ? ?.
                 T.specialize_hyps.
                 case: H => //= [? ?].
                 destruct_cper.
                 destruct_per.
                 eauto.
             *** move=> ? ? ? ? ? ?.
                 T.specialize_hyps.
                 case: H => //= [? ?].
                 destruct_cper; destruct_per; eauto.
          ** move=> ? ? ? ? ?  ?.
             T.specialize_hyps.
             T.destruct_conjs.
             destruct_cper.
             eauto.
  Qed.

  Instance type_computational {σ} :
    TS.type_computational σ
    → TS.type_computational (t σ).
  Proof.
    move=> [ih]; constructor => ? ?; elim_clo.
    - move=> [A0 R] 𝒟 A1 //= A01.
      rewrite -roll.
      apply: Sig.init.
      apply: ih; eauto.
    - move=> ι A0 A0v R 𝒟 ℰ.
      destruct_has => ? //= ?;
      rewrite -roll; apply: Sig.conn; eauto.
      + constructor; eauto.
        move=> e0 e1 e01; destruct (H1 e0 e1); eauto.
        T.destruct_conjs.
        repeat split; eauto.
      + constructor; eauto.
        move=> e0 e1 e01; destruct (H1 e0 e1);
        T.destruct_conjs;
        repeat split; eauto.
      + constructor.
        Later.gather.
        eauto.
      + constructor.
        move=> κ.
        T.specialize_hyps.
        eauto.
  Qed.
End Clo.
