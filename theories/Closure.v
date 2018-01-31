Require Import Unicode.Utf8 Program.Equality Logic.FunctionalExtensionality Classes.Morphisms Coq.omega.Omega.
From ctt Require Import Notation OrderTheory Axioms Var Program OpSem TypeSystem.
From ctt Require Tactic.
Module T := Tactic.

Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Module Connective.
  Inductive ctor := void | unit | bool | prod | arr | later | isect.

  Inductive void_el : rel :=.

  Inductive unit_val : rel :=
  | ax : unit_val (Prog.ax, Prog.ax).

  Inductive bool_val : rel :=
  | tt : bool_val (Prog.tt, Prog.tt)
  | ff : bool_val (Prog.ff, Prog.ff).

  Inductive prod_el (R0 : rel) (R1 : Prog.t 0 → rel) : rel :=
  | proj :
      ∀ M0 M1,
        R0 (Prog.fst M0, Prog.fst M1)
        → R1 (Prog.fst M0) (Prog.snd M0, Prog.snd M1)
        → prod_el R0 R1 (M0, M1).

  (* negative definition of pi type *)
  Inductive fun_el (R0 : rel) (R1 : Prog.t 0 → rel) : rel :=
  | app :
      ∀ f0 f1,
        (∀ M0 M1,
            R0 (M0, M1)
            → R1 M0 ((f0 ⋅ M0)%prog, (f1 ⋅ M1)%prog))
        → fun_el R0 R1 (f0, f1).

  Inductive cext (R : rel) : rel :=
  | mk_cext :
      ∀ M0 M1 v0 v1,
        M0 ⇓ v0
        → M1 ⇓ v1
        → R (v0, v1)
        → cext R (M0, M1).

  Module CExtNotation.
    Notation "[ R ]⇓" := (cext R).
  End CExtNotation.

  Import CExtNotation.

  Inductive has (τ : cts) : ctor → Prog.t 0 × rel → Ω :=
  | has_void : has τ void (Prog.void, void_el)
  | has_unit : has τ unit (Prog.unit, [unit_val]⇓)
  | has_bool : has τ bool (Prog.bool, [bool_val]⇓)
  | has_prod :
      ∀ A0 A1 R0 R1,
        τ (A0, R0)
        → (∀ M0 M1,
              R0 (M0, M1)
              → τ ((A1 ⫽ Sub.inst0 M0)%prog, R1 M0)
                ∧ τ ((A1 ⫽ Sub.inst0 M0)%prog, R1 M1)
                ∧ τ ((A1 ⫽ Sub.inst0 M1)%prog, R1 M1)
                ∧ τ ((A1 ⫽ Sub.inst0 M1)%prog, R1 M0))
        → has τ prod (Prog.prod A0 A1, prod_el R0 R1)
  | has_arr :
      ∀ A0 A1 R0 R1,
        τ (A0, R0)
        → (∀ M0 M1,
              R0 (M0, M1)
              → τ ((A1 ⫽ Sub.inst0 M0)%prog, R1 M0)
                ∧ τ ((A1 ⫽ Sub.inst0 M0)%prog, R1 M1)
                ∧ τ ((A1 ⫽ Sub.inst0 M1)%prog, R1 M1)
                ∧ τ ((A1 ⫽ Sub.inst0 M1)%prog, R1 M0))
        → has τ arr (Prog.arr A0 A1, fun_el R0 R1)

  | has_later :
      ∀ κ B R,
        ▷[κ] (τ (B, R))
        → has τ later (Prog.ltr κ B, fun M0M1 => ▷[κ] (R M0M1))
  | has_isect :
      ∀ B S,
        (∀ κ, τ (B κ, S κ))
        → has τ isect (Prog.isect B, fun M0M1 => ∀ κ, S κ M0M1).

  Hint Constructors has cext prod_el bool_val unit_val.

  Local Hint Resolve Later.map.
  Theorem monotone : ∀ ι, Proper (Poset.order ==> Poset.order) (fun τ => has τ ι).
  Proof.
    move=> ι τ0 τ1 τ01 [A R] H.
    dependent destruction H;
    try by [eauto].

    constructor.
    + auto.
    + move=> M0 M1 M0M1.
      edestruct H0; eauto.
      T.destruct_conjs.
      repeat split; eauto.
    + constructor; eauto.
      move=> M0 M1 M0M1.
      edestruct H0; eauto;
      T.destruct_conjs;
      repeat split; eauto.
  Qed.

  Hint Resolve monotone.

  Ltac destruct_cext :=
    match goal with
    | H : [_]⇓ _ |- _ => dependent destruction H
    end.
End Connective.

Export Connective.CExtNotation.

Module Sig.
  (* For each refinement cts σ, we define a monotone map on
       refinement matrices which adds the appropriate
       types/rels. *)
  Inductive t (σ τ : cts) : (Prog.t 0 × rel) → Ω :=
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
    T.split => [X | X]; [rewrite /t|].
    - rewrite -LFP.roll; eauto.
    - rewrite LFP.roll; eauto.
  Qed.

  Lemma map_has {σ ρ ι A R} :
    ρ ⊑ σ
    → Connective.has ρ ι (A, R)
    → Connective.has σ ι (A, R).
  Proof.
    move=> sub has.
    dependent destruction has; eauto.
    - constructor; eauto.
      move=> M0 M1 M01.
      edestruct H0; T.destruct_conjs; repeat split; eauto.
    - constructor; eauto.
      move=> M0 M1 M01.
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
    → A ⇓ Prog.univ i
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

      + T.eqcd; case => M0 M1; apply: propositional_extensionality; split => M0M1.
        * dependent destruction M0M1.
          constructor.
          ** replace R2 with R0; eauto.
          ** replace (R3 (M0 .1)%prog) with (R1 (M0 .1)%prog); eauto.
             destruct (H0 (M0.1)%prog (M1.1)%prog) as [H01 [H02 [H03 H04]]]; auto.
             replace R2 with R0 in H3; eauto.
             destruct (H3 (M0.1)%prog (M1.1)%prog); eauto.
        * dependent destruction M0M1.
          constructor.
          ** replace R0 with R2; auto.
             symmetry; eauto.
          ** replace (R1 (M0.1)%prog) with (R3 (M0.1)%prog); eauto.
             destruct (H0 (M0.1)%prog (M1.1)%prog) as [H01 [H02 [H03 H04]]]; eauto.
             *** replace R0 with R2; eauto.
                 symmetry; eauto.
             *** symmetry.
                 apply: H01; eauto.
                 destruct (H3 (M0.1)%prog (M1.1)%prog); eauto.
      + T.eqcd; case => f0 f1; apply: propositional_extensionality; split => f0f1.
        * dependent destruction f0f1.
          constructor => M0 M1 M0M1.
          replace (R3 M0) with (R1 M0).
          ** apply: H1.
             replace R0 with R2; auto.
             symmetry.
             apply: H; auto.
          ** edestruct H0; eauto.
             *** replace R0 with R2; eauto.
                 symmetry; apply: H; eauto.
             *** edestruct H3; eauto.
        * dependent destruction f0f1.
          constructor => M0 M1 M0M1.
          replace (R1 M0) with (R3 M0).
          ** apply: H1.
             replace R2 with R0; auto.
          ** edestruct H0; eauto.
             *** edestruct H3; eauto.
                 **** replace R2 with R0; eauto.
                 **** T.destruct_conjs; symmetry; auto.

      + do ? (T.eqcd; moves).
        Later.gather => *; T.destruct_conjs.
        rewrite_functionality_ih; eauto.
      + do ? (T.eqcd; moves).
        T.specialize_hyps.
        rewrite_functionality_ih; eauto.
  Qed.

  Theorem cext_per {R} :
    is_per R
    → is_per [R]⇓.
  Proof.
    move=> [ihSm ihTr].
    constructor.
    - move=> M0 M1 H1.
      dependent destruction H1.
      econstructor; eauto.
    - move=> M0 M1 M2 H1 H2.
      dependent destruction H1.
      dependent destruction H2.
      OpSem.evals_to_eq.
      T.destruct_eqs.
      econstructor; eauto.
  Qed.

  Theorem unit_val_per : is_per Connective.unit_val.
  Proof.
    constructor.
    - move=> M0 M1 H1.
      by dependent destruction H1.
    - move=> ? ? ? H1 H2.
      by [dependent destruction H1;
          dependent destruction H2].
  Qed.

  Theorem bool_val_per : is_per Connective.bool_val.
  Proof.
    constructor.
    - move=> M0 M1 H1.
      by dependent destruction H1.
    - move=> ? ? ? H1 H2.
      by [dependent destruction H1;
          dependent destruction H2].
  Qed.

  Theorem cext_computational {R} :
    rel_computational [R]⇓.
  Proof.
    move=> M0 M1 M2 M01 cext.
    Connective.destruct_cext.
    econstructor; eauto.
  Qed.

  Hint Resolve cext_per cext_computational unit_val_per bool_val_per cext_per.
  Hint Constructors is_cper.

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
        apply: map_has; last by eauto.
        move=> ? [? ?] //=.

      + destruct_has; simpl in *; try by [constructor; eauto]; cleanup.
        * constructor.
          ** constructor.
             *** move=> M0 M1 M01.
                 dependent destruction M01.
                 constructor.
                 **** apply: symmetric; auto.
                      apply: per; by destruct H.
                 **** replace (R1 (M1.1)%prog) with (R1 (M0.1)%prog);
                      edestruct H0; T.destruct_conjs; eauto.
                      ***** apply: symmetric; auto.
                            by apply: per.
                      ***** apply: (TS.is_extensional (t σ)); eauto.

             *** move=> M0 M1 M2 M01 M12.
                 dependent destruction M01.
                 dependent destruction M12.
                 destruct H.
                 constructor.

                 **** apply: transitive; eauto.
                      edestruct H0; eauto.
                      T.destruct_conjs.
                      by apply: per.
                 **** replace (R1 (M1.1)%prog) with (R1 (M0.1)%prog) in H4.
                      ***** apply: transitive; eauto.
                            edestruct (H0 (M0.1)%prog); eauto.
                            T.destruct_conjs.
                            by apply: per.
                      ***** edestruct (H0 (M0.1)%prog); eauto.
                            T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.

          ** move=> M0 M1 M2 M0M1 el.
             dependent destruction el.
             destruct H.
             constructor.
             *** apply: crel; first by [auto]; last by eauto.
                 by apply: fst_cong_approx.
             *** replace (R1 (M1.1)%prog) with (R1 (M0.1)%prog).
                 **** apply: crel; last by eauto.
                      ***** edestruct H0; eauto; T.destruct_conjs; eauto.
                      ***** by apply: snd_cong_approx.
                 **** edestruct (H0 (M1.1)%prog (M0.1)%prog); eauto.
                      ***** suff H4: R0 ((M0.1)%prog, (M0.1)%prog).
                            ****** apply: crel; [auto|apply: fst_cong_approx M0M1|eauto].
                            ****** apply: transitive; first by [apply: per].
                            ******* eauto.
                            ******* apply: symmetric; first by [apply: per]; eauto.
                      ***** T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.


        * destruct H.
          constructor.
          ** constructor.
             *** move=> f0 f1 f01.
                 dependent destruction f01.
                 constructor=> M0 M1 M01.
                 destruct H.
                 apply: symmetric; auto.
                 **** edestruct H0; T.destruct_conjs; eauto.
                      by apply: per.
                 **** replace (R1 M0) with (R1 M1).
                      ***** apply: H2; auto.
                            apply: symmetric; auto.
                            apply: per; auto.
                      ***** edestruct H0; eauto.
                            T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.
             *** move=> f0 f1 f2 f01 f12.
                 dependent destruction f01.
                 dependent destruction f12.
                 constructor=> M0 M1 M01.
                 apply: transitive.
                 **** edestruct H0; eauto.
                      T.destruct_conjs.
                      by apply: per.
                 **** apply: H2.
                      eauto.
                 **** replace (R1 M0) with (R1 M1).
                      ***** apply: H3; eauto.
                            apply: transitive; first by [apply: per]; eauto.
                            apply: symmetric; first by [apply: per]; eauto.
                      ***** edestruct H0; eauto.
                            T.destruct_conjs.
                            apply: (TS.is_extensional (t σ)); eauto.
          ** move=> f0 f1 f2 f01 H2.
             dependent destruction H2.
             constructor.
             move=> M0 M1 M0M1.
             apply: crel.
             *** edestruct H0; eauto; T.destruct_conjs; eauto.
             *** apply: app_cong_approx; exact f01.
             *** apply: H2; auto.

        * constructor.
          ** constructor.
             *** move=> M0 M1 H1.
                 Later.gather.
                 move=> //= [[ihR0 ?] M0M1].
                 apply: symmetric; eauto; apply: per; eauto.

             *** move=> M0 M1 M2 H1 H2.
                 Later.gather.
                 move=> //= [[? ?] [M0M1 M1M2]].
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
                 apply: symmetric; auto.
                 by apply: per.
             *** move=> ? ? ? ? ? ?.
                 T.specialize_hyps.
                 case: H => //= [? ?].
                 apply: transitive; eauto.
                 by apply: per.
          ** move=> ? ? ? ? ?  ?.
             T.specialize_hyps.
             T.destruct_conjs.
             apply: crel; eauto.
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
        move=> M0 M1 M01; destruct (H1 M0 M1); eauto.
        T.destruct_conjs.
        repeat split; eauto.
      + constructor; eauto.
        move=> M0 M1 M01; destruct (H1 M0 M1);
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
