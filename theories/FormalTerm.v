From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.

From gctt Require Import Terms.
From gctt Require Import Axioms.
From gctt Require Import GCTT.


Set Implicit Arguments.

Module FTm.
  Inductive t (l n : nat) :=
  | var : forall i, i < n -> t l n
  | fst : t l n -> t l n
  | snd : t l n → t l n
  | unit : t l n
  | bool : t l n
  | ax : t l n
  | tt : t l n
  | ff : t l n
  | prod : t l n -> t l n -> t l n
  | arr : t l n -> t l n -> t l n
  | pair : t l n -> t l n -> t l n
  | ltr : Fin.t l → t l n -> t l n
  | isect : t (S l) n -> t l n
  | univ : nat -> t l n.

  Arguments unit [l n].
  Arguments bool [l n].
  Arguments ax [l n].
  Arguments tt [l n].
  Arguments ff [l n].
  Arguments univ [l n] i.

  Definition Ren (l1 l2 : nat) : Type :=
    Fin.t l1 → Fin.t l2.

  Program Definition wkr (l1 l2 : nat) (ρ : Ren l1 l2) : Ren (S l1) (S l2) :=
    fun x =>
      match x with
      | Fin.F1 _ => Fin.F1
      | Fin.FS _ y => Fin.FS (ρ y)
      end.

  Program Fixpoint weak (l1 l2 : nat) : Ren l1 (l2 + l1) :=
    match l2 with
    | 0 => fun x => x
    | S n => fun x => weak n (Fin.FS x)
    end.

  Program Fixpoint map {l1 l2 n} (ρ : Ren l1 l2) (e : t l1 n) : t l2 n :=
    match e with
    | var i p => @var l2 n i p
    | fst e => fst (map ρ e)
    | snd e => snd (map ρ e)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρ A) (map ρ B)
    | arr A B => arr (map ρ A) (map ρ B)
    | pair e1 e2 => pair (map ρ e1) (map ρ e2)
    | ltr k A => ltr (ρ k) (map ρ A)
    | isect A => isect (map (wkr ρ) A)
    | univ i => univ i
    end.
End FTm.

Definition Env l := Fin.t l → CLK.

Program Definition cons {l} (κ : CLK) (σ : Env l) : Env (S l) :=
  fun x =>
    match x with
    | Fin.F1 _ => κ
    | Fin.FS _ x => σ x
    end.

Reserved Notation "⟦ e ⟧ σ" (at level 50).
Notation "κ ∷ σ" := (cons κ σ) (at level 30).

Fixpoint interp {l n : nat} (e : FTm.t l n) (σ : Env l) : Tm.t n :=
  match e with
  | FTm.var i p => Tm.var p
  | FTm.fst e => Tm.fst (⟦e⟧ σ)
  | FTm.snd e => Tm.snd (⟦e⟧ σ)
  | FTm.unit => Tm.unit
  | FTm.bool => Tm.bool
  | FTm.ax => Tm.ax
  | FTm.tt => Tm.tt
  | FTm.ff => Tm.ff
  | FTm.prod A B => Tm.prod (⟦A⟧ σ) (⟦B⟧ σ)
  | FTm.arr A B => Tm.arr (⟦A⟧ σ) (⟦B⟧ σ)
  | FTm.pair A B => Tm.pair (⟦A⟧ σ) (⟦B⟧ σ)
  | FTm.ltr r A => Tm.ltr (σ r) (⟦A⟧ σ)
  | FTm.isect A => Tm.isect (fun κ => ⟦A⟧ (κ ∷ σ))
  | FTm.univ i => Tm.univ i
  end
where "⟦ e ⟧ ρ" := (interp e ρ).

Module Jdg.
  Inductive atomic l n :=
  | eq_ty : FTm.t l n → FTm.t l n → atomic l n.

  Reserved Notation "J⟦ J ⟧" (at level 50).

  Import Univ.

  Definition meaning (l : nat) (J : atomic l 0) : Prop :=
    match J with
    | eq_ty A B =>
      ∀ (σ : Env l),
        ⊧ ⟦ A ⟧ σ ∼ ⟦ B ⟧ σ
    end.

  Notation "⟦ n ∣ J ⟧" := (@meaning n J) (at level 50).


  Ltac rewrite_all_hyps :=
    repeat
      match goal with
      | x : _ |- _ => rewrite -x
      end.

  Local Open Scope program_scope.

  Theorem interp_naturality :
    ∀ l1 l2 n (e : FTm.t l1 n) (ρ : FTm.Ren l1 l2) (σ : Env l2),
      ⟦ e ⟧ σ ∘ ρ = ⟦ FTm.map ρ e ⟧ σ.
  Proof.
    move=> l1 l2 n e; move: l2.
    elim e => *; eauto; simpl;
    try by [rewrite_all_hyps].

    + f_equal; T.eqcd => κ.
      rewrite_all_hyps.
      f_equal; T.eqcd => i; rewrite /cons.
      by dependent induction i.
  Qed.

  Program Definition interp_clk_wk l n (e : FTm.t l n) (σ : Env l) (κ : CLK) :
    ⟦ e ⟧ σ = ⟦ FTm.map (FTm.weak 1) e ⟧ (κ ∷ σ)
    := interp_naturality e (FTm.weak 1) (κ ∷ σ).
  Next Obligation.
    by simplify_eqs.
  Qed.

  Ltac rewrite_ :=
    let x := fresh in
    move=> x; rewrite x; clear x.

  Theorem test3 :
    ∀ (l : nat) (A : FTm.t l 0),
      ⟦ l ∣ eq_ty A A ⟧
      → ⟦ l ∣ eq_ty A (FTm.isect (FTm.map (FTm.weak 1) A)) ⟧.
  Proof.
    move=> l A D ρ //=.
    have : (λ κ : CLK, ⟦ FTm.map (FTm.weak 1) A ⟧ κ ∷ ρ) = (fun κ => ⟦A⟧ ρ).
    + T.eqcd => *.
      by [rewrite -interp_clk_wk].
    + rewrite_; apply: ClosedRules.isect_irrelevance.
      case: (D ρ) => ? [? ?];
      eauto.
  Qed.

End Jdg.