From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import Unicode.Utf8.
Require Import Coq.Vectors.Vector.
Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
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

  Program Fixpoint weak (l1 l2 : nat) (x : Fin.t l1) : Fin.t (l1 + l2) :=
    match l2 with
    | 0 => x
    | S n => weak n (Fin.FS x)
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

  Program Definition kwkTm {l n} (e : t l n) : t (S l) n :=
    map (weak 1) e.
  Next Obligation.
    omega.
  Defined.

End FTm.

Definition Env := Vector.t CLK.

Reserved Notation "⟦ e ⟧ ρ" (at level 50).
Notation "κ ∷ ρ" := (Vector.cons _ κ _ ρ) (at level 30).

Print Vector.t.

Fixpoint interp {l n : nat} (e : FTm.t l n) (ρ : Env l) : Tm.t n :=
  match e with
  | FTm.var i p => Tm.var p
  | FTm.fst e => Tm.fst (⟦e⟧ ρ)
  | FTm.snd e => Tm.snd (⟦e⟧ ρ)
  | FTm.unit => Tm.unit
  | FTm.bool => Tm.bool
  | FTm.ax => Tm.ax
  | FTm.tt => Tm.tt
  | FTm.ff => Tm.ff
  | FTm.prod A B => Tm.prod (⟦A⟧ ρ) (⟦B⟧ ρ)
  | FTm.arr A B => Tm.arr (⟦A⟧ ρ) (⟦B⟧ ρ)
  | FTm.pair A B => Tm.pair (⟦A⟧ ρ) (⟦B⟧ ρ)
  | FTm.ltr r A => Tm.ltr (nth ρ r) (⟦A⟧ ρ)
  | FTm.isect A => Tm.isect (fun κ => ⟦A⟧ (κ ∷ ρ))
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
      ∀ (ρ : Env l),
        ⊧ ⟦ A ⟧ ρ ∼ ⟦ B ⟧ ρ
    end.

  Notation "⟦ n ∣ J ⟧" := (@meaning n J) (at level 50).

  Theorem welp : ∀ n m : nat, S (n + m) = n + S m.
    move=> n m.
    induction n; simpl; auto.
  Defined.
  Print welp.

  Program Fixpoint insert_at {l} (ρ : Env l) (i : Fin.t l) (κ : CLK) : Env (S l) :=
    match i with
    | Fin.F1 _ => κ ∷ ρ
    | Fin.FS _ j =>
      match ρ with
      | nil => _
      | κ' ∷ ρ' => κ' ∷ insert_at ρ' j κ
      end
    end.

  (* TODO *)
  Axiom interp_clk_wk :
    ∀ l n (e : FTm.t l n) (ρ : Env l) (κ : CLK),
      ⟦ e ⟧ ρ = ⟦ FTm.kwkTm e ⟧ (κ ∷ ρ).


  Theorem test3 :
    ∀ (l : nat) (A : FTm.t l 0),
      ⟦ l ∣ eq_ty A A ⟧
      → ⟦ l ∣ eq_ty A (FTm.isect (FTm.kwkTm A)) ⟧.
  Proof.
    move=> l A D ρ.
    simpl.
    have : (λ κ : CLK, ⟦ FTm.kwkTm A ⟧ κ ∷ ρ) = (fun κ => ⟦A⟧ ρ).
    + T.eqcd => κ.
      by [rewrite -interp_clk_wk].
    + move=> Q.
      rewrite Q.
      simpl.
      apply: ClosedRules.isect_irrelevance.
      simpl in D.
      specialize (D ρ).
      case: D => R [D1 D2].
      eauto.
  Qed.

End Jdg.