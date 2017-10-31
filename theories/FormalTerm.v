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


  Fixpoint liftVar n (x : Fin.t n) : Fin.t (pred n) -> Fin.t n :=
    match x with
    | Fin.F1 _ => fun y => Fin.FS y
    | Fin.FS _ x' => fun y =>
                    match y in Fin.t n' return Fin.t n' -> (Fin.t (pred n') -> Fin.t n')
                                             -> Fin.t (S n') with
                    | Fin.F1 _ => fun x' _ => Fin.F1
                    | Fin.FS _ y' => fun _ fx' => Fin.FS (fx' y')
                    end x' (liftVar x')
    end.

  Fixpoint liftFin n (x : Fin.t n) : Fin.t (pred n) -> Fin.t n :=
    match x with
    | Fin.F1 _ => fun y => Fin.FS y
    | Fin.FS _ x' =>
      fun y =>
        match y in Fin.t n' return Fin.t n' -> (Fin.t (pred n') -> Fin.t n') -> Fin.t (S n') with
        | Fin.F1 _ => fun x' _ => Fin.F1
        | Fin.FS _ y' => fun _ fx' => Fin.FS (fx' y')
        end x' (liftFin x')
    end.

  Fixpoint kliftTm {l n} (e : t l n) (k : Fin.t (S l)) : t (S l) n :=
    match e with
    | var _ p => var _ p
    | fst e => fst (kliftTm e k)
    | snd e => snd (kliftTm e k)
    | unit => unit _ _
    | bool => bool _ _
    | ax => ax _ _
    | tt => tt _ _
    | ff => ff _ _
    | prod a b => prod (kliftTm a k) (kliftTm b k)
    | arr a b => arr (kliftTm a k) (kliftTm b k)
    | pair a b => pair (kliftTm a k) (kliftTm b k)
    | ltr k' a => ltr (liftVar k k') (kliftTm a k)
    | isect a => isect (kliftTm a (Fin.FS k))
    | univ i => univ _ _ i
    end.

  Definition kwkTm {l n} (e : t l n) : t (S l) n :=
    kliftTm e Fin.F1.
End FTm.

Definition Env := Vector.t CLK.

Reserved Notation "⟦ e ⟧ ρ" (at level 50).
Notation "κ ∷ ρ" := (Vector.cons _ κ _ ρ) (at level 30).

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

  Lemma test :
    ∀ l n (e : FTm.t l n) (ρ : Env (S l)),
      ⟦ FTm.isect (FTm.kwkTm (FTm.ltr Fin.F1 (FTm.tt _ n))) ⟧ ρ
      =
      Tm.isect (fun κ => Tm.ltr (nth ρ Fin.F1) Tm.tt).
  Proof.
    move=> l n e ρ.
    simpl.
    auto.
  Qed.


  (* This should be true, just a little gnarly to prove. *)
  Lemma interp_clk_wk :
    ∀ l n (e : FTm.t l n) (ρ : Env l) (κ : CLK),
      ⟦ e ⟧ ρ = ⟦ FTm.kwkTm e ⟧ (κ ∷ ρ).
  Proof.
  Admitted.


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