Require Import Unicode.Utf8.
Require Import Coq.Vectors.Vector.
From gctt Require Import Terms.
From gctt Require Import Axioms.

Set Implicit Arguments.

Module FTm.
  Inductive clk l :=
  | cref : ∀ k, k < l → clk l.

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
  | ltr : clk l → t l n -> t l n
  | isect : t (S l) n -> t l n
  | univ : nat -> t l n.
End FTm.

Definition Env := Vector.t CLK.


Definition interp_clk {l : nat} (k : FTm.clk l) (ρ : Env l) : CLK :=
  match k with
  | FTm.cref _ p => Vector.nth_order ρ p
  end.

Reserved Notation "⟦ e ⟧ ρ" (at level 50).
Notation "K⟦ k ⟧ ρ" := (interp_clk k ρ) (at level 50).
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
  | FTm.ltr ref A => Tm.ltr (K⟦ref⟧ ρ) (⟦A⟧ ρ)
  | FTm.isect A => Tm.isect (fun κ => ⟦A⟧ (κ ∷ ρ))
  | FTm.univ i => Tm.univ i
  end
where "⟦ e ⟧ ρ" := (interp e ρ).