From gctt Require Import Axioms.
Require Import Unicode.Utf8.

Set Implicit Arguments.

Module Tm.
  Inductive t (n : nat) :=
  | var : forall i, i < n -> t n
  | fst : t n -> t n
  | snd : t n → t n
  | unit : t n
  | bool : t n
  | ax : t n
  | tt : t n
  | ff : t n
  | prod : t n -> t n -> t n
  | arr : t n -> t n -> t n
  | pair : t n -> t n -> t n
  | ltr : CLK -> t n -> t n
  | isect : (CLK -> t n) -> t n
  | univ : nat -> t n.

  Arguments unit [n].
  Arguments bool [n].
  Arguments ax [n].
  Arguments tt [n].
  Arguments ff [n].
  Arguments univ [n] i.
End Tm.

Inductive val : Tm.t 0 → Prop :=
| val_bool : val Tm.bool
| val_unit : val Tm.unit
| val_prod : ∀ {e1 e2}, val (Tm.prod e1 e2)
| val_arr : ∀ {e1 e2}, val (Tm.arr e1 e2)
| val_ltr : ∀ {κ e}, val (Tm.ltr κ e)
| val_isect : ∀ {e}, val (Tm.isect e)
| val_univ : ∀ {i}, val (Tm.univ i)
| val_ax : val Tm.ax
| val_tt : val Tm.tt
| val_ff : val Tm.ff
| val_pair : ∀ {e1 e2}, val (Tm.pair e1 e2).

Inductive eval : Tm.t 0 → Tm.t 0 → Prop :=
| eval_val : ∀ {v}, val v → eval v v
| eval_fst : ∀ {e e1 e2 v}, eval e (Tm.pair e1 e2) → eval e1 v → eval (Tm.fst e) v
| eval_snd : ∀ {e e1 e2 v}, eval e (Tm.pair e1 e2) → eval e2 v → eval (Tm.snd e) v.

Notation "e ⇓ e'" := (eval e e') (at level 50).

Hint Constructors val.
Hint Constructors eval.


(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.