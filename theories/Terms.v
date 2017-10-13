From gctt Require Import Axioms.
Require Import Unicode.Utf8.

Set Implicit Arguments.

Module Tm.
  Inductive t (n : nat) :=
  | var : forall i, i < n -> t n
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

Inductive eval : Tm.t 0 → Tm.t 0 → Prop :=
| eval_prod : ∀ {A B}, eval (Tm.prod A B) (Tm.prod A B)
| eval_unit : eval Tm.unit Tm.unit
| eval_bool : eval Tm.bool Tm.bool
| eval_univ : ∀ {n}, eval (Tm.univ n) (Tm.univ n)
| eval_isect : ∀ {n}, eval (Tm.isect n) (Tm.isect n)
| eval_ltr : ∀ {A κ}, eval (Tm.ltr κ A) (Tm.ltr κ A)
| eval_tt : eval Tm.tt Tm.tt
| eval_ff : eval Tm.ff Tm.ff
| eval_pair : forall {e1 e2}, eval (Tm.pair e1 e2) (Tm.pair e1 e2)
| eval_ax : eval Tm.ax Tm.ax.

Notation "e ⇓ e'" := (eval e e') (at level 50).

Hint Resolve
     eval_prod
     eval_pair
     eval_unit
     eval_bool
     eval_univ
     eval_isect
     eval_tt
     eval_ff
     eval_ax
     eval_ltr.
