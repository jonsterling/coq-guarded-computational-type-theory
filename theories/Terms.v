From gctt Require Import Axioms.
Require Import Unicode.Utf8.
Require Import Fin.

Set Implicit Arguments.

Module Tm.
  Inductive t (n : nat) :=
  | var : Fin.t n -> t n
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


Reserved Notation "e 'val'" (at level 50).
Reserved Notation "e ⇓ e'" (at level 50).

Inductive is_val : Tm.t 0 → Prop :=
| val_bool : Tm.bool val
| val_unit : Tm.unit val
| val_prod : ∀ {e1 e2}, Tm.prod e1 e2 val
| val_arr : ∀ {e1 e2}, Tm.arr e1 e2 val
| val_ltr : ∀ {κ e}, Tm.ltr κ e val
| val_isect : ∀ {e}, Tm.isect e val
| val_univ : ∀ {i}, Tm.univ i val
| val_ax : Tm.ax val
| val_tt : Tm.tt val
| val_ff : Tm.ff val
| val_pair : ∀ {e1 e2}, Tm.pair e1 e2 val
where "v 'val'" := (is_val v).

Inductive eval : Tm.t 0 → Tm.t 0 → Prop :=
| eval_val :
    ∀ {v},
      v val
      → v ⇓ v

| eval_fst :
    ∀ {e e1 e2 v},
      e ⇓ Tm.pair e1 e2
      → e1 ⇓ v
      → Tm.fst e ⇓ v

| eval_snd :
    ∀ {e e1 e2 v},
      e ⇓ Tm.pair e1 e2
      → e2 ⇓ v
      → Tm.snd e ⇓ v

where "e ⇓ e'" := (eval e e').


Hint Constructors is_val.
Hint Constructors eval.


(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.