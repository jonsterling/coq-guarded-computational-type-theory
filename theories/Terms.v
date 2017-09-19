From gctt Require Import Axioms.

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


Axiom eval : Tm.t 0 -> Tm.t 0 -> Prop.
Notation "e ⇓ e'" := (eval e e') (at level 50).

Axiom eval_prod : forall {A B}, Tm.prod A B ⇓ Tm.prod A B.
Axiom eval_unit : Tm.unit ⇓ Tm.unit.
Axiom eval_univ : forall {n}, Tm.univ n ⇓ Tm.univ n.
Axiom eval_isect : forall {A}, Tm.isect A ⇓ Tm.isect A.
Hint Resolve eval_prod eval_unit eval_univ eval_isect.
