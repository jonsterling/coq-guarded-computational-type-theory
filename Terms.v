Require Import Axioms.

Module Tm.
  Axiom t : Type.
  Axiom unit : t.
  Axiom bool : t.
  Axiom ax : t.
  Axiom tt : t.
  Axiom ff : t.
  Axiom pair : t -> t -> t.
  Axiom prod : t -> t -> t.
  Axiom ltr : CLK -> t -> t.
End Tm.

Axiom eval : Tm.t -> Tm.t -> Prop.
Notation "e ⇓ e'" := (eval e e') (at level 50).