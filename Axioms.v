Axiom CLK : Type.

Module Later.
  Axiom t : CLK -> Prop -> Prop.
  Axiom map : forall κ (p q : Prop), (p -> q) -> (t κ p -> t κ q).
End Later.

Notation "▷[ κ ] ϕ" := (Later.t κ ϕ) (at level 0).
