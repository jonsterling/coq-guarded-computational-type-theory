Require Import Unicode.Utf8 Program.Tactics Logic.FunctionalExtensionality Classes.Morphisms.

Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From ctt Require Import Axioms.


Notation "'℘' A" := (A -> Prop) (at level 10).

(* Order-theory stuff drawn from Pichardie and Cachera, but partly
 rewritten by me to use ssreflect and just use native equality. *)

Module Poset.
  Class t A : Type :=
    { order : A -> A -> Prop;
      refl : ∀ x y,  x = y -> order x y;
      antisym : ∀ x y, order x y -> order y x -> x = y;
      trans : ∀ x y z, order x y -> order y z -> order x z
    }.
End Poset.

Notation "x ⊑ y" := (Poset.order x y) (at level 40).

Module CompleteLattice.
  Class t (A:Type) : Type :=
    { porder :> Poset.t A;
      join : ℘ A -> A;
      join_bound : forall x (f : ℘ A), f x -> x ⊑ join f;
      join_lub : forall (f : ℘ A) z, (∀ x, f x -> x ⊑ z) -> join f ⊑ z
    }.

  Definition subset_meet A {L:t A} (S:℘ A) : ℘ A :=
    fun a => ∀x:A, S x -> a ⊑ x.

  Definition meet {A} {L:t A} (S:℘ A) : A := join (subset_meet A S).

  Lemma meet_bound : forall A (L:t A), ∀x:A, ∀f:℘ A, f x -> (meet f) ⊑ x.
  Proof.
    firstorder.
    apply: join_lub.
    firstorder.
  Qed.

  Lemma meet_glb : forall A (L:t A), ∀f:℘ A, ∀z, (∀ x, f x -> z ⊑ x) -> z ⊑ meet f.
  Proof.
    firstorder;
    by [apply: join_bound].
  Qed.
End CompleteLattice.

Hint Resolve
     @Equivalence_Reflexive @Equivalence_Symmetric @Equivalence_Transitive
     @Poset.refl @Poset.antisym @Poset.trans
     @CompleteLattice.join_bound @CompleteLattice.join_lub
     @CompleteLattice.meet_bound @CompleteLattice.meet_glb.

Program Instance PowerSetPoset A : Poset.t (℘ A) :=
  {| Poset.order := fun P Q => ∀ x, (P x -> Q x) |}.

Solve Obligations with firstorder.
Next Obligation.
  apply: functional_extensionality.
  move=> z.
  apply: propositional_extensionality.
  split; eauto.
Qed.


Program Instance PowerSetCompleteLattice A : CompleteLattice.t (℘ A) :=
  {| CompleteLattice.porder := PowerSetPoset _;
     CompleteLattice.join :=  (fun Q => fun x => exists y, Q y /\ y x)
  |}.

Solve Obligations with firstorder.


Class Monotone {A} `{P : CompleteLattice.t A} (f : A → A) :=
  { mono_proper : Proper (Poset.order ==> Poset.order) f }.

Module LFP.
  Section LFP.
    Context {L : Type} `{CL : CompleteLattice.t L} (f : L → L) `{Mf : Monotone L f}.

    Definition postfix : ℘ L :=
      fun a => (f a) ⊑ a.

    Definition t : L := CompleteLattice.meet postfix.

    Theorem roll : f t = t.
    Proof.
      have into : f t ⊑ t.
      + apply: CompleteLattice.meet_glb.
        move=> x PF.
        apply: (Poset.trans _ (f x));
        rewrite /t; auto.
        apply: mono_proper; auto.
      + apply: Poset.antisym; auto; rewrite /t.
        apply: CompleteLattice.meet_bound.
        by [apply: mono_proper].
    Qed.
  End LFP.
End LFP.