Require Import Unicode.Utf8.
Require Import Coq.Program.Tactics.
Require Import Coq.Setoids.Setoid.
Require Import Classes.SetoidClass.
Require Import Classes.Morphisms.
From mathcomp Require Import ssreflect.

Print Setoid.
Print Equivalence.
Set Bullet Behavior "Strict Subproofs".

(* Order-theory stuff drawn from Pichardie and Cachera, but partly
 rewritten by me to use ssreflect and setoids.*)

Print Basics.
Module Poset.
  Class t A : Type :=
    { eq :> Setoid A;
      order : A -> A -> Prop;
      order_proper : Proper (equiv ==> (equiv ==> iff)) order;
      refl : ∀ x y,  x==y -> order x y;
      antisym : ∀ x y, order x y -> order y x -> x == y;
      trans : ∀ x y z, order x y -> order y z -> order x z
    }.
End Poset.

Notation "x ⊑ y" := (Poset.order x y) (at level 40).

Class subset A `{Setoid A} : Type :=
  { carrier : A -> Prop;
    subset_comp_eq : ∀ x y:A, x == y -> carrier x -> carrier y
  }.
Coercion carrier : subset >-> Funclass.

Module CompleteLattice.
  Class t (A:Type) : Type :=
    { porder :> Poset.t A;
      join : subset A -> A;
      join_bound : forall x (f : subset A), f x -> x ⊑ join f;
      join_lub : forall (f : subset A) z, (∀ x, f x -> x ⊑ z) -> join f ⊑ z
    }.

  Program Definition subset_meet A {L:t A} (S:subset A) : subset A :=
    {| carrier := fun a => ∀x:A, S x -> a ⊑ x |}.
  Next Obligation.
    apply: Poset.trans; last eauto.
    apply: Poset.refl.
      by [symmetry].
  Defined.


  Definition meet {A} {L:t A} (S:subset A) : A := join (subset_meet A S).

  Lemma meet_bound : forall A (L:t A), ∀x:A, ∀f:subset A, f x -> (meet f) ⊑ x.
  Proof.
    firstorder.
    apply: join_lub.
    firstorder.
  Qed.

  Lemma meet_glb : forall A (L:t A), ∀f:subset A, ∀z, (∀ x, f x -> z ⊑ x) -> z ⊑ meet f.
  Proof.
    firstorder;
      by [apply: join_bound].
  Qed.
End CompleteLattice.

Print Equivalence.
Hint Resolve
     @Equivalence_Reflexive @Equivalence_Symmetric @Equivalence_Transitive
     @Poset.refl @Poset.antisym @Poset.trans
     @CompleteLattice.join_bound @CompleteLattice.join_lub
     @CompleteLattice.meet_bound @CompleteLattice.meet_glb.

Notation "'℘' A" := (A -> Prop) (at level 10).

Program Instance PowerSetSetoid A : Setoid (℘ A) :=
  {| equiv := fun P Q => ∀ x, (P x <-> Q x) |}.

Solve Obligations with firstorder.

Program Instance PowerSetPoset A : Poset.t (℘ A) :=
  {| Poset.order := fun P Q => ∀ x, (P x -> Q x) |}.

Solve Obligations with firstorder.


Program Instance PowerSetCompleteLattice A : CompleteLattice.t (℘ A) :=
  {| CompleteLattice.porder := PowerSetPoset _;
     CompleteLattice.join :=  (fun Q => fun x => exists y, Q y /\ y x)
  |}.

Solve Obligations with firstorder.



Class monotone A `{Poset.t A} B `{Poset.t B} : Type :=
  { mon_func : A -> B;
    mon_prop : ∀ a1 a2, a1 ⊑ a2 -> (mon_func a1) ⊑ (mon_func a2)
  }.

Coercion mon_func : monotone >-> Funclass.
Hint Resolve @mon_prop.
Coercion mon_prop : monotone >-> Funclass.
Arguments Build_monotone [A H B H0].


Program Definition PostFix {L P} `(f:@monotone L P L P) : subset L :=
  {| carrier := (fun a:L => (f a) ⊑ a) |}.
Next Obligation.
  apply: (Poset.trans _ x); eauto.
  apply: (Poset.trans _ (f x)).
  + eauto.
    apply: mon_prop.
    apply: Poset.refl.
    symmetry.
    auto.
  + auto.
Defined.

Definition lfp {L} `{CompleteLattice.t L} (f:monotone L L) : L :=
  CompleteLattice.meet (PostFix f).

Section KnasterTarski.
  Context {L : Type} `{CompleteLattice.t L}.
  Variable f : monotone L L.

  Lemma lfp_fixed_point : f (lfp f) == lfp f.
  Proof.
    have into : f (lfp f) ⊑ lfp f.
    + apply: CompleteLattice.meet_glb.
      move=> x PF.
      apply: (Poset.trans _ (f x));
        rewrite /lfp; auto.
    + apply: Poset.antisym; auto; rewrite /lfp.
      apply: CompleteLattice.meet_bound.
        by [apply: mon_prop].
  Qed.
End KnasterTarski.