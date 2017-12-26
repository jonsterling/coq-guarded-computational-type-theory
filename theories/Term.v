Require Import Unicode.Utf8 Program.
From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From gctt Require Import Notation Axioms Var.
From gctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.
Delimit Scope tm_scope with tm.
Delimit Scope subst_scope with subst.

Module Tm.
  Inductive t (Ψ : Ctx) :=
  | var : Var Ψ -> t Ψ
  | fst : t Ψ -> t Ψ
  | snd : t Ψ → t Ψ
  | app : t Ψ → t Ψ → t Ψ
  | unit : t Ψ
  | bool : t Ψ
  | ax : t Ψ
  | tt : t Ψ
  | ff : t Ψ
  | prod : t Ψ -> t (S Ψ) -> t Ψ
  | arr : t Ψ -> t (S Ψ) -> t Ψ
  | pair : t Ψ -> t Ψ -> t Ψ
  | lam : t (S Ψ) → t Ψ
  | ltr : 𝕂 -> t Ψ -> t Ψ
  | isect : (𝕂 → t Ψ) → t Ψ
  | univ : nat -> t Ψ
  | fix_ : t (S Ψ) → t Ψ.

  Arguments unit [Ψ].
  Arguments bool [Ψ].
  Arguments ax [Ψ].
  Arguments tt [Ψ].
  Arguments ff [Ψ].
  Arguments univ [Ψ] i.


  Module Notations.
    Notation "@0" := (Tm.var Fin.F1) : tm_scope.
    Notation "@1" := (Tm.var (Fin.FS Fin.F1)) : tm_scope.
    Notation "▶[ κ ] A" := (Tm.ltr κ A%tm) (at level 50) : tm_scope.
    Notation "'𝟚'" := Tm.bool : tm_scope.
    Notation "'𝟙'" := Tm.unit : tm_scope.
    Notation "★" := Tm.ax : tm_scope.
    Notation "e .1" := (Tm.fst e%tm) (at level 50) : tm_scope.
    Notation "e .2" := (Tm.snd e%tm) (at level 50) : tm_scope.
    Infix "×" := Tm.prod : tm_scope.
    Infix "⇒" := Tm.arr (at level 30) : tm_scope.
    Notation "⋂[ κ ] A" := (Tm.isect (fun κ => A%tm)) (at level 50) : tm_scope.
    Notation "⋂ A" := (Tm.isect A) (at level 50) : tm_scope.
    Notation "𝕌[ i ] " := (Tm.univ i%nat) : tm_scope.
    Notation "⟨ e1 , e2 ⟩" := (Tm.pair e1%tm e2%tm) : tm_scope.
    Notation "e1 ⋅ e2" := (Tm.app e1%tm e2%tm) (at level 50) : tm_scope.
    Notation "'𝛌{' e }" := (Tm.lam e%tm) (at level 50) : tm_scope.
    Notation "'𝛍{' e }" := (Tm.fix_ e%tm) (at level 50) : tm_scope.
  End Notations.

  Import Notations.

  Program Fixpoint map {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => var (ρ i)
    | fst e => fst (map ρ e)
    | snd e => snd (map ρ e)
    | app e1 e2 => app (map ρ e1) (map ρ e2)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρ A) (map (Ren.cong ρ) B)
    | arr A B => arr (map ρ A) (map (Ren.cong ρ) B)
    | pair e1 e2 => pair (map ρ e1) (map ρ e2)
    | lam e => lam (map (Ren.cong ρ) e)
    | ltr κ A => ltr κ (map ρ A)
    | isect A => isect (fun κ => map ρ (A κ))
    | univ i => univ i
    | fix_ e => fix_ (map (Ren.cong ρ) e)
    end.


  Local Ltac rewrites_aux :=
    repeat f_equal;
    try (let x := fresh in T.eqcd => x);
    try (rewrite Ren.cong_id).

  Local Ltac rewrites :=
    T.rewrites_with rewrites_aux.


  Theorem map_id {Ψ} (e : t Ψ) : map id e = e.
  Proof.
    induction e; by rewrites.
  Qed.

  Program Instance syn_struct_term : Sub.syn_struct t :=
    {| Sub.var := var;
       Sub.map := @map |}.
  Next Obligation.
    apply: map_id.
  Qed.

  Module RenNotation.
    Notation "e .[ ρ ]" := (Tm.map ρ%ren e) (at level 50) : tm_scope.
  End RenNotation.

  Import RenNotation.

  Program Fixpoint subst {Ψ1 Ψ2} (σ : Sub.t Ψ1 Ψ2) (e : t Ψ1) : t Ψ2 :=
    match e with
    | var i => σ i
    | fst e => fst (subst σ e)
    | snd e => snd (subst σ e)
    | app e1 e2 => app (subst σ e1) (subst σ e2)
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst (Sub.cong σ) B)
    | arr A B => arr (subst σ A) (subst (Sub.cong σ) B)
    | pair e1 e2 => pair (subst σ e1) (subst σ e2)
    | lam e => lam (subst (Sub.cong σ) e)
    | ltr κ A => ltr κ (subst σ A)
    | isect A => isect (fun κ => subst σ (A κ))
    | univ i => univ i
    | fix_ e => fix_ (subst (Sub.cong σ) e)
    end.

  Module SubstNotation.
    Notation "e ⫽ σ" := (Tm.subst σ%subst e%tm) (at level 20, left associativity) : tm_scope.
    Notation "σ' ◎ σ" := (Tm.subst σ'%subst ∘ σ%subst) (at level 50) : subst_scope.
  End SubstNotation.

  Import SubstNotation.

  (* TODO: make this part of the syntax-structure type class *)
  Theorem ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) (e : t _) :
    e.[ρ12].[ρ23]%tm
    =
    e.[ρ23 ∘ ρ12]%tm.
  Proof.
    move: Ψ2 Ψ3 ρ12 ρ23.
    induction e; rewrites;
    by dependent induction H.
  Qed.

  (* TODO: derive this generally for any syntax *)
  Theorem ren_subst_cong_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) :
    map (Ren.cong ρ23) ∘ Sub.cong σ12
    =
    Sub.cong (map ρ23 ∘ σ12).
  Proof.
    T.eqcd => x; rewrite /compose; move: Ψ2 Ψ3 σ12 ρ23.
    dependent destruction x;
    T.rewrites_with ltac:(try rewrite ren_coh).
  Qed.

  Local Open Scope tm_scope.

  Theorem ren_subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) e :
    (e ⫽ σ12).[ρ23]
    =
    (e ⫽ (map ρ23 ∘ σ12)).
  Proof.
    move: Ψ2 Ψ3 σ12 ρ23.
    induction e; rewrites;
    by rewrite -ren_subst_cong_coh.
  Qed.

  Theorem subst_ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) e :
    e.[ρ12] ⫽ σ23
    =
    e ⫽ (σ23 ∘ ρ12).
  Proof.
    move: Ψ2 Ψ3 ρ12 σ23.
    induction e; rewrites;
    f_equal; f_equal;
    by dependent destruction H.
  Qed.

  Theorem subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) (e : t _) :
    e ⫽ σ12 ⫽ σ23
    =
    e ⫽ (subst σ23 ∘ σ12).
  Proof.
    move: Ψ2 Ψ3 σ12 σ23.
    rewrite /compose.
    induction e; rewrites;
    dependent induction H; auto; simpl;
    by rewrite ren_subst_coh subst_ren_coh.
  Qed.


  Lemma cong_id {Ψ} : Sub.cong (@var Ψ) = @var (S Ψ).
  Proof.
    T.eqcd => x.
    dependent destruction x; auto.
  Qed.

  Theorem subst_ret {Ψ} e :
    e ⫽ (@var Ψ) = e.
  Proof.
    induction e; rewrites;
    by rewrite cong_id.
  Qed.

  Theorem subst_closed (σ : Sub.t 0 0) (e : t 0) :
    e ⫽ σ = e.
  Proof.
    rewrite -{2}(subst_ret e).
    f_equal.
    T.eqcd => x.
    dependent destruction x.
  Qed.

End Tm.

Export Tm.Notations Tm.RenNotation Tm.SubstNotation.

Hint Rewrite @Tm.subst_ren_coh @Tm.ren_subst_coh @Tm.subst_coh @Tm.subst_closed : syn_db.
Hint Unfold compose : syn_db.

Ltac simplify_subst_step :=
  simpl; autorewrite with syn_db; autounfold with syn_db.

Ltac simplify_subst :=
  repeat (simplify_eqs; f_equal; try T.eqcd; intros; simplify_subst_step).
