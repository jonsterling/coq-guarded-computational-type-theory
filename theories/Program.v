Require Import Unicode.Utf8 Program.
Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

From ctt Require Import Notation Axioms Var.
From ctt Require Tactic.
Module T := Tactic.


Set Implicit Arguments.
Delimit Scope prog_scope with prog.
Delimit Scope subst_scope with subst.

Module Prog.
  Inductive t (Ψ : Ctx) :=
  | var : Var Ψ -> t Ψ
  | fst : t Ψ -> t Ψ
  | snd : t Ψ → t Ψ
  | app : t Ψ → t Ψ → t Ψ
  | kapp : t Ψ → 𝕂 → t Ψ
  | void : t Ψ
  | unit : t Ψ
  | bool : t Ψ
  | ax : t Ψ
  | tt : t Ψ
  | ff : t Ψ
  | prod : t Ψ -> t (S Ψ) -> t Ψ
  | arr : t Ψ -> t (S Ψ) -> t Ψ
  | pair : t Ψ -> t Ψ -> t Ψ
  | lam : t (S Ψ) → t Ψ
  | klam : (𝕂 → t Ψ) → t Ψ
  | ltr : 𝕂 -> t Ψ -> t Ψ
  | isect : (𝕂 → t Ψ) → t Ψ
  | karr : (𝕂 → t Ψ) → t Ψ
  | univ : nat -> t Ψ
  | fix_ : t (S Ψ) → t Ψ.

  Arguments void [Ψ].
  Arguments unit [Ψ].
  Arguments bool [Ψ].
  Arguments ax [Ψ].
  Arguments tt [Ψ].
  Arguments ff [Ψ].
  Arguments univ [Ψ] i.


  Module Notations.
    Notation "@0" := (var Fin.F1) : prog_scope.
    Notation "@1" := (var (Fin.FS Fin.F1)) : prog_scope.
    Notation "▶[ κ ] A" := (ltr κ A%prog) (at level 50) : prog_scope.
    Notation "'𝟚'" := bool : prog_scope.
    Notation "'𝟙'" := unit : prog_scope.
    Notation "'𝟘'" := void : prog_scope.
    Notation "★" := ax : prog_scope.
    Notation "M .1" := (fst M%prog) (at level 50) : prog_scope.
    Notation "M .2" := (snd M%prog) (at level 50) : prog_scope.
    Infix "×" := prod : prog_scope.
    Infix "⇒" := arr (at level 30) : prog_scope.
    Notation "⋂[ κ ] A" := (isect (fun κ => A%prog)) (at level 50) : prog_scope.
    Notation "⋂ A" := (isect A) (at level 50) : prog_scope.
    Notation "𝕌[ i ] " := (univ i%nat) : prog_scope.
    Notation "⟨ M1 , M2 ⟩" := (pair M1%prog M2%prog) : prog_scope.
    Notation "M1 ⋅ M2" := (app M1%prog M2%prog) (at level 50) : prog_scope.
    Notation "'𝛌{' M }" := (lam M%prog) (at level 50) : prog_scope.
    Notation "'𝛍{' M }" := (fix_ M%prog) (at level 50) : prog_scope.
  End Notations.

  Import Notations.

  Program Fixpoint map {Ψ1 Ψ2} (ρ : Ren.t Ψ1 Ψ2) (M : t Ψ1) : t Ψ2 :=
    match M with
    | var i => var (ρ i)
    | fst M => fst (map ρ M)
    | snd M => snd (map ρ M)
    | app M1 M2 => app (map ρ M1) (map ρ M2)
    | kapp M κ => kapp (map ρ M) κ
    | unit => unit
    | void => void
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (map ρ A) (map (Ren.cong ρ) B)
    | arr A B => arr (map ρ A) (map (Ren.cong ρ) B)
    | pair M1 M2 => pair (map ρ M1) (map ρ M2)
    | lam M => lam (map (Ren.cong ρ) M)
    | klam M => klam (fun κ => map ρ (M κ))
    | ltr κ A => ltr κ (map ρ A)
    | isect A => isect (fun κ => map ρ (A κ))
    | karr A => karr (fun κ => map ρ (A κ))
    | univ i => univ i
    | fix_ M => fix_ (map (Ren.cong ρ) M)
    end.


  Local Ltac rewrites_aux :=
    repeat f_equal;
    try (let x := fresh in T.eqcd => x);
    try (rewrite Ren.cong_id).

  Local Ltac rewrites :=
    T.rewrites_with rewrites_aux.


  Theorem map_id {Ψ} (M : t Ψ) : map id M = M.
  Proof.
    induction M; by rewrites.
  Qed.

  Program Instance syn_struct_term : Sub.syn_struct t :=
    {| Sub.var := var;
       Sub.map := @map |}.
  Next Obligation.
    apply: map_id.
  Qed.

  Module RenNotation.
    Notation "M .[ ρ ]" := (map ρ%ren M) (at level 50) : prog_scope.
  End RenNotation.

  Import RenNotation.

  Program Fixpoint subst {Ψ1 Ψ2} (σ : Sub.t Ψ1 Ψ2) (M : t Ψ1) : t Ψ2 :=
    match M with
    | var i => σ i
    | fst M => fst (subst σ M)
    | snd M => snd (subst σ M)
    | app M1 M2 => app (subst σ M1) (subst σ M2)
    | kapp M κ => kapp (subst σ M) κ
    | void => void
    | unit => unit
    | bool => bool
    | ax => ax
    | tt => tt
    | ff => ff
    | prod A B => prod (subst σ A) (subst (Sub.cong σ) B)
    | arr A B => arr (subst σ A) (subst (Sub.cong σ) B)
    | pair M1 M2 => pair (subst σ M1) (subst σ M2)
    | lam M => lam (subst (Sub.cong σ) M)
    | klam M => klam (fun κ => subst σ (M κ))
    | ltr κ A => ltr κ (subst σ A)
    | isect A => isect (fun κ => subst σ (A κ))
    | karr A => karr (fun κ => subst σ (A κ))
    | univ i => univ i
    | fix_ M => fix_ (subst (Sub.cong σ) M)
    end.

  Module SubstNotation.
    Notation "M ⫽ σ" := (subst σ%subst M%prog) (at level 20, left associativity) : prog_scope.
    Notation "σ' ◎ σ" := (subst σ'%subst ∘ σ%subst) (at level 50) : subst_scope.
  End SubstNotation.

  Import SubstNotation.

  (* TODO: make this part of the syntax-structure type class *)
  Theorem ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) (M : t _) :
    M.[ρ12].[ρ23]%prog
    =
    M.[ρ23 ∘ ρ12]%prog.
  Proof.
    move: Ψ2 Ψ3 ρ12 ρ23.
    induction M; rewrites;
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

  Local Open Scope prog_scope.

  Theorem ren_subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (ρ23 : Ren.t Ψ2 Ψ3) M :
    (M ⫽ σ12).[ρ23]
    =
    (M ⫽ (map ρ23 ∘ σ12)).
  Proof.
    move: Ψ2 Ψ3 σ12 ρ23.
    induction M; rewrites;
    by rewrite -ren_subst_cong_coh.
  Qed.

  Theorem subst_ren_coh {Ψ1 Ψ2 Ψ3} (ρ12 : Ren.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) M :
    M.[ρ12] ⫽ σ23
    =
    M ⫽ (σ23 ∘ ρ12).
  Proof.
    move: Ψ2 Ψ3 ρ12 σ23.
    induction M; rewrites;
    f_equal; f_equal;
    by dependent destruction H.
  Qed.

  Theorem subst_coh {Ψ1 Ψ2 Ψ3} (σ12 : Sub.t Ψ1 Ψ2) (σ23 : Sub.t Ψ2 Ψ3) (M : t _) :
    M ⫽ σ12 ⫽ σ23
    =
    M ⫽ (σ23 ◎ σ12).
  Proof.
    move: Ψ2 Ψ3 σ12 σ23.
    rewrite /compose.
    induction M; rewrites;
    dependent induction H; auto; simpl;
    by rewrite ren_subst_coh subst_ren_coh.
  Qed.


  Lemma cong_id {Ψ} : Sub.cong (@var Ψ) = @var (S Ψ).
  Proof.
    T.eqcd => x.
    dependent destruction x; auto.
  Qed.

  Theorem subst_ret {Ψ} M :
    M ⫽ (@var Ψ) = M.
  Proof.
    induction M; rewrites;
    by rewrite cong_id.
  Qed.

  Theorem subst_closed (σ : Sub.t 0 0) (M : t 0) :
    M ⫽ σ = M.
  Proof.
    rewrite -{2}(subst_ret M).
    f_equal.
    T.eqcd => x.
    dependent destruction x.
  Qed.

End Prog.

Export Prog.Notations Prog.RenNotation Prog.SubstNotation.

Hint Rewrite @Prog.subst_ren_coh @Prog.ren_subst_coh @Prog.subst_coh @Prog.subst_closed : syn_db.
Hint Unfold compose : syn_db.

Ltac simplify_subst_step :=
  simpl; autorewrite with syn_db; autounfold with syn_db.

Ltac simplify_subst :=
  repeat (simplify_eqs; f_equal; try T.eqcd; intros; simplify_subst_step).
