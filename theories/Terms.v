From gctt Require Import Axioms.
Require Import Unicode.Utf8.

Set Implicit Arguments.

Module Tm.
  Inductive t (n : nat) :=
  | var : forall i, i < n -> t n
  | ret : val n → t n
  | fst : t n -> t n
  | snd : t n → t n
  with val (n : nat) :=
  | unit : val n
  | bool : val n
  | ax : val n
  | tt : val n
  | ff : val n
  | prod : t n -> t n -> val n
  | arr : t n -> t n -> val n
  | pair : t n -> t n -> val n
  | ltr : CLK -> t n -> val n
  | isect : (CLK -> t n) -> val n
  | univ : nat -> val n.


  Arguments unit [n].
  Arguments bool [n].
  Arguments ax [n].
  Arguments tt [n].
  Arguments ff [n].
  Arguments univ [n] i.
End Tm.

Inductive eval : Tm.t 0 → Tm.val 0 → Prop :=
| eval_ret : ∀ {v}, eval (Tm.ret v) v
| eval_fst : ∀ {e e1 e2 v}, eval e (Tm.pair e1 e2) → eval e1 v → eval (Tm.fst e) v
| eval_snd : ∀ {e e1 e2 v}, eval e (Tm.pair e1 e2) → eval e2 v → eval (Tm.snd e) v.

Notation "e ⇓ e'" := (eval e e') (at level 50).

Hint Resolve eval_ret eval_fst eval_snd.


(* TODO *)
Axiom determinacy : ∀ A A0 A1, A ⇓ A0 → A ⇓ A1 → A0 = A1.