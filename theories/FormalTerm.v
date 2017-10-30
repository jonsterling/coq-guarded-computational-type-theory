Require Import Unicode.Utf8.

Set Implicit Arguments.

Module FTm.
  Inductive t (l n : nat) :=
  | var : forall i, i < n -> t l n
  | fst : t l n -> t l n
  | snd : t l n → t l n
  | unit : t l n
  | bool : t l n
  | ax : t l n
  | tt : t l n
  | ff : t l n
  | prod : t l n -> t l n -> t l n
  | arr : t l n -> t l n -> t l n
  | pair : t l n -> t l n -> t l n
  | ltr : ∀ k, k < l → t l n -> t l n
  | isect : t (S l) n -> t l n
  | univ : nat -> t l n.
End FTm.
