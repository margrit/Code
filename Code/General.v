Require Import Decidable.

(* Entscheidbarkeit auf Typenlevel*)
Definition decT (T : Type) : Type := T + ( T -> False).

Definition eq_dec (T : Type) : Type := forall (x y :T), decidable (x = y).
Eval compute in ( eq_dec nat).
