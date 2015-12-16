(* -- Definition einer endlichen Menge aus der User Distribution -- 
   http://www.lix.polytechnique.fr/coq/V8.2pl1/contribs/Automata.Ensf_types.html#
   -- mit Elt = Elem --
*)


Inductive Finite_Set : Set :=
| empty : Finite_Set
| add : Elem -> Finite_Set -> Finite_Set
with Elem : Set :=
| natural : nat -> Elem
| couple : Elem -> Elem -> Elem
| up : Finite_Set -> Elem
| word : Word -> Elem
with Word : Set :=
| nil : Word
| cons : Elem -> Word -> Word.

(* Definition endliche Menge *)
Inductive Finite_Set_1 : nat -> Set :=
  F1 : forall n, Finite_Set_1 (S n)
| FS : forall n, Finite_Set_1 n -> Finite_Set_1 (S n).

Parameter A : Finite_Set.
Parameter B : Finite_Set.
Print A.

Definition abb A B := A -> B.
Print abb.

(*
Axiom states_size: forall l: list Q, length l > Q_size ->
  repeats l.
*)