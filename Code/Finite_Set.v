(* -- Definition einer endlichen Menge aus der User Distribution -- 
   http://www.lix.polytechnique.fr/coq/V8.2pl1/contribs/Automata.Ensf_types.html#
   -- mit Elt = Elem --
*)

(*
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
*)

(* Definition endliche Menge *)
Inductive Finite_Set : nat -> Set :=
  F1 : forall n, Finite_Set (S n)
| FS : forall n, Finite_Set n -> Finite_Set (S n).

(*
Axiom states_size: forall l: list Q, length l > Q_size ->
  repeats l.
*)