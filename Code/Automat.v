Require Import Arith.
Require Import Fin.
Require Import Ensembles.

Parameters A B: Set.

(*Definition t: Q -> Q.
Proof.
intros.
assumption.
Qed.*)

(* -- Definition einer endlichen Menge aus der User Distribution -- 
   http://www.lix.polytechnique.fr/coq/V8.2pl1/contribs/Automata.Ensf_types.html#
   -- mit Elt = Elem --
*)

(*
Inductive FinSet : Set :=
| empty : FinSet
| add : Elem -> FinSet -> FinSet
with Elem : Set :=
| natural : nat -> Elem
| couple : Elem -> Elem -> Elem
| up : FinSet -> Elem
| word : Word -> Elem
with Word : Set :=
| nil : Word
| cons : Elem -> Word -> Word.
*)


(* Definition endliche Menge *)
Inductive Finite_Set : nat -> Type :=
  F1 : forall n, Finite_Set (S n)
| FS : forall n, Finite_Set n -> Finite_Set (S n).

(* Definition Injektivitaet aus Fin
--!!!-- Problem Match x mit n --!!!--

Definition FS_injective : forall (n : nat) (x y : t n),
  FS x = FS y -> x=y.
*)

(*
Inductive Automat: Type :=
   states : Set
  | actions : Set
  | initial : states
  | final : Set
  | transitions : states -> actions -> list states.
*)

(* Automat allgemein *)
(* http://stackoverflow.com/questions/22475373/modelisation-of-an-automaton-with-coq *)
Record Automat: Type :=
  mk_auto{
  states: Set;
  actions: Set;
  initial: states;
  final: Set;
  transitions: states -> actions -> list states
  }.

(* Definition Injektivitaet 
   - Elemente aus Menge A werden eindeutig, durch f, in Menge B abgebildet *)
Definition injective (f: A -> B) :=
  forall x y : A, f x = f y -> x=y.

Definition surjective (f: B -> A) :=
  forall x y : B, f x = f y -> x=y.

(*
Definition bijective (f: A -> B /\ g: B -> A) :=
  forall x y : A B, f x = f y /\ g x = g y -> x=y.
*)
(* Typ von A B: Set
   - Typ sollte noch angepasst werden
   - muss fuer Finite_Set und Finite_Sub gelten
*)

Inductive Word :=
  nil : Word
| cons : Set -> Word -> Word.

(* -- Tendenz induktive Definition --*)  
Definition delta (a:Automat) :=
  match a with
  empty : states -> nil -> states
| word : states -> Word -> list states
  end.


Definition Language_A : Type := 
  forall w: Word, 
  ex delta (initial,w) : Set -> Set.

