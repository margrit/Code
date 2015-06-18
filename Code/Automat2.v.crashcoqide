Require Import Arith.
Require Import Fin.
(*Require Import Ensembles.*)

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
  states: Type;
  alphabet: Type;
  initial: states;
  final: list states;
  transitions: states -> alphabet -> list states
  }.


Definition testNEA : Automat := mk_auto (Finite_Set 2) (Finite_Set 2) (F1 1) ((FS 1 (F1 0))::nil) (fun x y => nil).

Definition mk_NEA (s: nat) (a: nat) (ini: (Finite_Set s)) (final: (list (Finite_Set s))) (trans : ((Finite_Set s) -> (Finite_Set a) -> (list (Finite_Set s)))) : Automat := mk_auto (Finite_Set s) (Finite_Set a) ini final trans.  

Definition test2NEA : Automat := mk_NEA 3 4 (F1 2) nil (fun q x => nil).



(* Definition Injektivitaet 
   - Elemente aus Menge A werden eindeutig, durch f, in Menge B abgebildet *)
Definition injective (f: A -> B) :=
  forall x y : A, f x = f y -> x=y.

Definition surjective (f: A -> B) :=
  forall y : B, exists x : A, f x =y.

Definition notInjective (f: A -> B) :=
  exists x y : A, (f x = f y /\ (not (x = y))).

Lemma lala : forall f : A -> B , (notInjective f) -> (not (injective f)).
Proof.
  intros.
  unfold not.
  intro.
  unfold notInjective in H.
  unfold injective in H0.
  elim H.
  intro.
  intro.
  elim H1.
  intro.
  elim H0 with x x0.
  intro.
  elim H2.
  intro.
  intro.
  elim H4.
  reflexivity.
Abort.  



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

