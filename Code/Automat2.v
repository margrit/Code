Require Import Arith.
Require Import Fin.
(*Require Import Ensembles.*)

Section definitions.

Variable A B: Set.

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
Inductive Finite_Set : nat -> Set :=
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
  mk_automat{
  states: Type;
  alphabet: Type;
  initial: states;
  final: list states;
  transitions: states -> alphabet -> list states
  }.

Definition testNEA : Automat := mk_automat (Finite_Set 2) (Finite_Set 2) 
                                (F1 1) ((FS 1 (F1 0))::nil) (fun x y => nil).

(* Finite_Set 2 steht für -- Warum 2 -- Anzahl der Zustände und Länge des Alphabets *)

Definition mk_NEA (s: nat) (a: nat) 
           (ini: (Finite_Set s)) 
           (final: (list (Finite_Set s))) 
           (trans : ((Finite_Set s) -> (Finite_Set a) -> (list (Finite_Set s)))) : 
           Automat := mk_automat (Finite_Set s) (Finite_Set a) ini final trans.  

(* Definition eines NEA, der nichts macht *)

Definition test2NEA : Automat := mk_NEA 3 4 (F1 2) nil (fun q x => nil).

(* Alternative Definitions eines DEAs *)

Record DAutomat: Type :=
  mk_dauto{
  dstates: Type;
  dalphabet: Type;
  dinit: dstates;
  dfinal: list dstates;
  dtrans: dstates -> dalphabet -> dstates
  }.

Definition mk_DEA (s : nat) (a : nat)
           (ini : (Finite_Set s))
           (final : (list(Finite_Set s)))
           (trans : ((Finite_Set s) -> (Finite_Set a) -> (Finite_Set s))):
           DAutomat := mk_dauto (Finite_Set s) (Finite_Set a) ini final trans.

(* optimierte Teilmengenkonstruktion
   - Umwandlung NEA => DEA 
   - nicht alle Zustände sind erreichbar
   - Epsilon-Hülle darstellen
   **
   - iterativ mit (d)trans zu konstruieren
   ** start : Q_0 := {qDEA} = {e-Hülle(q0)}
   ** go : Q_i+1 := Q_i union {dtrans(S,a)| S : Q (erreichbare Zustände), a : alphabet}
   ** stop := Q_i+1 = Q_i => Q_DEA := Q_i
*)

(* Startzustand und alle Zustände, die von dort aus
   durch Epsilon-Übergänge erreichet werden können 
   - brauch man ne Abbruchbedingung (unendlich viele E-Übergänge - eher nicht) 
*)
(*
Fixpoint start (s : nat) (QDEA : ) : Finite_Set := match QDEA with
               |ini => QDEA  
               end.
*)
Fixpoint go (s : nat) (a : nat) (QDEA : ) {Q_i+1 = Q_i} : Type := match ... with
               | init => QDEA
               | trans
               |
               end.


(* Definition Injektivitaet 
   - Elemente aus Menge A werden eindeutig, durch f, in Menge B abgebildet *)
Definition injective (f: A -> B) := forall x y : A, f x = f y -> x=y.

Definition surjective (f: A -> B) := forall y : B, exists x : A, f x =y.

Definition notInjective (f: A -> B) := exists x y : A, (f x = f y /\ (not (x = y))).

End definitions.
Section lemmas.

Lemma notInjImplNot_Inj : forall (A B : Set) (f : A -> B) , 
                          (notInjective A B f) -> (not (injective A B f)).
Proof.
  intros.
  unfold notInjective in H.
  unfold not.
  unfold injective.
  destruct H as [x H1].
  destruct H1 as [y P].
  destruct P as [Eqf Neq].
  intro.
  unfold not in Neq.
  elim Neq.
  apply H.
  trivial.
Qed.

(* notInjImplNot_Inj arbeitet auf Set und nicht auf Finite_Set *)

(* Lemma Not_InjImplNotInj1 : forall (A B : Set)(f : A -> B),
                           (not (injective A B f)) -> (notInjective A B f).
Proof.
  intros.
  unfold not in H.
  unfold notInjective.
  unfold injective in H.
  unfold not.
  induction H.
  intros.
*)  

(* Klassische vs. konstruktivistischer Logik
   - Welche Vorraussetzungen müssen noch getroffen werden um entscheidbar zu sein?
   - Die 2. Ricktung bekommt man hin, wenn man mehr Einschränkungen auf endliche Mengen
     definiert. 
   - Beide Varianten mal aufschreiben und sowohl die Hin- als auch die Rückrichtung 
     zeigen.
   - Wie geht man mit der doppelten Negation um?
*)


Lemma Not_InjImplNotInj : forall (n m : nat)  (f : (Finite_Set n) -> (Finite_Set m)) , 
                          (not (injective (Finite_Set n) (Finite_Set m) f)) 
                          -> (notInjective (Finite_Set n) (Finite_Set m) f).
Proof.
  intros.
  unfold notInjective.
  unfold not in H.
  unfold injective in H.
  induction n.
  elim H.
  intros.

(* z.z. dass Finite_Set 0 leer ist, dann müsste man weiter kommen.
   Zur Not ein Lemma mit aufnehmen, dass genau das zeigt. *)
  induction x.
  

(*x=y->fx=fy kann man mit f_equal oder injection zeigen. Problem, man kann nicht sagen 
ob f terminiert, daher geht es nicht so einfach anders herum. *)
  

Abort.



(*
Definition bijective (f: A -> B /\ g: B -> A) :=
  forall x y : A B, f x = f y /\ g x = g y -> x=y.
*)
(* Typ von A B: Set
   - Typ sollte noch angepasst werden
   - muss fuer Finite_Set und Finite_Sub gelten
*)

Inductive word : Set :=
  nil : word
| cons : word -> word -> word.

(* -- Tendenz induktive Definition --*)  
(*
Definition delta (a:Automat) :=
  match a with
  empty : states -> nil -> states
| word : states -> Word -> list states
  end.
*)

(* nicht klar, was Du hier genau willst, aber falls Du die Übergangsfunktion von
einem Automaten a haben willst, kannst Du die mit "transitions" bekommen, die Definition mit
"record" macht das...:*)

Check transitions.

(*
Definition Language_A : Type := 
  forall w: Word, 
  ex delta (initial,w) : Set -> Set.
*)


