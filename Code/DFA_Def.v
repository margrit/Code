(* Grundsaetzliche Anpassungen: 

   - Benutzung des Fin.t aus der Standard Library 
   - Nicht mit Prop arbeiten sondern mit Type

*)

(* Vorschlag: Hier ein kurzes Notationsverzeichnis, das in der 
   coqdoc-Dokumentation erscheinen koennte? 
   Und die konkreten Definitionen aus den VL-Folien dann jeweils an der Stelle, 
   wo das entsprechende Konzept implementiert wird? *)


(*Aus Dfa.v*)
(*
 * Die Basis Komponenten eines Automaten. 
 *)

Require Import Fin.
Require Import Arith.


Section Definitions.

(* Anzahl der moeglichen Zustaende *)
Parameter Q_size : nat.

(* Typ der Zustaende *)
Definition Q := @Fin.t Q_size.

(* Anzahl der Elemente des Eingabealphabets *)
Parameter S_size : nat.

(* Typ des Eingabealphabets *)
Definition Sigma := @Fin.t S_size.

(* Die Transitionsfunktion - delta *)
Parameter delta : Q -> Sigma -> Q.

(* Funktion die entscheidet, ob ein Zustand ein akzeptierender Zustand ist *)
Parameter is_accepting : Q -> bool.

(* Startzustand *)
Parameter q0 : Q.

(* Um zu definieren, wann ein Wort akzeptiert wird, muessen noch 
einige Vorueberlegungen getroffen werden. Hierzu braucht man die 
erweiterte Transitionsfunktion delta_dach. *)
Print cons.
(* Erweiterte Überführungsfunktion - delta_dach *)
Fixpoint delta_dach (q : Q) (wort : list Sigma) : Q :=
  match wort with
    | nil                  => q
    | cons h wort1 => delta_dach (delta q h) wort1
  end.

(* Definiert, wann ein Wort akzeptiert wird. *)
Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_dach q0 w).

(* Typ der Konfigurationen eines DFA, Konf_DFA = Q x Sigma* *)
Definition Konf_DFA := Q * (list Sigma) : Type.
Print Konf_DFA.

(* Konfigurationsübergangsrelation *)
(* brauchen boolsche Gleichheit über Q *)
Parameter eq_Q : Q -> Q -> bool.

Inductive Konf_rel_DFA_Schritt (x : Konf_DFA) (y : Konf_DFA) : Type :=
  | irgendwie : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma), Konf_rel_DFA_Schritt (q, a w) -> (p w).

End Definitions.
