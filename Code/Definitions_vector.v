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

Load Repeats_vector.
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

(* Erweiterte Uebergangsfunktion - delta_dach *)
Fixpoint delta_dach {n : nat} (q : Q) (v : Vector.t Sigma n) : Q :=
  match v with
    | nil _               => q
    | cons _ h _ v'  => delta_dach (delta q h) v'
  end.

(* Vorschlag zur Anpassung an VL-Notation: *)
Theorem delta_dach_append : forall {n m : nat}(xs : Vector.t Sigma n)(ys : Vector.t Sigma m)(q : Q),
  delta_dach q (append xs ys) = delta_dach (delta_dach q xs) ys.
Proof.
  induction xs.
  - simpl.
    intros ys q.
    reflexivity.
  - simpl.
    intros.
    apply IHxs.
Qed.

(* Definiert, wann ein Wort akzeptiert wird. *)
Definition accepted_word {n : nat}(w : Vector.t Sigma n) :=
  is_accepting (delta_dach q0 w).

End Definitions.
