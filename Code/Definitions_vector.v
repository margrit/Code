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

(* Require Import String. *)
Load Repeats_vector.
(* Load Finite_Set. *)
Require Import Fin.
Require Import Arith.

Section Definitions.

(* Q, Sigma, Q_size waren als Variablen erst angegeben und dann zu Parametern geändert. *)
(* Typen der Zustaende *)
(* Anzahl der moeglichen Zustaende *)
Parameter Q_size : nat.
Definition Q := @Fin.t Q_size.
Print Q.

(* Der Typ des Alphabets und dessen Symbole *)
Parameter S_size : nat.
Definition Sigma := @Fin.t S_size.
Print Sigma.

(* zum Testen...: Let Sigma := string. *)

(* Die Transitionsfunktion - delta *)
Parameter delta : Q -> Sigma -> Q.
Print delta.

(* Funktion die entscheidet, ob ein Zustand ein akzeptierender Zustand ist *)
Parameter is_accepting : Q -> Type.
Print is_accepting.

(* Startzustand *)
Parameter q0 : Q.
Print q0.

(* Um zu definieren, wann ein Wort akzeptiert wird, muessen noch 
einige Vorueberlegungen getroffen werden. Hierzu braucht man die 
erweiterte Transitionsfunktion ext.
accepted_word (w : list Sigma) := is_accepting (ext q0 w). *)

(* Erweiterte Uebergangsfunktion - delta_hat *)
Fixpoint delta_hat {n : nat} (q : Q) (v : Vector.t Sigma n) : Q :=
  match v with
    | nil _           => q
    | cons _ h _ v'   => delta_hat (delta q h) v'
  end.
Print delta_hat.

(* Vorschlag zur Anpassung an VL-Notation: *)
Theorem delta_hat_append : forall {n m : nat}(xs : Vector.t Sigma n)(ys : Vector.t Sigma m)(q : Q),
  delta_hat q (append xs ys) = delta_hat (delta_hat q xs) ys.
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
  is_accepting (delta_hat q0 w).
Print accepted_word.

End Definitions.
