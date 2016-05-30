(*Aus Dfa.v*)
(*
 * Die Basis Komponenten eines Automaten. 
 *)

(* Require Import String. *)
Load Repeats.
Load Finite_Set.
Require Import Fin.
Require Import Arith.

(* Q, Sigma, Q_size waren als Variablen erst angegeben und dann zu Parametern geändert. *)
(* Typen der Zustaende *)
(* Anzahl der moeglichen Zustaende *)
Parameter Q_size : nat.
Definition Q := Finite_Set Q_size.
Print Q.

(* Der Typ des Alphabets und dessen Symbole *)
Parameter S_size : nat.
Definition Sigma := Finite_Set S_size.
Print Sigma.

(* zum Testen...: Let Sigma := string. *)

(* Die Transitionsfunktion - delta *)
Parameter delta : Q -> Sigma -> Q.
Print delta.

(* Funktion die entscheidet, ob ein Zustand ein akzeptierender Zustand ist *)
Parameter is_accepting : Q -> Prop.
Print is_accepting.

(* Startzustand *)
Parameter q0 : Q.
Print q0.

(* Um zu definieren, wann ein Wort akzeptiert wird, muessen noch 
einige Vorueberlegungen getroffen werden. Hierzu braucht man die 
erweiterte Transitionsfunktion ext.
accepted_word (w : list Sigma) := is_accepting (ext q0 w). *)

(* Erweiterte Transitionsfunktion - ext *)
Fixpoint ext (q : Q) (l : list Sigma) : Q :=
  match l with
    | nil     => q
    | h :: t  => ext (delta q h) t
  end.

Theorem ext_app : forall xs ys : list Sigma, forall q : Q,
  ext q (xs ++ ys) = ext (ext q xs) ys.
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
Definition accepted_word (w : list Sigma) :=
  is_accepting (ext q0 w).
Print accepted_word.
