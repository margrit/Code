(*Aus Dfa.v*)
(*
 * Die Basis Komponenten eines Automaten. 
 *)

(* Require Import String. *)

Load Repeats.
Load Finite_Set.
Require Import Fin.

(* Q, Sigma, Q_size waren als Variablen erst angegeben und dann zu Parametern geändert. *)
(* Typen der Zustaende *)
Parameter Q : Finite_Set.
Print Q.

(* Anzahl der moeglichen Zustaende *)
Parameter Q_size : nat.

(* Der Typ des Alphabets und dessen Symbole *)
Parameter Sigma: Finite_Set.

(* zum Testen...: Let Sigma := string. *)

(* Die Transitionsfunktion - delta *)
Definition q := Q -> Sigma -> Q.

(* Funktion die entscheidet, ob ein Zustand ein akzeptierender Zustand ist *)
Parameter is_accepting: Q -> Prop.

(* Startzustand *)
Variable q0 : Q.

(* Um zu definieren, wann ein Wort akzeptiert wird, muessen noch 
einige Vorueberlegungen getroffen werden. Hierzu braucht man die 
erweiterte Transitionsfunktion ext.
accepted_word (w: list Sigma) := is_accepting (ext q0 w). *)

(* Keine Verwendung von Axiomen. *)
Axiom states_size: forall l: list Q, length l > Q_size ->
  repeats l.

(* Erweiterte Transitionsfunktion - ext *)
Fixpoint ext (q: Q) (l: list Sigma) : Q :=
  match l with
  | nil => q
  | h :: t => ext (d q h) t
  end.

Theorem ext_app: forall xs ys: list Sigma, forall q: Q,
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
Definition accepted_word (w: list Sigma) :=
  is_accepting (ext q0 w).