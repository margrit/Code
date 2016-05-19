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
Parameter delta : Q -> Sigma -> list Q.

(* Funktion die entscheidet, ob ein Zustand ein akzeptierender Zustand ist *)
Parameter is_accepting : Q -> bool.

(* Startzustand *)
Parameter q0 : Q.

(* Um zu definieren, wann ein Wort akzeptiert wird, muessen noch 
einige Vorueberlegungen getroffen werden. Hierzu braucht man die 
erweiterte Transitionsfunktion delta_dach. *)
Print cons.
Print Power_set.

(* Erweiterte Überführungsfunktion - delta_dach *)
Fixpoint delta_hat (q : Q) (word : list Sigma) : list Q :=
  match word with
    | nil                   => q
    | cons h word1 => delta_hat (delta q h) word1
  end.

(* Definiert, wann ein Wort akzeptiert wird. *)
Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_hat q0 w).

(* Typ der Konfigurationen eines DFA, Konf_DFA = Q x Sigma* *)
Definition Konf_DFA := Q * (list Sigma) : Type.
Print Konf_DFA.
Print cons.
Print fst.

(* Konfigurationsübergangsrelation *)

Inductive Konf_DFA_step : Konf_DFA -> Konf_DFA -> Type :=
 | sowarsgedacht : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma) (eq : (delta q a) = p), 
                                    Konf_DFA_step (q, (cons a w)) (p, w).

(* Tip: Das wird die reflexiv-transitive
Hülle von Konf_rel_DFA_Schritt, Du brauchst also 3 Konstruktoren (einen
für "Konf_rel_DFA_Schritt ist drin", einen für "ist reflexiv" und
einen für "ist transitiv"...
*)

Inductive Konf_rel_DFA : Konf_DFA -> Konf_DFA -> Type :=
  | refl    : forall (K : Konf_DFA), Konf_rel_DFA K K
  | step  : forall (K L M : Konf_DFA),
                                    Konf_rel_DFA K L ->
                                    Konf_DFA_step L M ->
                                    Konf_rel_DFA K M.

End Definitions.
