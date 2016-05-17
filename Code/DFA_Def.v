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
erweiterte Transitionsfunktion delta_hat. *)
Print cons.
(* Erweiterte Überführungsfunktion - delta_hat *)
Fixpoint delta_hat (q : Q) (word : list Sigma) : Q :=
  match word with
    | nil                  => q
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
 | one_step : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma) (eq : (delta q a) = p), 
                                    Konf_DFA_step (q, (cons a w)) (p, w).

(* Tip: Das wird die reflexiv-transitive
Hülle von Konf_rel_DFA_step, Du brauchst also 3 Konstruktoren (einen
für "Konf_rel_DFA_step ist drin", einen für "ist reflexiv" und
einen für "ist transitiv"...
*)

(*K ext_conf M <=> K = M oder ex L mit K ext_conf L und L conf_step M*)
Inductive Konf_rel_DFA : Konf_DFA -> Konf_DFA -> Type :=
  | refl    : forall (K : Konf_DFA), Konf_rel_DFA K K
  | step  : forall (K L M : Konf_DFA),
                                    Konf_rel_DFA K L ->
                                    Konf_DFA_step L M ->
                                    Konf_rel_DFA K M.

Print option.

(*nextConf*)
Fixpoint nextConf  (conf : Konf_DFA) : option Konf_DFA :=
  match conf with
    | (q, nil)      => None
    | (q, cons a w) => Some (delta q a, w)
  end.

(*Kunfigurationssequenz in einer Liste speichern.*)
Fixpoint conf_Sequenz' (w : list Sigma) : Q -> list Konf_DFA :=
  match w with
    | nil       => fun q : Q => cons (q, nil) nil
    | cons a w  => fun q : Q => cons (q, nil) (conf_Sequenz' w (delta q a))
  end.

Fixpoint conf_Sequenz (conf : Konf_DFA) : list Konf_DFA :=
  match conf with
    | (q, w) => conf_Sequenz' w q
  end.
 
(*Inductive conf_Sequenz Konf_DFA : list Konf_DFA -> Type :=
    | nil : (q, nil)               -> (q, nil) + nil
    | step : (q, cons a w) -> q cons a w cons conf_Sequenz (delta q a) w.
*)

(*Definition der akzeptierten Sprache
Definition L_DFA (w : list Sigma) : Konf_DFA:=
exists p : Q, Konf_rel_DFA (q0 , w) (p, nil).
*)
(*Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_hat q0 w).
Parameter is_accepting : Q -> bool.
*)

End Definitions.

