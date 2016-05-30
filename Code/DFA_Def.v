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

(* Typ der Konfigurationen eines DFA, Conf_DFA = Q x Sigma* *)
Definition Conf_DFA := Q * (list Sigma) : Type.
Print Conf_DFA.
Print cons.
Print fst.

(* Konfigurationsübergangsrelation *)

Inductive Conf_DFA_step : Conf_DFA -> Conf_DFA -> Type :=
 | one_step : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma) (eq : (delta q a) = p), 
                                    Conf_DFA_step (q, (cons a w)) (p, w).

(* Tip: Das wird die reflexiv-transitive
Hülle von Conf_rel_DFA_step, Du brauchst also 3 Konstruktoren (einen
für "Conf_rel_DFA_step ist drin", einen für "ist reflexiv" und
einen für "ist transitiv"...
*)

(*K ext_conf M <=> K = M oder ex L mit K ext_conf L und L conf_step M*)
Inductive Conf_rel_DFA : Conf_DFA -> Conf_DFA -> Type :=
  | refl    : forall (K : Conf_DFA), Conf_rel_DFA K K
  | step  : forall (K L M : Conf_DFA),
                                    Conf_rel_DFA K L ->
                                    Conf_DFA_step L M ->
                                    Conf_rel_DFA K M.

Print option.

(*nextConf*)
Fixpoint nextConf  (conf : Conf_DFA) : option Conf_DFA :=
  match conf with
    | (q, nil)            => None
    | (q, cons a w) => Some (delta q a, w)
  end.

(*Konfigurationssequenz in einer Liste speichern.*)
Fixpoint conf_seq' (w : list Sigma) : Q -> list Conf_DFA :=
  match w with
    | nil             => fun q : Q => cons (q, nil) nil
    | cons a w'  => fun q : Q => cons (q, w) (conf_seq' w' (delta q a))
  end.

Print conf_seq'.
(* aber im 2. Fall muss (q, w) zur Liste hinzugefuegt werden, oder? *)

Fixpoint conf_seq (conf : Conf_DFA) : list Conf_DFA :=
  match conf with
    | (q, w) => conf_seq' w q
  end.

(* Ich habe auch nichts wirklich Besseres zu bieten. Man koennte vermutlich einen
   anonymen Fixpunkt benutzen, aber dadurch wird es nicht lesbarer und 
   ich sehe auch sonst keinen Vorteil.
   Die "Wrapper" Funktion muss dann natuerlich kein Fixpunkt sein. *)

Definition word := list Sigma.

Definition emtptyW := @nil Sigma.
Definition concatW := @cons Sigma.

Fixpoint conf_list (w : word) (q : Q) : list Conf_DFA :=
 let conf := (q, w) in
  match w with
    | nil             => cons conf nil
    | cons a w'  => cons conf (conf_list w' (delta q a))
  end.

Definition conf_to_conf_list (conf : Conf_DFA) : list Conf_DFA :=
  let (q, w) := conf in conf_list w q.

Print list.

(*Definition eines induktiven Datentyps, der Wörter beschreibt.*)
Inductive Word (S : Sigma) : Type :=
| empty_Word : Word S
| cons_Word : Word S -> Word S -> Word S.

(*Definition der akzeptierten Sprache
Definition L_DFA (w : list Sigma) : Conf_DFA:=
exists p : Q, Conf_rel_DFA (q0 , w) (p, nil).
*)
(*Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_hat q0 w).
Parameter is_accepting : Q -> bool.
*)

End Definitions.

