(* Grundsaetzliche Anpassungen: 

   - Benutzung des Fin.t aus der Standard Library 
   - Nicht mit Prop arbeiten sondern mit Type

*)

(** Wie in der Vorlesung Theoretische Informatik I werden die einzelne Komponenten eines
 deterministischen endlichen Automats (DEA, nachfolgend DFA genannt) als 5-Tupel beschrieben.

DFA = (Q, Sigma, delta, q0, F) mit

* Q, als nichtleere endliche Zustandsmenge
* Sigma, als (endliches) Eingabealphabet
* delta: Q x Sigma -> Q, als Zustandsüberführungsfunktion
* q0, als Startzustand
* F Teilmenge von Q, als Menge der akzeptierenden Zustände.

Diese Komponenten werden nachfolgend definiert.*)

Require Import Fin.
(* Load Pigeonhole_vector. *)
Load Word_Prop.

Section Definitions.

(** Die Anzahl der möglichen Zustände.*)
Parameter Q_size : nat.

(** Der Typ der Zustände.*)
Definition Q := @Fin.t Q_size.

(** Die Anzahl der Elemente des Eingabealphabets.*)
Parameter S_size : nat.

(** Der Typ des Eingabealphabets.*)
Definition Sigma := @Fin.t S_size.

(** Die Transitionsfunktion - delta.*)
Parameter delta : Q -> Sigma -> Q.

(** Die Funktion, die entscheidet, ob ein Zustand ein akzeptierender Zustand ist. *)
Parameter is_accepting : Q -> Prop.

(** Der Startzustand. *)
Parameter q0 : Q.

(** Um zu definieren, wann ein Wort akzeptiert wird, mÜssen noch einige Vorüberlegungen
getroffen werden. Hierzu wird die erweiterte Transitionsfunktion [delta_hat] bzw. 
[delta_hat_cons] benötigt. Da im allgemeinen auf Wörtern gearbeitet werden soll, die [snoc] als
Konstruktor haben, wird dies in den Funktionsnamen weggelassen, um diese kurz zu halten.
Nur wenn explizit auf Listen gearbeitet werden soll, wird der [cons] Konstruktor im Namen
verwendet.*)

(** Die erweiterte Überführungsfunktion [delta_hat], wie in der Vorlesung definiert.*)
Fixpoint delta_hat (q : Q) (w : @Word Sigma) : Q :=
   match w with
    | eps          => q
    | snoc w' h => delta (delta_hat q w' ) h
  end.

(** Um ein zusätzliches Zeichen und ein Wort aus dem Eingabealphabet abzuarbeiten kann
erst das Zeichen vor das Wort gehängt werden, um dann [delta_hat] von dem Ausgangszustand
darauf anzuwenden. Die andere Variante ist, dass zuerst der Folgezustand mit [delta] von dem
Zeichen und dem Ausgangszustand berechnet wird und davon ausgehend dann das Wort 
abgearbeitet wird.*)
Lemma delta_hat_Lemma (q : Q) (a : Sigma) (w : @Word Sigma) :
  delta_hat q (concat_word (snoc eps a) w) = delta_hat (delta q a) w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Theorem delta_hat_app : forall w v : @Word Sigma, forall q : Q,
  delta_hat q (concat_word w v) = delta_hat (delta_hat q w) v.
Proof.
  induction v.
  - simpl.
    intros q.
    reflexivity.
  - simpl.
    intros.
    rewrite <- IHv.
    reflexivity.
Defined.

Definition accepted_word (w : @Word Sigma) : Prop :=
  is_accepting (delta_hat q0 w).

(** Die von einem endlichen Automaten beschriebene Sprachen.*)
Definition DFA_Lang (w : @Word Sigma) : Prop :=
  accepted_word w.

(* Der Typ der Konfigurationen eines DFA, Conf_DFA = Q x @Word Sigma*.*)
(*Definition Conf_DFA := Q * (list Sigma) : Type.*)
Definition Conf_DFA := Q * (@Word Sigma) : Type.

(* Konfigurationsübergangsrelation mit Type*)

(*### geht besser ###*)
(* Ein einzelner Konfigurationsschritt. Ausgehend von einer Konfiguration, einem Zeichen
aus Sigma und einem Wort, wird das Zeichen durch [delta] abgearbeitet und führt zur
nachfolgenden Konfiguration.*)
Inductive Conf_DFA_step : Conf_DFA -> Conf_DFA -> Type :=
 | one_step : forall (q : Q) (p : Q) (a : Sigma) (w : @Word Sigma) (eq : (delta q a) = p),
                                    Conf_DFA_step (q, (snoc w a)) (p, w).

(* Die reflexiv-transitive Hülle von Conf_rel_DFA_step.
K ext_conf M <=> K = M (revlexiv) oder 
ex L mit K ext_conf L und L conf_step M (reflexiv-transitive Hülle)*)
Inductive Conf_rel_DFA : Conf_DFA -> Conf_DFA -> Type :=
  | refl    : forall (K : Conf_DFA), Conf_rel_DFA K K
  | step  : forall (K L M : Conf_DFA),
                                     Conf_rel_DFA K L ->
                                     Conf_DFA_step L M ->
                                     Conf_rel_DFA K M.

(** Für die Anwendung des Pumping Lemmas muss die Abarbeitung eines Wortes in einer Liste
gespeichert werden, da diese Informationen enthält, ob ein Zustand mehrfach durchlaufen wird.
Dies ist der Fall, wenn die Anzahl der Konfigurationen innerhalb der Liste länger ist, als die Anzahl
der Zustände des Automaten.*)

(* Ableiten der nächsten Konfiguration [next_Conf].*)
Fixpoint next_Conf  (conf : Conf_DFA) : option Conf_DFA :=
  match conf with
    | (q, eps)      => None
    | (q, snoc w a) => Some (delta q a, w)
  end.

(*Konfigurationssequenz in einer Liste speichern.*)
Fixpoint conf_seq' (w : @Word Sigma) : Q -> list Conf_DFA :=
  match w with
    | eps        => fun q : Q => cons (q, eps) nil
    | snoc w' a  => fun q : Q => cons (q, w) (conf_seq' w' (delta q a))
  end.

Print conf_seq'.
(* aber im 2. Fall muss (q, w) zur Liste hinzugefuegt werden, oder? *)

Fixpoint conf_seq (conf : Conf_DFA) : list Conf_DFA :=
  match conf with
    | (q, w) => conf_seq' w q
  end.

(*################# Alternativ ###################*)

(* Ich habe auch nichts wirklich Besseres zu bieten. Man koennte vermutlich einen
   anonymen Fixpunkt benutzen, aber dadurch wird es nicht lesbarer und 
   ich sehe auch sonst keinen Vorteil.
   Die "Wrapper" Funktion muss dann natuerlich kein Fixpunkt sein. *)

Fixpoint conf_list (w : @Word Sigma) (q : Q) : list Conf_DFA :=
 let conf := (q, w) in
  match w with
    | eps       => cons conf nil
    | snoc w' a => cons conf (conf_list w' (delta q a))
  end.

Definition conf_to_conf_list (conf : Conf_DFA) : list Conf_DFA :=
  let (q, w) := conf in conf_list w q.

Fixpoint state_letter_list (w : @Word Sigma) (q : Q) : list (Q * option Sigma) :=
 match w with 
  | eps => cons (q, None) nil
  | snoc w' a => cons (q, Some a) (state_letter_list w' (delta q a))
 end.

(*Definition der akzeptierten Sprache
Definition L_DFA (w : list Sigma) : Conf_DFA:=
exists p : Q, Conf_rel_DFA (q0 , w) (p, nil).
*)

End Definitions.

