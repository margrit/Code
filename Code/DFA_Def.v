(* Grundsaetzliche Anpassungen: 

   - Benutzung des Fin.t aus der Standard Library 
   - Nicht mit Prop arbeiten sondern mit Type

*)

(** Wie in der Vorlesung Theoretische Informatik I werden die einzelne Komponenten eines
 deterministischen endlichen Automats (DEA, nachfolgend DFA genannt) als 5-Tupel beschrieben.

 DFA = (Q, Sigma, delta, q0, F) mit

* Q, als nichtleere endliche Zustandsmenge
* Sigma, als (endliches) Eingabealphabet
* delta: Q x Sigma -> Q, als Zustandsueberfuehrungsfunktion
* q0, als Startzustand
* F Teilmenge von Q, als Menge der akzeptierenden Zustaende.

 Diese Komponenten werden nachfolgend definiert. *)

Require Import Fin.
Load Words.
Load Pigeonhole_vector.

Section Definitions.

(** Die Anzahl der moeglichen Zustaende. *)

Parameter Q_size : nat.

(** Der Typ der Zustaende. *)

Definition Q := @Fin.t Q_size.

(** Die Anzahl der Elemente des Eingabealphabets. *)

Parameter S_size : nat.

(** Der Typ des Eingabealphabets. *)

Definition Sigma := @Fin.t S_size.

(** Die Transitionsfunktion - delta. *)

Parameter delta : Q -> Sigma -> Q.

(** Die Funktion, die entscheidet, ob ein Zustand ein akzeptierender Zustand ist. *)

Parameter is_accepting : Q -> Type. (*Proofs as Programms Paedagogik*)

(** Der Startzustand. *)

Parameter q0 : Q.

(** Um zu definieren, wann ein Wort akzeptiert wird, muessen noch einige Vorueberlegungen
getroffen werden. Hierzu wird die erweiterte Transitionsfunktion [delta_hat] benoetigt. *)

(** Die erweiterte Ueberfuehrungsfunktion [delta_hat], wie in der Vorlesung definiert. *)

Fixpoint delta_hat (q : Q) (w : @Word Sigma) : Q :=
   match w with
    | eps          => q
    | snoc w' h => delta (delta_hat q w' ) h
  end.

(** Um ein zusaetzliches Zeichen und ein Wort aus dem Eingabealphabet abzuarbeiten kann
erst das Zeichen vor das Wort gehaengt werden, um dann [delta_hat] von dem Ausgangszustand
darauf anzuwenden. Die andere Variante ist, dass zuerst der Folgezustand mit [delta] von dem
Zeichen und dem Ausgangszustand berechnet wird und davon ausgehend dann das Wort 
abgearbeitet wird. *)

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

(** Die Abarbeitung eines, aus zwei Teilwoertern bestehenden Wortes. *)

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

(** Die von einem endlichen Automaten beschriebene Sprachen definiert durch [is_accepting].*)
(* Waere "In_Lang_delta" nicht eigentlich passender
 (betrachte die Formulierung des Pumping Lemmas...) *)

Definition Lang_delta (w : @Word Sigma) : Type :=
           is_accepting (delta_hat q0 w).

(** Die Konfigurationsuebergangsrelation*)

(** Der Typ der Konfigurationen eines DFA, Conf_DFA = Q x @Word Sigma*. *)

Definition Conf_DFA := Q * (@Word Sigma) : Type.

(** Ein einzelner Konfigurationsschritt. Ausgehend von einer Konfiguration, einem Zeichen a
aus Sigma und einem Wort w, wird das Zeichen durch [delta] abgearbeitet und fuehrt zur
nachfolgenden Konfiguration. *)

Inductive Conf_DFA_step : Conf_DFA -> Conf_DFA -> Type :=
  | one_step : forall (q : Q) (a : Sigma) (w : @Word Sigma),
                        Conf_DFA_step (q, (concat_word (snoc eps a) w)) (delta q a, w).

(** Die reflexiv-transitive Huelle von Conf_rel_DFA_step um die eigentliche Konfigurations-
uebergangsrelation zu beschreiben. *)

Inductive Conf_rel_DFA : Conf_DFA -> Conf_DFA -> Type :=
  | refl  : forall (K : Conf_DFA), Conf_rel_DFA K K
  | step  : forall (K L M : Conf_DFA),
                                     Conf_DFA_step K L ->
                                     Conf_rel_DFA L M ->
                                     Conf_rel_DFA K M.

(** Die von einem DFA beschriebene Sprachen definiert durch [Conf_rel_DFA]. *)

Definition Lang_Conf (w: @Word Sigma) : Type :=
           {p : Q & (is_accepting p * Conf_rel_DFA (q0, w) (p, eps))%type}.

(** Fuer die Anwendung des Pumping Lemmas muss die Abarbeitung eines Wortes in einer Liste
gespeichert werden, da diese Informationen enthaelt, ob ein Zustand mehrfach durchlaufen wird.
Dies ist der Fall, wenn die Anzahl der Konfigurationen innerhalb der Liste laenger ist, als die Anzahl
der Zustaende des Automaten. *)

(* Ableiten der naechsten Konfiguration [next_Conf]. *)

Fixpoint next_Conf  (conf : Conf_DFA) : option Conf_DFA :=
  match conf with
    | (q, eps)         => None
    | (q, snoc w a) => Some (delta q a, w)
  end.


(* Hier gibt es offenbar gerade ein Problem ?

(*Konfigurationssequenz in einer Liste speichern.*)
Fixpoint conf_seq' (w : @Word Sigma) : Q -> list Conf_DFA :=
  match w with
    | eps           => fun q : Q => cons (q, eps) nil
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
    | eps             => cons conf nil
    | snoc w' a => cons conf (conf_list w' (delta q a))
  end.

Definition conf_to_conf_list (conf : Conf_DFA) : list Conf_DFA :=
  let (q, w) := conf in conf_list w q.

*)

(*-----------------------------------------------------------------------------*)

(* Liste der Zustaende, die bei der Abarbeitung des Worts durchlaufen werden. 
   Wird in PL-Beweis gebraucht. *)

Definition trace_w (q : Q) (w : @Word Sigma) : @Word Q :=
           map_word (delta_hat q) (inits_w w).

Lemma trace_length_w : forall w : @Word Sigma, forall q : Q,
      word_length (trace_w q w) = S (word_length w).
Proof.
  intros w q.
  unfold trace_w.
  rewrite map_length_w.
  apply inits_len_w.
Defined.

Definition concat_trace_w : forall (q : Q) (w w' : @Word Sigma),
           trace_w q (concat_word w' w) = 
           concat_word (removelast_w (trace_w q w')) 
           (trace_w (delta_hat q w') w).
Proof.
  intros q w w'.
  unfold trace_w.
  rewrite commute_inits_concat_w.
  rewrite commute_concat_map_w.
  rewrite commute_removelast_map_w.
  induction w.
  - simpl. reflexivity.
  - (* Laesst sich das snoc auf einfachere Weise nach aussen ziehen? *)
    simpl (concat_word (removelast_w (map_word (delta_hat q) (inits_w w')))
    (map_word (delta_hat q) (map_word (concat_word w') (inits_w (snoc w a))))).
    simpl (concat_word (removelast_w (map_word (delta_hat q) (inits_w w')))
    (map_word (delta_hat (delta_hat q w')) (inits_w (snoc w a)))).
    rewrite IHw.
    rewrite delta_hat_app.
    reflexivity.
Defined.

(*-----------------------------------------------------------------------------*)

(*Definition der akzeptierten Sprache
Definition L_DFA (w : list Sigma) : Conf_DFA:=
exists p : Q, Conf_rel_DFA (q0 , w) (p, nil).
*)

End Definitions.

