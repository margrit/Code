(** Wie in der Vorlesung Theoretische Informatik I werden die einzelne Komponenten eines
 deterministischen Transitionssystem (DTS) als 5-Tupel beschrieben.

DTS = (Q, Sigma, delta, q0, F) mit

* Q, als Zustandsmenge
* Sigma, als Eingabealphabet
* delta: Q x Sigma -> Q, als Zustandsüberführungsfunktion
* q0, als Startzustand
* F Teilmenge von Q, als Menge der akzeptierenden Zustände.

Diese Komponenten werden nachfolgend definiert.*)

Module Type Sigma.
Require Word_Prop.
(** Der Typ des Eingabealphabets.*)
Parameter Sigma : Type.
End Sigma.

Module Type Q.
(** Der Typ der Zustände.*)
Parameter Q : Type.
(** Der Startzustand. *)
Parameter q0 : Q.
End Q.
(*
Module Par (S:Sigma) (Q:Q).
Import Q.
Import Sigma.
Definition Q := Q.
Definition Sigma := Sigma.
(** Die Transitionsfunktion - delta.*)
Definition delta : Q -> Sigma -> Q.
(** Die Funktion, die entscheidet, ob ein Zustand ein akzeptierender Zustand ist. *)
Definition is_accepting : Q -> Type. (*Proofs as programs Pädagogik*)

*)
Require Import Word_Prop.
Module WordSig (S : Sigma) (Q : Q) : Sigma with Definition Sigma := @Word S.Sigma.
Import Q.
Definition Sigma := @Word S.Sigma.
Definition Q := Q.
Definition delta := Q -> Sigma -> Q.
Definition is_accepting := Q -> Type.
Definition q0 := q0.
End WordSig.


Module DTS_Fun (Par : DTS_Par) <: DTS_Par.
Import Par.
Import Word_Prop.

Definition Q := Q.
Definition delta := delta.
Definition is_accepting := is_accepting.
Definition q0 := q0.

(** Um zu definieren, wann ein Wort akzeptiert wird, müssen noch einige Vorüberlegungen
getroffen werden. Hierzu wird die erweiterte Transitionsfunktion [delta_hat] bzw. benötigt. *)

(** Die erweiterte Überführungsfunktion [delta_hat], wie in der Vorlesung definiert.*)
Fixpoint delta_hat (q : Q) (w : @Word Sigma) : Q :=
   match w with
    | eps       => q
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

(** Die Abarbeitung eines aus zwei Teilwörtern bestehenden Wortes*)
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

(** Die von einem deterministischen Transitionssystems beschriebene Sprachen definiert 
durch [is_accepting].*)
Definition Lang_delta (w : @Word Sigma) : Type :=
  is_accepting (delta_hat q0 w).

(** Die Konfigurationsübergangsrelation*)

(** Der Typ der Konfigurationen eines DTS, Conf = Q x @Word Sigma*.*)
Definition Conf := Q * (@Word Sigma) : Type.

(** Ein einzelner Konfigurationsschritt. Ausgehend von einer Konfiguration, einem Zeichen a
aus Sigma und einem Wort w, wird das Zeichen durch [delta] abgearbeitet und führt zur
nachfolgenden Konfiguration.*)

Inductive Conf_step : Conf -> Conf -> Type :=
 | one_step : forall (q : Q) (a : Sigma) (w : @Word Sigma),
                        Conf_step (q, (concat_word [a] w)) (delta q a, w).

(** Die reflexiv-transitive Hülle von Conf_rel_DFA_step um die eigentliche Konfigurations-
übergangsrelation zu beschreiben.*)
Inductive Conf_rel : Conf -> Conf -> Type :=
  | refl  : forall (K : Conf), Conf_rel K K
  | step  : forall (K L M : Conf), Conf_step K L -> Conf_rel L M -> Conf_rel K M.

(** Die von einem deterministischen Transitionssystems beschriebene Sprachen definiert 
durch [Conf_rel].*)
Definition Lang_Conf (w: @Word Sigma) : Type :=
{p : Q & (is_accepting p * Conf_rel (q0, w) (p, eps))%type}.

(** Für die Anwendung des Pumping Lemmas muss die Abarbeitung eines Wortes in einer Liste
gespeichert werden, da diese Informationen enthält, ob ein Zustand mehrfach durchlaufen wird.
Dies ist der Fall, wenn die Anzahl der Konfigurationen innerhalb der Liste länger ist, als die Anzahl
der Zustände des Automaten.*)

(* Ableiten der nächsten Konfiguration [next_Conf].*)
Fixpoint next_Conf  (conf : Conf) : option Conf :=
  match conf with
    | (q, eps)      => None
    | (q, snoc w a) => Some (delta q a, w)
  end.

(*Konfigurationssequenz in einer Liste speichern.*)
Fixpoint conf_seq' (w : @Word Sigma) : Q -> list Conf :=
  match w with
    | eps        => fun q : Q => cons (q, eps) nil
    | snoc w' a  => fun q : Q => cons (q, w) (conf_seq' w' (delta q a))
  end.

(*Print conf_seq'.*)
(* aber im 2. Fall muss (q, w) zur Liste hinzugefuegt werden, oder? *)

Fixpoint conf_seq (conf : Conf) : list Conf :=
  match conf with
    | (q, w) => conf_seq' w q
  end.

(*################# Alternativ ###################*)

(* Ich habe auch nichts wirklich Besseres zu bieten. Man koennte vermutlich einen
   anonymen Fixpunkt benutzen, aber dadurch wird es nicht lesbarer und 
   ich sehe auch sonst keinen Vorteil.
   Die "Wrapper" Funktion muss dann natuerlich kein Fixpunkt sein. *)

Fixpoint conf_list (w : @Word Sigma) (q : Q) : list Conf :=
 let conf := (q, w) in
  match w with
    | eps       => cons conf nil
    | snoc w' a => cons conf (conf_list w' (delta q a))
  end.

Definition conf_to_conf_list (conf : Conf) : list Conf :=
  let (q, w) := conf in conf_list w q.

End DTS_Fun.

