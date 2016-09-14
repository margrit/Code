(* TODO Margrit:  -> done
      Bemerkungen anpassen: 
         Was sind Deterministische Transitionssysteme ?
           im Prinzip dasselbe wie DFAs, nur die Endlichkeit der 
           Zustands- und Eingabealphabet-Typen ist weggelassen
         DFAs sind also spezielle DTSs.
         Warum trennen wir das?
           Definitionen delta_hat, Conf, Lang_delta, Lang_Conf und auch
           der Äquivalenzbeweis von Lang_delta und Lang_Conf (in DFA_prop 
           (das sollte übrigens DTS_prop heissen)) hängen nicht von der
           Endlichkeit ab.
*)

(** Wie in der Vorlesung Theoretische Informatik I werden die einzelne Komponenten eines
 deterministischen Transitionssystem (DTS) als 5-Tupel beschrieben.

DTS = (Q, Sigma, delta, q0, F) mit

* Q, als Zustandsmenge
* Sigma, als Eingabealphabet
* delta: Q x Sigma -> Q, als Zustandsüberführungsfunktion
* q0, als Startzustand
* F Teilmenge von Q, als Menge der akzeptierenden Zustände.

Diese Komponenten werden nachfolgend definiert.*)

(*Load Pigeonhole_vector.
Load Word_Prop. *)
Require Import Word_Prop.

Module Type DTS_Par.


(** Der Typ der Zustände.*)
Parameter Q : Type.

(** Der Typ des Eingabealphabets.*)
Parameter Sigma : Type.

(** Die Transitionsfunktion - delta.*)
Parameter delta : Q -> Sigma -> Q.

(** Die Funktion, die entscheidet, ob ein Zustand ein akzeptierender Zustand ist. *)
Parameter is_accepting : Q -> Type. (*Proofs as programs Pädagogik*)

(** Der Startzustand. *)
Parameter q0 : Q.

End DTS_Par.
(** Signatur der Eigenschaften von DTS.*)
Module Type DTS_Prop.

Parameter Q : Type.
Parameter Sigma : Type.
Parameter delta : Q -> Sigma -> Q.
Parameter is_accepting : Q -> Type.
Parameter q0 : Q.
Parameter delta_hat : Q -> @Word Sigma -> Q.
Axiom delta_hat_Lemma : forall (q : Q) (a : Sigma) (w : @Word Sigma),
  delta_hat q (concat_word (snoc eps a) w) = delta_hat (delta q a) w.
Axiom delta_hat_app : forall (w v : @Word Sigma) (q : Q),
  delta_hat q (concat_word w v) = delta_hat (delta_hat q w) v.
Parameter Lang_delta : @Word Sigma -> Type.
Parameter Conf : Type.
Parameter Conf_rel : Conf -> Conf -> Type.
Parameter Lang_Conf : @Word Sigma -> Type.
End DTS_Prop.

(** Funktor*)
Module DTS_Fun (Par : DTS_Par) <: DTS_Prop.
Import Par.
Definition Q := Q.
Definition Sigma := Sigma.
Definition delta := delta.
Definition is_accepting := is_accepting.
Definition q0 := q0.

(** Die erweiterte Überführungsfunktion [delta_hat], wie in der Vorlesung definiert.*)
Fixpoint delta_hat (q : Q) (w : @Word Sigma) := 
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
Lemma delta_hat_app : forall w v : @Word Sigma, forall q : Q,
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
(* Hilfsrelation [Conf_step] *)
Inductive Conf_step : Conf -> Conf -> Type :=
 | one_step : forall (q : Q) (a : Sigma) (w : @Word Sigma),
                        Conf_step (q, (concat_word [a] w)) (delta q a, w).

(** Die reflexiv-transitive Hülle von Conf_rel_DFA_step um die eigentliche Konfigurations-
übergangsrelation zu beschreiben.*)
Inductive Conf_rel' : Conf -> Conf -> Type :=
  | refl  : forall (K : Conf), Conf_rel' K K
  | step  : forall (K L M : Conf), Conf_step K L -> Conf_rel' L M -> Conf_rel' K M.

Definition Conf_rel := Conf_rel'.

(** Die von einem deterministischen Transitionssystems beschriebene Sprachen definiert 
durch [Conf_rel].*)
Definition Lang_Conf (w: @Word Sigma) : Type :=
{p : Q & (is_accepting p * Conf_rel (q0, w) (p, eps))%type}.

End DTS_Fun.


(** Um zu definieren, wann ein Wort akzeptiert wird, müssen noch einige Vorüberlegungen
getroffen werden. Hierzu wird die erweiterte Transitionsfunktion [delta_hat] bzw. benötigt. *)
