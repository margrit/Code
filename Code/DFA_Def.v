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
Load Word_Prop.

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
erweiterte Transitionsfunktion delta_hat_cons. *)

(* Erweiterte Überführungsfunktion - delta_hat, wird wahrscheinlich wieder rausgenommen, 
 da in der Vorlesung über snoc-Listen definiert wurde.*)
Fixpoint delta_hat_cons (q : Q) (w : list Sigma) : Q :=
  match w with
    | nil             => q
    | cons h w' => delta_hat_cons (delta q h) w'
  end.

(*Lemma delta_hat_cons_Lemma (q : Q) (a : Sigma) (l : list Sigma) :
  delta_hat_cons q (l ++ (a :: nil)) = delta (delta_hat_cons q l) a.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Defined.
*)

(* Erweiterte Überführungsfunktion delta_hat_snoc, wie in der Vorlesung definiert.*)
Fixpoint delta_hat_snoc (q : Q) (w : @Word Sigma) : Q :=
   match w with
    | eps          => q
    | snoc w' h => delta (delta_hat_snoc q w' ) h
  end.

Lemma delta_hat_snoc_Lemma (q : Q) (a : Sigma) (w : @Word Sigma) :
  delta_hat_snoc q (concat_word (snoc eps a) w) = delta_hat_snoc (delta q a) w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma delta_hat_cons_snoc (q : Q) (l : list Sigma) :
  delta_hat_cons q l = delta_hat_snoc q (list_to_word_rec l).
Proof.
generalize q.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite (IHl (delta q1 a)).
    rewrite (delta_hat_snoc_Lemma q1 a (list_to_word_rec l)).
    reflexivity.
Defined.

(*Lemma delta_hat_snoc_cons (q : Q) (w : @Word Sigma) :
  delta_hat_snoc q w = delta_hat_cons q (word_to_list_rec w).
Proof.
generalize q.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite <- (IHw (delta_hat_snoc q1 w)).
    rewrite (delta_hat_snoc_Lemma q1 a (list_to_word_rec l)).
    reflexivity.
Defined.
*)

(* Definiert, wann ein Wort akzeptiert wird. *)
Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_hat_cons q0 w).

Definition accepted_word_snoc (w : @Word Sigma) :=
  is_accepting (delta_hat_snoc q0 w).

(* Typ der Konfigurationen eines DFA, Conf_DFA = Q x Sigma* *)
(*Definition Conf_DFA := Q * (list Sigma) : Type.*)
Definition Conf_DFA := Q * (@Word Sigma) : Type.
Print Conf_DFA.

(* Konfigurationsübergangsrelation *)

(* Ein einzelner Konfigurationsschritt. *)
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

Print option.

(* Ableiten der nächsten Konfiguration - next_Conf.*)
Fixpoint next_Conf  (conf : Conf_DFA) : option Conf_DFA :=
  match conf with
    | (q, eps)         => None
    | (q, snoc w a) => Some (delta q a, w)
  end.

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

(*Definition word := list Sigma.

Definition emtptyW := @nil Sigma.
Definition concatW := @cons Sigma.
*)

Fixpoint conf_list (w : @Word Sigma) (q : Q) : list Conf_DFA :=
 let conf := (q, w) in
  match w with
    | eps             => cons conf nil
    | snoc w' a => cons conf (conf_list w' (delta q a))
  end.

Definition conf_to_conf_list (conf : Conf_DFA) : list Conf_DFA :=
  let (q, w) := conf in conf_list w q.

Print list.

(*Definition eines induktiven Datentyps, der Wörter beschreibt.*)
(*Inductive Word (S : Sigma) : Type :=
| empty_Word : Word S
| cons_Word : Word S -> Word S -> Word S.
*)
(*Definition der akzeptierten Sprache
Definition L_DFA (w : list Sigma) : Conf_DFA:=
exists p : Q, Conf_rel_DFA (q0 , w) (p, nil).
*)
(*Definition accepted_word (w : list Sigma) :=
  is_accepting (delta_hat q0 w).
Parameter is_accepting : Q -> bool.
*)

End Definitions.

