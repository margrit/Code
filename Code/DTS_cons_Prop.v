(* Hier kommen die cons Sachen rein, woraus man Übungsaufgaben basteln kann*)
Require DTS_Def.
Require Import List.

Module Type DTS_cons_Prop.
Parameter Q : Type.
Parameter Sigma : Type.
Parameter delta : Q -> Sigma -> Q.
Parameter is_accepting : Q -> Type.
Parameter q0 : Q.
Parameter delta_hat_cons : Q -> list Sigma -> Q.
Axiom delta_hat_cons_Lemma : forall (q : Q) (a : Sigma) (l : list Sigma),
  delta_hat_cons q (l ++ (a :: nil)) = delta (delta_hat_cons q l) a.
Axiom delta_hat_cons_app : forall xs ys : list Sigma, forall q : Q,
  delta_hat_cons q (xs ++ ys) = delta_hat_cons (delta_hat_cons q xs) ys.
Parameter Lang_delta_cons : list Sigma -> Type.
Parameter Conf : Type.
Parameter Conf_rel : Conf -> Conf -> Type.
Parameter Lang_Conf : list Sigma -> Type.
End DTS_cons_Prop.

Module DTS_cons_Fun (Par : DTS_Def.DTS_Par) <: DTS_cons_Prop.
Import Par.
Definition Q := Q.
Definition Sigma := Sigma.
Definition delta := delta.
Definition is_accepting := is_accepting.
Definition q0 := q0.

(** Erweiterte Überführungsfunktion [delta_hat_cons], wird hier nicht weiter verwendet,
 da die Verfahren in der Vorlesung über den [snoc] Konstruktor definiert wurden. Es wäre als eine
 Übungsaufgabe denkbar, dass kleine Beispiele mit dem [cons] Konstruktor zu lösen sind.*)
Fixpoint delta_hat_cons (q : Q) (l : list Sigma) : Q :=
  match l with
    | nil             => q
    | cons h l' => delta_hat_cons (delta q h) l'
  end.

(** Siehe [delta_hat_Lemma, nur auf Listen statt Wörtern.]*)
Lemma delta_hat_cons_Lemma (q : Q) (a : Sigma) (l : list Sigma) :
  delta_hat_cons q (l ++ (a :: nil)) = delta (delta_hat_cons q l) a.
Proof.
generalize q.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite IHl.
    reflexivity.
Defined.

(** Die Abarbeitung einer, aus zwei Teillisten bestehenden Liste.*)
Theorem delta_hat_cons_app : forall xs ys : list Sigma, forall q : Q,
  delta_hat_cons q (xs ++ ys) = delta_hat_cons (delta_hat_cons q xs) ys.
Proof.
  induction xs.
  - simpl.
    intros ys q.
    reflexivity.
  - simpl.
    intros.
    apply IHxs.
Defined.

(** Die von einem endlichen Automaten beschriebene Sprachen definiert durch [is_accepting].*)
Definition Lang_delta_cons (l : list Sigma) :=
  is_accepting (delta_hat_cons q0 l).

(** Der Typ der Konfigurationen eines DTS, Conf = Q x @Word Sigma*.*)
Definition Conf := Q * (list Sigma) : Type.

(** Ein einzelner Konfigurationsschritt. Ausgehend von einer Konfiguration, einem Zeichen a
aus Sigma und einem Wort w, wird das Zeichen durch [delta] abgearbeitet und führt zur
nachfolgenden Konfiguration.*)
(* Hilfsrelation [Conf_step] *)
Inductive Conf_step : Conf -> Conf -> Type :=
 | one_step : forall (q : Q) (a : Sigma) (l : list Sigma),
                        Conf_step (q, (a :: l)) (delta q a, l).

(** Die reflexiv-transitive Hülle von Conf_rel_DFA_step um die eigentliche Konfigurations-
übergangsrelation zu beschreiben.*)
Inductive Conf_rel' : Conf -> Conf -> Type :=
  | refl  : forall (K : Conf), Conf_rel' K K
  | step  : forall (K L M : Conf), Conf_step K L -> Conf_rel' L M -> Conf_rel' K M.

Definition Conf_rel := Conf_rel'.
(** Die von einem deterministischen Transitionssystems beschriebene Sprachen definiert 
durch [Conf_rel].*)
Definition Lang_Conf (l : list Sigma) : Type :=
{p : Q & (is_accepting p * Conf_rel (q0, l) (p, nil))%type}.

End DTS_cons_Fun.
