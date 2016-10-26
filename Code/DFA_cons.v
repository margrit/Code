Load DFA_Def.

(** Die erweiterte Ueberfuehrungsfunktion [delta_hat_cons] fuer Listen. *)

Fixpoint delta_hat_cons (q : Q) (w : list Sigma) : Q :=
  match w with
    | nil             => q
    | cons h w' => delta_hat_cons (delta q h) w'
  end.

(** Siehe [delta_hat_Lemma], nur auf Listen statt Woertern. *)

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

(** Die Abarbeitung einer aus zwei Teillisten bestehenden Liste. *)

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

(** Die Funktionen [delta_hat] und [delta_hat_cons] angewendet auf ein Wort bzw. eine Liste
beschreiben, den gleichen Sachverhalt. Die Liste kann durch [delta_hat_cons] direkt abgearbeitet
werden. Bei [delta_hat] muss die Liste durch [list_to_word] in ein Wort umgewandelt werden,
da der Eingabetyp [Word] erwartet wird. Die Abbildung in die andere Richtung kann mit
[word_to_list] analog definiert werden. *)

Lemma delta_hat_cons_snoc (q : Q) (l : list Sigma) :
      delta_hat_cons q l = delta_hat q (list_to_word l).
Proof.
  generalize q.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite (IHl (delta q1 a)).
    rewrite (delta_hat_Lemma q1 a (list_to_word l)).
    reflexivity.
Defined.

Lemma delta_hat_snoc_cons (q : Q) (w : @Word Sigma) :
      delta_hat q w = delta_hat_cons q (word_to_list w).
Proof.
  generalize q.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite IHw.
    rewrite <- delta_hat_cons_Lemma.
    reflexivity.
Defined.

(** Die von einem endlichen Automaten beschriebene Sprache definiert durch [Lang_delta_cons]. *)

Definition Lang_delta_cons (w : list Sigma) :=
           is_accepting (delta_hat_cons q0 w).

(** Die Funktionen [Lang_delta] und [Lang_delta_cons] beschreiben die gleiche Sprache. *)

Lemma Lang_delta_Lemma (w : @Word Sigma) :
      Lang_delta w = Lang_delta_cons (word_to_list w).
Proof.
  unfold Lang_delta.
  unfold Lang_delta_cons.
  induction w.
  - simpl.
    reflexivity.
  - generalize q0.
    simpl.
    intro q0.
    rewrite delta_hat_cons_Lemma.
    rewrite delta_hat_snoc_cons.
    reflexivity.
Defined.
