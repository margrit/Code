Require DTS_Def.
Require DTS_cons_Prop.
Require Import Program.
Import Word_Prop.

Module DTS_Word_List  (DTS : DTS_Def.DTS_Par).

Module DTS_Word_List_Prop := DTS_Def.DTS_Fun DTS.
Module DTS_List_Word_Prop := DTS_cons_Prop.DTS_cons_Fun DTS.
Import DTS_Word_List_Prop.
Import DTS_List_Word_Prop.
Import DTS.
(** Die Funktionen [delta_hat] und [delta_hat_cons] angewendet auf ein Wort bzw. eine Liste
beschreiben den gleichen Sachverhalt. Die Liste kann durch [delta_hat_cons] direkt abgearbeitet
werden. Bei [delta_hat] muss die Liste durch [list_to_word] in ein Wort umgewandelt werden,
da der Eingabetyp [Word] erwartet wird. Die Abbildung in die andere Richtung kann man mit
[word_to_list] analog definieren.*)
Lemma delta_hat_cons_snoc (q : Q) (l : list Sigma) :
      delta_hat_cons q l = delta_hat q (list_to_word l).
Proof.
  generalize q.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    intro q1.
    rewrite IHl.
    rewrite delta_hat_Lemma.
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

(** Die Funktionen [Lang_delta] und [Lang_delta_cons] beschreiben die gleichen Sprachen.*)
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

End DTS_Word_List.