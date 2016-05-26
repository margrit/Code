(* Nur Spielerei: *)
Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.


Inductive word {A : Type} : Type:= 
| eps : @word A 
| snoc : @word A -> A -> @word A.

(* Zu Vergleich: *)

Print list.
Print word.


Fixpoint concat {A : Type} (w1 w2 : @word A) : @word A :=
match w2 with 
| eps => w1
| snoc w x => snoc (concat w1 w) x
end.

Eval compute in (concat (snoc (snoc (snoc eps h) a) l) (snoc (snoc eps l) o)).



(* Zur Uebung: *)

(* Berechnung der Wortlaenge *)

Fixpoint word_length {A : Type} (w : @word A) : nat :=
match w with
| eps => (* TODO *)
| snoc w' x => (* TODO *)
end.

 
(* Ein Wort umdrehen: *)

Fixpoint word_reverse {A : Type} (w : @word A) : @word A  :=
(* TODO *)
.

(* Ein Wort in eine Liste umwandeln: *)

Fixpoint word_to_list {A : Type} (w : @word A) : list A :=
(* TODO *)
.


(* Eine Liste in ein Wort umwandeln: *)

Fixpoint list_to_word {A : Type} (l : list A) : @word A :=
(* TODO *)
.


(* Isomorphie zwischen Woertern und Listen: *)

Lemma list_word_list {A : Type} (l : list A) : word_to_list (list_to_word l) = l.
Proof.
admit.
Admitted.


Lemma word_list_word {A : Type} (w : @word A) : list_to_word (word_to_list w) = w.
Proof.
admit.
Admitted. 
