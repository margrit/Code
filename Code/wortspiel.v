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
| eps          => 0
| snoc w' x => S (word_length w')
end.

Eval compute in (word_length (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(* Ein Wort umdrehen: *)

Fixpoint word_reverse {A : Type} (w : @word A) : @word A  :=
match w with
| eps           => eps
| snoc w' x  => concat (snoc eps x) (word_reverse w')
end.

Eval compute in (word_reverse (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

Require Import List.
(* Ein Wort in eine Liste umwandeln: *)

Fixpoint word_to_list {A : Type} (w : @word A) : list A :=
match w with
| eps           => nil
| snoc w' x  => cons x (word_to_list w')
end.

Fixpoint rev_word_to_list {A : Type} (w : @word A) : list A :=
match w with
| eps           => nil
| snoc w' x  => rev (cons x (rev_word_to_list w'))
end.

Eval compute in (word_to_list (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(* Eine Liste in ein Wort umwandeln: *)

Fixpoint list_to_word {A : Type} (l : list A) : @word A :=
match l with
| nil           => eps
| cons x l'  => snoc (list_to_word l') x
end.

Eval compute in (list_to_word (cons h(cons a(cons l nil)))).

(* Isomorphie zwischen Woertern und Listen: *)

Lemma list_word_list {A : Type} (l : list A) : word_to_list (list_to_word l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma word_list_word {A : Type} (w : @word A) : list_to_word (word_to_list w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Qed.
