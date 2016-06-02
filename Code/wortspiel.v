(* Nur Spielerei: *)
Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.


Inductive word {A : Type} : Type:= 
| eps : @word A 
| snoc : @word A -> A -> @word A.

(* Zu Vergleich: *)

Print list.
Print word.


Fixpoint concat_word {A : Type} (w1 w2 : @word A) : @word A :=
match w2 with 
| eps => w1
| snoc w x => snoc (concat_word w1 w) x
end.

Eval compute in (concat_word (snoc (snoc (snoc eps h) a) l) (snoc (snoc eps l) o)).
Print "++".
(*Eigenschaften von concat_word*)
Lemma concat_word_nil {A : Type} (w : @word A) : concat_word w eps = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Defined.

(*Lemma concat_word_associative {A : Type} (w1 w2 w3 : @word A) :
  concat_word (concat_word w1 w2) w3 = concat_word w1 (concat_word w2 w3).
Proof.
  induction w1.
  -
*)
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
| snoc w' x  => concat_word (snoc eps x) (word_reverse w')
end.

(*Eigenschaften von word_reverse*)

(*Lemma word_reverse_nil  {A : Type} (w : @word A) : snoc*)

(*Lemma word_reverse_concat_word {A : Type} (w1 w2 : @word A) :
      word_reverse (concat_word w1 w2) = concat_word (word_reverse w1) (word_reverse w2).
Proof.
  induction w1.
  - assert (word_reverse eps = @eps A).
    + simpl; reflexivity.
    + rewrite H.
    pose (concat_word_nil (word_reverse w2)).
...
    rewrite e.
    simpl; reflexivity.
  - simpl.
    rewrite IHw2.
    apply concat_word_associative.
Defined.

Lemma word_reverse_idempotent {A : Type} (w : @word A) : word_reverse (word_reverse w) = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_reverse_concat_word (word_reverse w) snoc nil a).
    rewrite e.
    rewrite IHw.
    simpl.
    reflexivity.
Defined.
*)

Eval compute in (word_reverse (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(* Ein Wort in eine Liste umwandeln: *)
Fixpoint word_to_list {A : Type} (w : @word A) : list A :=
match w with
| eps           => nil
| snoc w' x  => cons x (word_to_list w')
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

Require Import List.

Print rev.

(*Ein Wort in eine Liste umwandeln unter Beachtung der Reihenfolge.*)
Definition word_to_list'' {A : Type} (w : @word A) : list A := rev (word_to_list w).
Eval compute in (word_to_list'' (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).
Definition word_to_list''' {A : Type} (w : @word A) : list A := word_to_list (word_reverse w).
Eval compute in (word_to_list''' (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

Fixpoint word_to_list' {A : Type} (w : @word A) : list A :=
match w with
| eps           => nil
| snoc w' x  => rev (cons x (word_to_list' w'))
end.

Eval compute in (word_to_list' (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(*Eine Liste in ein Wort umwandeln unter Beachtung der Reihenfolge.*)
Definition list_to_word'' {A : Type} (l : list A) : @word A := word_reverse (list_to_word l).
Eval compute in (list_to_word'' (cons h(cons a(cons l nil)))).
Definition list_to_word''' {A : Type} (l : list A) : @word A := list_to_word (rev l).
Eval compute in (list_to_word''' (cons h(cons a(cons l nil)))).

Fixpoint list_to_word' {A : Type} (l : list A) : @word A :=
match l with
| nil           => eps
| cons x l'  => word_reverse (snoc (list_to_word' l') x)
end.

Eval compute in (list_to_word' (cons h(cons a(cons l nil)))).

(*Nach Definition von word_to_list'' - ergo albern*)
Lemma rev_word_to_list {A : Type} (w : @word A) : rev (word_to_list w) = word_to_list'' w.
Proof.
unfold word_to_list''.
reflexivity.
Qed.

Lemma list_word_list'' {A : Type} (l : list A) : word_to_list'' (list_to_word'' l) = l.
Proof.
unfold word_to_list''.
induction l.
  - simpl.
    reflexivity.
  - 

Lemma word_list_word'' {A : Type} (w : @word A) : list_to_word'' (word_to_list'' w) = w.