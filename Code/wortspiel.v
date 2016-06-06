Require Import List.
(* Nur Spielerei: *)
Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.

(*Definition von Wörtern*)

Inductive word {A : Type} : Type:= 
  | eps   : @word A
  | snoc : @word A -> A -> @word A.

(* Berechnung der Wortlaenge *)
Fixpoint word_length {A : Type} (w : @word A) : nat :=
  match w with
    | eps          => 0
    | snoc w' x => S (word_length w')
  end.

Eval compute in (word_length (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(*Verknüpfung zweier Wörter*)
Fixpoint concat_word {A : Type} (w1 w2 : @word A) : @word A :=
  match w2 with
    | eps => w1
    | snoc w x => snoc (concat_word w1 w) x
  end.

Eval compute in (concat_word (snoc (snoc (snoc eps h) a) l) (snoc (snoc eps l) o)).

(*Eigenschaften von concat_word*)
Lemma concat_word_nil {A : Type} (w : @word A) : concat_word eps w = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma concat_word_associative {A : Type} (w1 w2 w3 : @word A) :
  concat_word (concat_word w1 w2) w3 = concat_word w1 (concat_word w2 w3).
Proof.
  induction w3.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw3.
    reflexivity.
Defined.

(* Ein Wort umdrehen: *)
Fixpoint word_reverse {A : Type} (w : @word A) : @word A  :=
  match w with
    | eps           => eps
    | snoc w' x  => concat_word (snoc eps x) (word_reverse w')
  end.

(*Eigenschaften von word_reverse*)
Lemma word_reverse_concat_word {A : Type} (w1 w2 : @word A) :
      word_reverse (concat_word w1 w2) = concat_word (word_reverse w2) (word_reverse w1).
Proof.
induction w2.
  - assert (word_reverse eps = @eps A).
    + simpl; reflexivity.
    + rewrite H.
       simpl.
       pose (concat_word_nil (word_reverse w1)) as con_nil.
       rewrite con_nil.
       reflexivity.
  - simpl.
    rewrite IHw2.
    apply eq_sym.
    apply concat_word_associative.
Defined.

Lemma word_reverse_idempotent {A : Type} (w : @word A) : word_reverse (word_reverse w) = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_reverse_concat_word (snoc eps a0) (word_reverse w) ).
    rewrite e.
    rewrite IHw.
    simpl.
    reflexivity.
Defined.

Eval compute in (word_reverse (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(*Eigenschaften von concat - aus wortspiel2.v*)

(*Eigenschaften von rev - aus wortspiel2.v*)


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

(*Ein Wort in eine Liste umwandeln unter Beachtung der Reihenfolge.*)
Definition word_to_list'' {A : Type} (w : @word A) : list A := rev (word_to_list w).
Eval compute in (word_to_list'' (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

(*Idee: Wort erst in eine Liste umwandeln und dann die Reihenfolge wieder zurück ändern.*)
Fixpoint word_to_list_rec {A: Type} (w : @word A) : list A :=
  match w with
  | eps           => nil
  | snoc w' x  => app (word_to_list_rec w') (cons x nil)
end.

Eval compute in (word_to_list_rec (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

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

Fixpoint list_to_word_rec {A : Type} (l : list A) : @word A :=
match l with
  | nil           => eps
  | cons x l'  => concat_word (snoc eps x) (list_to_word_rec l')
end.

Eval compute in (list_to_word_rec (cons h(cons a(cons l (cons l nil))))).

Definition list_to_word''' {A : Type} (l : list A) : @word A := list_to_word (rev l).
Eval compute in (list_to_word''' (cons h(cons a(cons l nil)))).

Fixpoint list_to_word' {A : Type} (l : list A) : @word A :=
match l with
| nil           => eps
| cons x l'  => word_reverse (snoc (list_to_word' l') x)
end.

Eval compute in (list_to_word' (cons h(cons a(cons l nil)))).


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

(*Kopie aus wortspiel2 *)
Lemma list_to_word_singleappend {A : Type} (a : A) (l : list A) :
  list_to_word (l ++ (a :: nil)) = concat_word (snoc eps a) (list_to_word l).
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Defined.
(*Ende der Kopie aus wortspiel2 *)

(*word_to_list_rec (concat_word (snoc eps a0) (list_to_word_rec l0)) = a0 :: l0*)

Lemma word_to_list_rec_singleappend {A : Type} (x : A) (w : @word A):
word_to_list_rec (concat_word w (snoc eps x))  = app (word_to_list_rec w) (cons x nil).
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Defined.

Lemma list_word_list_rec {A : Type} (l : list A) : word_to_list_rec (list_to_word_rec l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_to_list_rec_singleappend (list_to_word_rec l0)).
    rewrite e.
(*Um IHl anwenden zu können, muss ich das irgendwie hin bekommen, dass list_to_word_rec
abgeschlossen unter Concatenation ist. Irgendwie sowas in die Richtung.
Lemma concat_word (snoc eps w)(list_to_word_rec l) = wl *)

Lemma word_list_word_rec {A : Type} (w : @word A) : list_to_word_rec (word_to_list_rec w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
(*Lemma word_to_list w ++ x::nil = cons x w*)

(*Nach Definition von word_to_list'' - ergo albern*)
Lemma rev_word_to_list {A : Type} (w : @word A) : rev (word_to_list w) = word_to_list'' w.
Proof.
unfold word_to_list''.
reflexivity.
Qed.

Lemma list_word_list'' {A : Type} (l : list A) : word_to_list'' (list_to_word'' l) = l.
Proof.
unfold word_to_list''.
unfold list_to_word''.
induction l.
  - simpl.
    reflexivity.
  - simpl.

Lemma word_list_word'' {A : Type} (w : @word A) : list_to_word'' (word_to_list'' w) = w.