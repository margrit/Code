Require Import List.

Lemma concat_nil {A : Type} (ls : list A) : (ls ++ nil) = ls.
Proof.
  induction ls.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHls.
    reflexivity.
Defined.

Lemma concat_associative {A : Type} (l1 l2 l3 : list A) : 
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3). 
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Defined.

Lemma rev_concat {A : Type} (l1 l2 : list A) : 
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  induction l1.
  - assert (rev nil = @nil A).
    + simpl; reflexivity.
    + rewrite H.
    pose (concat_nil (rev l2)).
    rewrite e.
    simpl; reflexivity.
  - simpl.
    rewrite IHl1.
    apply concat_associative.
Defined.

Lemma rev_idempotent {A : Type} (ls : list A) : rev (rev ls) = ls.
Proof.
  induction ls.
  - simpl.
    reflexivity.
  - simpl.
    pose (rev_concat (rev ls) (a :: nil)).
    rewrite e.
    rewrite IHls.
    simpl.
    reflexivity.
Defined.

(* aus wortspiel.v ... alles hier sollte dann
   sowieso irgendwann dorthin wandern.           *)

Inductive word {A : Type} : Type:= 
| eps : @word A 
| snoc : @word A -> A -> @word A.

Fixpoint concat {A : Type} (w1 w2 : @word A) : @word A :=
match w2 with 
| eps => w1
| snoc w x => snoc (concat w1 w) x
end.

(* Ein Wort umdrehen: *)
Fixpoint word_reverse {A : Type} (w : @word A) : @word A  :=
match w with
| eps           => eps
| snoc w' x  => concat (snoc eps x) (word_reverse w')
end.

(* Eine Liste in ein Wort umwandeln: *)
Fixpoint list_to_word {A : Type} (l : list A) : @word A :=
match l with
| nil           => eps
| cons x l'  => snoc (list_to_word l') x
end.


(*Eine Liste in ein Wort umwandeln unter Beachtung der Reihenfolge.*)
Definition list_to_word'' {A : Type} (l : list A) : @word A := 
  word_reverse (list_to_word l).

(************* Ende Kopie aus wortspiel.v *)

(* Hier noch eine andere Variante von list_to_word'' 
   Langsam werden es zuviele Striche... *)

Definition list_to_word''' {A : Type} (l : list A) : @word A := 
  list_to_word (rev l).


Lemma list_to_word_singleappend {A : Type} (a : A) (l : list A) :
  list_to_word (l ++ (a :: nil)) = concat (snoc eps a) (list_to_word l).
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Defined.

Lemma list_to_word_Lemma {A : Type} (l : list A) :
  list_to_word''' l = list_to_word'' l.
Proof.
  unfold list_to_word'''.
  unfold list_to_word''.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHl.
    pose (ltwsa := list_to_word_singleappend a (rev l)).
    rewrite ltwsa.
    reflexivity.

