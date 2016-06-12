Require Import List.
(* Funktionen die aus der List Bibliothek importiert und hier verwendet werden sind
 - rev, app und concat. *)

(*Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.*)

(* Definition von Wörtern*)
Inductive Word {A : Type} : Type:=
  | eps   : @Word A
  | snoc : @Word A -> A -> @Word A.

(* Berechnung der Wortlänge *)
Fixpoint word_length {A : Type} (w : @Word A) : nat :=
  match w with
    | eps          => 0
    | snoc w' x => S (word_length w')
  end.

(* Verknüpfung zweier Wörter*)
Fixpoint concat_word {A : Type} (w1 w2 : @Word A) : @Word A :=
  match w2 with
    | eps => w1
    | snoc w x => snoc (concat_word w1 w) x
  end.

(* Ein Wort umdrehen: *)
Fixpoint word_reverse {A : Type} (w : @Word A) : @Word A  :=
  match w with
    | eps           => eps
    | snoc w' x  => concat_word (snoc eps x) (word_reverse w')
  end.

(* Eigenschaften von concat und rev über Listen*)

(* Eine Liste verknüpft mit der leeren Liste ergibt die Ursprungsliste.*)
Lemma concat_nil {A : Type} (ls : list A) : (ls ++ nil) = ls.
Proof.
  induction ls.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHls.
    reflexivity.
Defined.

(* Die Konkatenation von Listen ist assoziativ.*)
Lemma concat_associative {A : Type} (l1 l2 l3 : list A) :
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3). 
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Defined.

(* Gleichheit von der Konkatenation und das Umdrehen von Listen.*)
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

(* Das Drehen von Listen ist idempotent.*)
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

(* Eigenschaften von concat_word und word_reverse.*)

(* Ein Wort verknüpft mit dem leeren Wort ergibt das Ursprungswort.*)
Lemma concat_word_eps {A : Type} (w : @Word A) : concat_word eps w = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(* Die Konkatenation von Wörtern ist assoziativ.*)
Lemma concat_word_associative {A : Type} (w1 w2 w3 : @Word A) :
  concat_word (concat_word w1 w2) w3 = concat_word w1 (concat_word w2 w3).
Proof.
  induction w3.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw3.
    reflexivity.
Defined.

(* Gleichheit von der Konkatenation und das Umdrehen von Wörtern.*)
Lemma word_reverse_concat_word {A : Type} (w1 w2 : @Word A) :
      word_reverse (concat_word w1 w2) = concat_word (word_reverse w2) (word_reverse w1).
Proof.
induction w2.
  - assert (word_reverse eps = @eps A).
    + simpl; reflexivity.
    + rewrite H.
       simpl.
       pose (concat_word_eps (word_reverse w1)) as con_nil.
       rewrite con_nil.
       reflexivity.
  - simpl.
    rewrite IHw2.
    apply eq_sym.
    apply concat_word_associative.
Defined.

(* Das Drehen von Wörtern ist idempotent.*)
Lemma word_reverse_idempotent {A : Type} (w : @Word A) : word_reverse (word_reverse w) = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_reverse_concat_word (snoc eps a) (word_reverse w) ).
    rewrite e.
    rewrite IHw.
    simpl.
    reflexivity.
Defined.

(* Eine Liste in ein Wort umwandeln.*)

(* Hierbei wird die Liste in ein Wort umgewandelt, allerdings wird das Wort auch in der umgedrehten 
Reihenfolge wieder zusammengesetzt.*)
Fixpoint list_to_word {A : Type} (l : list A) : @Word A :=
  match l with
    | nil           => eps
    | cons x l'  => snoc (list_to_word l') x
  end.

(* Eine Liste in ein Wort umwandeln unter Beachtung der Reihenfolge und mithilfe von list_to_word.
Hierbei gibt es zwei Varianten. Die Liste zuerst in ein Wort umwandeln und dann die Reihenfolge ändern
oder zuerst die Liste umdrehen und dann in ein Wort umwandeln.*)
Definition list_to_word'' {A : Type} (l : list A) : @Word A := word_reverse (list_to_word l).

Definition list_to_word''' {A : Type} (l : list A) : @Word A := list_to_word (rev l).

(* Rekursive Funktion, die eine Liste in ein Wort umwandelt und dabei über Pattern Matching die
richtige Reihenfolge beibehält.*)
Fixpoint list_to_word_rec {A : Type} (l : list A) : @Word A :=
match l with
  | nil           => eps
  | cons x l'  => concat_word (snoc eps x) (list_to_word_rec l')
end.

(* Ein zusätzliches Zeichen in list_to_word verarbeiten oder erst die Liste in ein Wort umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
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

(* Ein zusätzliches Zeichen in list_to_word_rec verarbeiten oder erst die Liste in ein Wort umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
Lemma list_to_word_rec_singleappend {A : Type} (a : A) (l : list A) :
  list_to_word_rec (l ++ (a :: nil)) = concat_word (list_to_word_rec l) (snoc eps a).
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Defined.

(* Ein zusätzliches Zeichen in list_to_word'' verarbeiten oder erst die Liste in ein Wort umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
Lemma list_to_word''_singleappend {A : Type} (a : A) (l : list A) :
  list_to_word'' (l ++ (a :: nil)) = concat_word (list_to_word'' l) (snoc eps a).
Proof.
unfold list_to_word''.
induction l.
  - simpl.
    reflexivity.
   - simpl.
     rewrite IHl.
    reflexivity.
Defined.

(* Isomorphie zwischen list_to_word_rec und list_to_word''.*)
Lemma list_to_word_rec_Lemma {A : Type} (a : A) (l : list A) : 
  list_to_word_rec l = list_to_word'' l.
Proof.
unfold list_to_word''.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Defined.

(* Isomorphie zwischen list_to_word''' und list_to_word''. Hierbei kann eins der beiden Lemmata noch
 entfernt werden. Es wird sich im Laufe der Arbeit herausstellen, welche der beiden Richtungen
 häufiger Anwendung findet.*)
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
Defined.

Lemma list_to_word'_Lemma {A : Type} (l : list A) :
  list_to_word'' l = list_to_word''' l.
Proof.
  unfold list_to_word'''.
  unfold list_to_word''.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    pose (ltw'sa := list_to_word_singleappend a (rev l)).
    rewrite ltw'sa.
    reflexivity.
Defined.

(* Ein Wort in eine Liste umwandeln: *)
Fixpoint word_to_list {A : Type} (w : @Word A) : list A :=
  match w with
    | eps           => nil
    | snoc w' x  => cons x (word_to_list w')
  end.

(* Eine Wort in eine Liste umwandeln unter Beachtung der Reihenfolge und mithilfe von word_to_list.
Hierbei gibt es zwei Varianten. Das Wort zuerst in eine Liste umwandeln und dann die Reihenfolge ändern
oder zuerst das Wort umdrehen und dann in eine Liste umwandeln.*)
Definition word_to_list'' {A : Type} (w : @Word A) : list A := rev (word_to_list w).

Definition word_to_list''' {A : Type} (w : @Word A) : list A := word_to_list (word_reverse w).

(* Rekursive Funktion, die ein Wort in eine Liste umwandelt und dabei über Pattern Matching die
richtige Reihenfolge beibehält.*)
Fixpoint word_to_list_rec {A: Type} (w : @Word A) : list A :=
  match w with
  | eps           => nil
  | snoc w' x  => app (word_to_list_rec w') (cons x nil)
end.

(* Ein zusätzliches Zeichen in word_to_list verarbeiten oder erst das Wort in eine Liste umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
Lemma word_to_list_singleappend {A : Type} (x : A) (w : @Word A) :
  word_to_list (concat_word (snoc eps x) w) = app (word_to_list w) (x :: nil).
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(* Ein zusätzliches Zeichen in word_to_list_rec verarbeiten oder erst das Wort in eine Liste umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
Lemma word_to_list_rec_singleappend {A : Type} (x : A) (w : @Word A):
word_to_list_rec (concat_word (snoc eps x) w)  = app (cons x nil) (word_to_list_rec w).
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(* Ein zusätzliches Zeichen in word_to_list'' verarbeiten oder erst das Wort in eine Liste umwandeln
 und dann das zusätzliche Zeichen anhängen.*)
Lemma word_to_list''_singleappend {A : Type} (x : A) (w : @Word A) :
word_to_list'' (concat_word (snoc eps x) w)  = app (cons x nil) (word_to_list'' w).
Proof.
unfold word_to_list''.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(* Isomorphie zwischen word_to_list_rec und word_to_list''.*)
Lemma word_to_list_rec_Lemma {A : Type} (x : A) (w : @Word A) :
  word_to_list_rec w = word_to_list'' w.
Proof.
unfold word_to_list''.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(* Isomorphie zwischen word_to_list''' und word_to_list''. Hierbei kann eins der beiden Lemmata noch
 entfernt werden. Es wird sich im Laufe der Arbeit herausstellen, welche der beiden Richtungen
 häufiger Anwendung findet.*)
Lemma word_to_list_Lemma {A : Type} (w : @Word A) :
  word_to_list''' w = word_to_list'' w.
Proof.
unfold word_to_list'''.
unfold word_to_list''.
induction w.
 - simpl.
   reflexivity.
  - simpl.
    rewrite <- IHw.
    pose (wtl := word_to_list_singleappend a (word_reverse w)).
    rewrite wtl.
    reflexivity.
Defined.

(*Wird in einem Beweis verwendet*)
Lemma word_to_list'_Lemma {A : Type} (w : @Word A) :
  word_to_list'' w = word_to_list''' w.
Proof.
unfold word_to_list'''.
unfold word_to_list''.
induction w.
 - simpl.
   reflexivity.
  - simpl.
    rewrite IHw.
    pose (wtl' := word_to_list_singleappend a (word_reverse w)).
    rewrite wtl'.
    reflexivity.
Defined.

(* Die Umwandlung einer Liste in einem Wort und zurück ergibt die Identität.*)
Lemma list_word_list {A : Type} (l : list A) : word_to_list (list_to_word l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma list_word_list'' {A : Type} (l : list A) : word_to_list'' (list_to_word'' l) = l.
Proof.
unfold list_to_word''.
pose (wtl'L := word_to_list'_Lemma (word_reverse (list_to_word l))).
rewrite wtl'L.
unfold word_to_list'''.
pose (wrip := word_reverse_idempotent (list_to_word l)).
rewrite wrip.
apply list_word_list.
Defined.

Lemma list_word_list_rec {A : Type} (l : list A) : word_to_list_rec (list_to_word_rec l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_to_list_rec_singleappend a (list_to_word_rec l)).
    rewrite e.
    rewrite IHl.
    simpl.
    reflexivity.
Defined.

(* Die Umwandlung eines Wortes in einer Liste und zurück ergibt die Identität.*)
Lemma word_list_word {A : Type} (w : @Word A) : list_to_word (word_to_list w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Qed.

Lemma word_list_word'' {A : Type} (w : @Word A) : list_to_word'' (word_to_list'' w) = w.
Proof.
unfold word_to_list''.
pose (ltw'L := list_to_word'_Lemma (rev (word_to_list w))).
rewrite ltw'L.
unfold list_to_word'''.
pose (revip := rev_idempotent (word_to_list w)).
rewrite revip.
apply word_list_word.
Defined.

Lemma word_list_word_rec {A : Type} (w : @Word A) : list_to_word_rec (word_to_list_rec w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    pose (list_to_word_rec_singleappend a (word_to_list_rec w)).
    rewrite e.
    rewrite IHw.
    simpl.
    reflexivity.
Defined.
