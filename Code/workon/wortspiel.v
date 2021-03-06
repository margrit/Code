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
(*Eigenschaften von concat und rev über Listen*)

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
    pose (rev_concat (rev ls) (a0 :: nil)).
    rewrite e.
    rewrite IHls.
    simpl.
    reflexivity.
Defined.

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

Eval compute in (list_word_list (cons h(cons a(cons l (cons l nil))))).

Lemma word_list_word {A : Type} (w : @word A) : list_to_word (word_to_list w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Qed.

Eval compute in (word_list_word (snoc (snoc (snoc (snoc (snoc eps h) a) l) l) o)).

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

Lemma word_to_list_singleappend {A : Type} (x : A) (w : @word A) :
  word_to_list (concat_word (snoc eps x) w) = app (word_to_list w) (x :: nil).
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Print app.
Eval compute in (list_to_word_rec((cons l nil) ++ (a :: nil))).
Eval compute in (list_to_word((cons l nil) ++ (a :: nil))).
Eval compute in (list_to_word_singleappend( (cons l nil) ++ (a :: nil))).
Eval compute in (concat_word (snoc eps a) (snoc eps l)).

(*  | cons x l'  => concat_word (snoc eps x) (list_to_word_rec l')*)
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

(*word_to_list_rec (concat_word (snoc eps a0) (list_to_word_rec l0)) = a0 :: l0*)
(*  | snoc w' x  => app (word_to_list_rec w') (cons x nil)*)
Lemma word_to_list_rec_singleappend {A : Type} (x : A) (w : @word A):
word_to_list_rec (concat_word (snoc eps x) w)  = app (cons x nil) (word_to_list_rec w).
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma list_word_list_rec {A : Type} (l : list A) : word_to_list_rec (list_to_word_rec l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    pose (word_to_list_rec_singleappend a0 (list_to_word_rec l0)).
    rewrite e.
    rewrite IHl.
    simpl.
    reflexivity.
Defined.

Lemma word_list_word_rec {A : Type} (w : @word A) : list_to_word_rec (word_to_list_rec w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    pose (list_to_word_rec_singleappend a0 (word_to_list_rec w)).
    rewrite e.
    rewrite IHw.
    simpl.
    reflexivity.
Defined.
(*Lemma word_to_list w ++ x::nil = cons x w*)

(*Nach Definition von word_to_list'' - ergo albern*)
Lemma rev_word_to_list {A : Type} (w : @word A) : rev (word_to_list w) = word_to_list'' w.
Proof.
unfold word_to_list''.
reflexivity.
Qed.

Lemma word_to_list''_singleappend {A : Type} (x : A) (w : @word A):
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

(*weitere Lemmata über die Isomorphie zwischen list_to_word / '' / ''' / rec*)
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
    pose (ltwsa := list_to_word_singleappend a0 (rev l0)).
    rewrite ltwsa.
    reflexivity.
Defined.

(*weitere Lemmata über die Isomorphie zwischen word_to_list / '' / ''' / rec*)
Lemma word_to_list_Lemma {A : Type} (w : @word A) :
  word_to_list''' w = word_to_list'' w.
Proof.
unfold word_to_list'''.
unfold word_to_list''.
induction w.
 - simpl.
   reflexivity.
  - simpl.
    rewrite <- IHw.
    pose (wtl := word_to_list_singleappend a0 (word_reverse w)).
    rewrite wtl.
    reflexivity.
Defined.

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
    pose (ltw'sa := list_to_word_singleappend a0 (rev l0)).
    rewrite ltw'sa.
    reflexivity.
Defined.

Lemma word_to_list'_Lemma {A : Type} (w : @word A) :
  word_to_list'' w = word_to_list''' w.
Proof.
unfold word_to_list'''.
unfold word_to_list''.
induction w.
 - simpl.
   reflexivity.
  - simpl.
    rewrite IHw.
    pose (wtl' := word_to_list_singleappend a0 (word_reverse w)).
    rewrite wtl'.
    reflexivity.
Defined.

Lemma word_list_word'' {A : Type} (w : @word A) : list_to_word'' (word_to_list'' w) = w.
Proof.
unfold word_to_list''.
pose (ltw'L := list_to_word'_Lemma (rev (word_to_list w))).
rewrite ltw'L.
unfold list_to_word'''.
pose (revip := rev_idempotent (word_to_list w)).
rewrite revip.
apply word_list_word.
Defined.

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

