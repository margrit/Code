Require Import List.
(* Funktionen die aus der List Bibliothek importiert und hier verwendet werden sind
 - rev, app und concat. *)

(* Beispiel für ein Eingabealphabet: Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.*)

(** Die Ursprungsidee war auf Listen zu arbeiten. Da die Verfahren aus der Vorlesung
 möglichst eins zu eins abgebildet werden sollen, ist es notwendig einen induktiven Typen
 [Word] zu definieren, der, anders als bei Listen, die Zeichen am Ende der Zeichenkette anfügt.
 Da sowohl Listen als auch Wörter für die Darstellung benötigt werden, müssen die Typen
 ineinander überführbar sein. *)

(** * Definition von Wörtern: *)
Inductive Word {A : Type} : Type:=
  | eps   : @Word A
  | snoc : @Word A -> A -> @Word A.

(** Anpassung der Notation der Wörter zur Verbesserung der Lesbarkeit. *)
Notation "[ ]" := eps.
Notation "[ x ; .. ; y ]" := (snoc ( .. (snoc eps x) .. ) y).

(** ** Grundoperationen auf dem Typ [Word]: *)

(** Berechnung der Wortlänge: *)
Fixpoint word_length {A : Type} (w : @Word A) : nat :=
  match w with
    | eps          => 0
    | snoc w' x => S (word_length w')
  end.

(** Verknüpfung zweier Wörter: *)
Fixpoint concat_word {A : Type} (w1 w2 : @Word A) : @Word A :=
  match w2 with
    | eps => w1
    | snoc w x => snoc (concat_word w1 w) x
  end.

(** Ein Wort umdrehen: *)
Fixpoint word_reverse {A : Type} (w : @Word A) : @Word A  :=
  match w with
    | eps           => eps
    | snoc w' x  => concat_word (snoc eps x) (word_reverse w')
  end.

(** Map-Funktion auf Wörtern (Word ist ein Funktor) *)
Fixpoint map_word {A B : Type} (f : A -> B) (w : @Word A) : @Word B :=
 match w with
   | eps => eps
   | snoc w' x => snoc (map_word f w') (f x)
 end.

Lemma map_length_w {A B : Type} : forall (f : A -> B) (w : @Word A),
       word_length (map_word f w) = word_length w.
Proof.
intros f w.
induction w as [ | w' IHw].
- simpl. reflexivity.
- simpl. rewrite IHw. reflexivity.
Defined.


(** * Definition von Listen *)

(** In der Standardbibliothek befinden sich bereits Listenoperationen wie [concat] und [rev],
 die analog zu [concat_word] und [word_reverse] arbeiten. Zusätzlich werden noch weitere 
 Eigenschaften benötigt, die nachfolgend gezeigt werden. *)

(** ** Eigenschaften von [concat] und [rev] über Listen: *)

(** Die leere Liste [nil] ist rechtsneutral bzgl. der Konkatenation. (Per Definition ist [nil] auch
linksneutral.)*)
Lemma concat_nil {A : Type} (ls : list A) : (ls ++ nil) = ls.
Proof.
  induction ls.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHls.
    reflexivity.
Defined.

(** Die Konkatenation von Listen ist assoziativ.*)
Lemma concat_associative {A : Type} (l1 l2 l3 : list A) :
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3). 
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Defined.

(** Das Umdrehen von Listen ist ein Antihomomorphismus bzgl. der Konkatenation. *)
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

(** Das Umdrehen von Listen ist idempotent.*)
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

(** Analog zum Typen [list] werden diese Eigenschaften ebenfalls für die Operationen auf [Word]
 bewiesen.*)

(** ** Eigenschaften von [concat_word] und [word_reverse].*)

(** Das leere Wort [eps] ist linksneutral bzgl. der Konkatenation. (Per Definition ist [eps] auch
rechtsneutral.)*)
Lemma concat_word_eps {A : Type} (w : @Word A) : concat_word eps w = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(** Die Konkatenation von Wörtern ist assoziativ.*)
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

(** Das Umdrehen von Wörtern ist ein Antihomomorphismus bzgl. der Konkatenation. *)
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

(** Das Umdrehen von Wörtern ist idempotent.*)
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

(** Somit ist [Word] als Monoid mit [concat_word] als assoziativer Konkatenation 
 und [eps] als neutralem Element definiert. Bei [list] erhalten wir die gleichen Eigenschaften 
 durch [concat] als assoziative Konkatenation und [nil] als neutrales Element bzgl. der 
 Konkatenation.

 Diese Eigenschaften von Listen und Wörtern ermöglichen weitere Schlussfolgerungen
 bzgl. der Überführung von Listen in Wörtern und anders herum. *)

(**  * Eine Liste in ein Wort umwandeln.*)

(** Ein Problem, dass sich hierbei ergibt ist, dass die Typen von Listen und Wörtern auf unterschiedlich
 arbeitende Konstruktoren aufbauen. Die Liste wird von hinten nach vorn aufgebaut, indem das 
 nächste Zeichen vorn angehängt wird und der Aufbau eines Wortes ist entgegengesetzt. Wenn man
 die Umwandlung von einer Liste in ein Wort eins zu eins implementiert, erhält man die Funktion, die in
 [list_to_word] beschrieben ist.*)
Fixpoint list_to_word_simple {A : Type} (l : list A) : @Word A :=
  match l with
    | nil           => eps
    | cons x l'  => snoc (list_to_word_simple l') x
  end.

(** Das Ergebnis ist jedoch ein Wort in umgedrehter Reihenfolge. Hierbei handelt 
es sich um einen Antihomomorphismus: Das neutrale Element wird erhalten, das Bild einer Konkatenation
ist die umgekehrte Konkatenation der Bilder der Einzellisten.*)
Lemma  list_to_word_simple_antihom {A: Type} (l1 l2 : list A) :
  list_to_word_simple (l1 ++ l2) = concat_word (list_to_word_simple l2) (list_to_word_simple l1).
Proof.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Defined.

(** Um eine Liste mithilfe von [list_to_word_simple] in ein Wort unter Beachtung der Reihenfolge unzuwandeln,
 können zwei verschiedene Ansätze verwendet werden. Die Liste wird zuerst in ein Wort umgewandelt
und anschließend wird die Reihenfolge mit [word_reverse] geändert oder die Liste wird zuerst mit [rev]
umgedreht und anschließend in ein Wort umgewandelt. Da jeweils zwei Antihomomorphismen hintereinander
ausgeführt werden, sind beide entstehenden Funktionen Homomorphismen bzgl. der Konkatenationen.*)
Definition list_to_word' {A : Type} (l : list A) : @Word A := word_reverse (list_to_word_simple l).

Definition list_to_word'' {A : Type} (l : list A) : @Word A := list_to_word_simple (rev l).

(**  [list_to_word'] und [list_to_word''] basieren auf Funktionen, die durch Pattern Matching definiert sind.
Durch Auffaltung der Definitionen können auch [list_to_word'] und [list_to_word''] über Pattern Matching
definiert werden. Es stellt sich heraus, dass in beiden Fällen dieselbe Funktion [list_to_word] entsteht.
Die Gleichheiten werden in  [list_to_word_Lemma] und [list_to_word_Lemma'] gezeigt.*)
Fixpoint list_to_word {A : Type} (l : list A) : @Word A :=
match l with
  | nil           => eps
  | cons x l'  => concat_word (snoc eps x) (list_to_word l')
end.

(** [list_to_word_single] auf einelementigen Listen.*)
Lemma list_to_word_single {A : Type} (a : A) :
  list_to_word (cons a nil) = snoc eps a.
Proof.
simpl.
reflexivity.
Defined.

(** [list_to_word] ist ein Homomorphismus bzgl. Konkatenationen.*)
Lemma list_to_word_hom {A : Type} (l1 l2 : list A) :
  list_to_word (l1 ++ l2) = concat_word (list_to_word l1) (list_to_word l2).
Proof.
induction l1.
  - simpl.
    rewrite (concat_word_eps (list_to_word l2)).
    reflexivity.
  - simpl.
    rewrite IHl1.
    apply eq_sym.
    apply concat_word_associative.
Defined.

(** [list_to_word], [list_to_word'] und [list_to_word''] beschreiben dieselbe Funktion.*)
Lemma list_to_word_Lemma {A : Type} (l : list A) : 
  list_to_word l = list_to_word' l.
Proof.
unfold list_to_word'.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Defined.

Lemma list_to_word_Lemma' {A : Type} (l : list A) : 
  list_to_word l = list_to_word'' l.
Proof.
unfold list_to_word''.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite list_to_word_simple_antihom.
    rewrite IHl.
    reflexivity.
Defined.

Lemma list_to_word'_Lemma {A : Type} (l : list A) :
  list_to_word' l = list_to_word'' l.
Proof.
rewrite <- list_to_word_Lemma.
rewrite <- list_to_word_Lemma'.
reflexivity.
Defined.

(** * Ein Wort in eine Liste umwandeln: *)

(** Wie auch schon bei der Umwandlung von einer Liste in ein Wort, besteht das Problem mit der
 Reihenfolge aufgrund der Konstruktoren auch hier. Die eins zu eins Implementierung der Umwandlung
liefert die Funktion [word_to_list_simple].*)
Fixpoint word_to_list_simple {A : Type} (w : @Word A) : list A :=
  match w with
    | eps           => nil
    | snoc w' x  => cons x (word_to_list_simple w')
  end.

(** [word_to_list_simple] ist ein Antihomomorphismus bzgl. der Konkatenation. *)
Lemma  word_to_list_simple_antihom {A: Type} (w1 w2 : @Word A) :
  word_to_list_simple (concat_word w1 w2) = (word_to_list_simple w2) ++ (word_to_list_simple w1).
Proof.
induction w2.
- simpl.
  reflexivity.
- simpl.
  rewrite IHw2.
  reflexivity.
Defined.

(** Wie schon bei [list_to_word] kann bei [word_to_list] die Reihenfolge durch das Umdrehen der Liste nach der
 Umwandlung mit [rev] oder das vorhrige Umdrehen gewährleistet werden. Dies wird durch die Funktionen
 [word_to_list'] und [word_to_list''] dargestellt.*)
Definition word_to_list' {A : Type} (w : @Word A) : list A := rev (word_to_list_simple w).

Definition word_to_list'' {A : Type} (w : @Word A) : list A := word_to_list_simple (word_reverse w).

(** Es entsteht durch Auffaltung beider Definitionen dieselbe Funktion [word_to_list], siehe [list_to_word].*)
Fixpoint word_to_list {A: Type} (w : @Word A) : list A :=
  match w with
  | eps           => nil
  | snoc w' x  => app (word_to_list w') (cons x nil)
end.

(** Die Abarbeitung eines Zeichens von [word_to_list].*)
Lemma word_to_list_single {A : Type} (a : A) :
  word_to_list (snoc eps a) = cons a nil.
Proof.
simpl.
reflexivity.
Defined.

(** [word_to_list] ist ein Homomorphismus bzgl. der Konkatenation. *)
Lemma word_to_list_hom {A : Type} (w1 w2 : @Word A) :
  word_to_list (concat_word w1 w2) = word_to_list w1 ++ word_to_list w2.
Proof.
induction w2.
  - simpl.
    rewrite (concat_nil (word_to_list w1)).
    reflexivity.
  - simpl.
    rewrite IHw2.
    apply concat_associative.
Defined.

(** [word_to_list], [word_to_list'] und [word_to_list''] beschreiben dieselbe Funktion.*)
Lemma word_to_list_Lemma {A : Type} (w : @Word A) :
  word_to_list w = word_to_list' w.
Proof.
unfold word_to_list'.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma word_to_list_Lemma' {A : Type} (w : @Word A) :
  word_to_list w = word_to_list'' w.
Proof.
unfold word_to_list''.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite word_to_list_simple_antihom.
    rewrite IHw.
    reflexivity.
Defined.

Lemma word_to_list'_Lemma {A : Type} (w : @Word A) :
  word_to_list' w = word_to_list'' w.
Proof.
rewrite <- word_to_list_Lemma.
rewrite <- word_to_list_Lemma'.
reflexivity.
Defined.

(** [list_to_word_simple] und [word_to_list_simple*] sind zueinander inverse Isomorphismen.*)
Lemma list_word_list_simple {A : Type} (l : list A) : word_to_list_simple (list_to_word_simple l) = l.
Proof.
induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma word_list_word_simple {A : Type} (w : @Word A) : list_to_word_simple (word_to_list_simple w) = w.
Proof.
induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Qed.

(** [list_to_word] und [word_to_list*] sind zueinander inverse Isomorphismen.*)

Lemma list_word_list {A : Type} (l : list A) : word_to_list (list_to_word l) = l.
Proof.
rewrite list_to_word_Lemma.
rewrite word_to_list_Lemma'.
unfold list_to_word'.
unfold word_to_list''.
rewrite word_reverse_idempotent.
apply list_word_list_simple.
Defined.

Lemma word_list_word {A : Type} (w : @Word A) : list_to_word (word_to_list w) = w.
Proof.
rewrite list_to_word_Lemma.
rewrite word_to_list_Lemma'.
unfold list_to_word'.
unfold word_to_list''.
rewrite word_list_word_simple.
apply word_reverse_idempotent.
Defined.


(** Hilfsfunktionen *)

(** Das n-te Element eines Worts, falls n < word_length, sonst None *)
Fixpoint nth_error_w {A : Type} (w : @Word A) (n : nat) : option A :=
 match n, w with
  | _   , eps       => None
  | 0   , snoc _ x  => Some x
  | S n', snoc w' _ => nth_error_w w' n'
 end.

Fixpoint sublist {A : Type} (l : list A) (i j : nat) : option (list A) := 
 match i, j, l with
  | S i', S j', (x :: l') => match sublist l' i' j' with
                              | None     => None
                              | Some l'' => Some l''
                             end 
  | 0   , S j', (x :: l') => match sublist l' 0 j' with
                              | None => None
                              | Some l'' => Some (x :: l'')
                             end
  | 0   , 0, _            => Some nil
  | _, _, _               => None
 end.


(** Teilwort von Index i bis Index j, falls i < j < word_length, Index rueckwaerts! *)
Definition subword {A : Type} (w : @Word A) (i j : nat) : option (@Word A) := 
 match sublist (word_to_list w) i j with
  | None => None
  | Some l => Some (list_to_word l)
 end.


(* Lemmata *)


Lemma S_plus_1' : forall n,  (S n = n + 1).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Defined.

Lemma wl_pres_length {A : Type} (w : @Word A) : length (word_to_list w) = word_length w.
Proof.
induction w.
- simpl. reflexivity.
- simpl.
  SearchAbout length.
  rewrite app_length.
  simpl. 
  rewrite <- S_plus_1'. 
  rewrite IHw. reflexivity.
Defined.
 