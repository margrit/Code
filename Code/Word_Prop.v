Require Import List.
(* Funktionen die aus der List Bibliothek importiert und hier verwendet werden sind
 - rev, app und concat. *)

(*Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.*)

(** Die Ursprungsidee war auf Listen zu arbeiten. Da die Verfahren aus der Vorlesung
 möglichst eins zu eins abgebildet werden sollen, ist es notwendig einen induktiven Typen
 [Word] zu definieren, der, anders als bei Listen, die Zeichen am Ende der Zeichenkette anfügt.
 Da sowohl Listen als auch Wörter für die Darstellung benötigt werden, müssen die Typen
 ineinander überführbar sein. *)

(** * Definition von Wörtern: *)
Inductive Word {A : Type} : Type:=
  | eps   : @Word A
  | snoc : @Word A -> A -> @Word A.

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

(** * Definition von Listen *)

(** In der Standardbibliothek befinden sich bereits Listenoperationen wie [concat] und [rev],
 die analog zu [concat_word] und [word_reverse] arbeiten. Zusätzlich werden noch weitere 
 Eigenschaften benötigt, die nachfolgend gezeigt werden. *)

(** ** Eigenschaften von [concat] und [rev] über Listen: *)

(** Die leere Liste [nil] ist rechtsneutral bzgl. der Konkatenation.*)
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

(** Das leere Wort [eps] ist linksneutral bzgl. der Konkatenation. *)
Lemma concat_word_eps {A : Type} (w : @Word A) : concat_word eps w = w.
Proof.
  induction w.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

(** Das leere Wort [eps] ist rechtsneutral bzgl. der Konkatenation. *)
Lemma concat_eps_word  {A : Type} (w : @Word A) : concat_word w eps = w.
Proof.
simpl.
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
 [list_to_word] beschrieben ist. Das Ergebis ist jedoch ein Wort in umgedrehter Reihenfolge. Hierbei
 handelt es sich um einen Antihomomorphismus, da zwar das neutrale Element enthalten ist, die
 Konkatenation aber fehlt.*)
Fixpoint list_to_word {A : Type} (l : list A) : @Word A :=
  match l with
    | nil           => eps
    | cons x l'  => snoc (list_to_word l') x
  end.

(** Um eine Liste mithilfe von [list_to_word] in ein Wort unter Beachtung der Reihenfolge unzuwandeln,
 können zwei verschiedene Ansätze verwendet werden. Die Liste wird zuerst in ein Wort umgewandelt
und anschließend wird die Reihenfolge mit [word_reverse] geändert oder die Liste wird zuerst mit [rev]
umgedreht und anschließend in ein Wort umgewandelt. *)
Definition list_to_word'' {A : Type} (l : list A) : @Word A := word_reverse (list_to_word l).

Definition list_to_word''' {A : Type} (l : list A) : @Word A := list_to_word (rev l).

(**  Um [list_to_word] als homomorphe Abbildung zu definieren, muss die Konkatenation bzgl. des
 entstehenden Monoides berücksichtigt werden. Dadurch wird die Reihenfolge bei der Umwandlung
 in [list_to_word_rec] eingehalten*)
Fixpoint list_to_word_rec {A : Type} (l : list A) : @Word A :=
match l with
  | nil           => eps
  | cons x l'  => concat_word (snoc eps x) (list_to_word_rec l')
end.

(** #########*)
Lemma list_to_word_rec_single {A : Type} (a : A) :
  list_to_word_rec (cons a nil) = snoc eps a.
Proof.
simpl.
reflexivity.
Defined.

(** [list_to_word] ist ein Antihomomorphismus bzgl. der Konkatenation. *)
Lemma  list_to_word_antihom {A: Type} (l1 l2 : list A) :
  list_to_word (l1 ++ l2) = concat_word (list_to_word l2) (list_to_word l1).
Proof.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Defined.

(** Um ein zusätzliches Zeichen in [list_to_word] bzw. [list_to_word_rec] zu verarbeiten kann das
 Zeichen erst mit der Liste verknüpft und dann in ein Wort umgewandelt werden oder die
 Ursprungsliste wird in ein Wort umgewandelt und mit [concat_word] das zusätzliche Zeichen
 angehängt. Bei [list_to_word_singleappend] ist zu beachten, dass das entstehende Wort in gedrehter
 Reihenfolge abgebildet wird und somit das zusätzliche Zeichen vorn angehängt werden muss.
 Bei [list_to_word_rec_singleappend] wird das zusätzliche Zeichen hinten an das Wort gehängt.*)
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

(** [list_to_word_rec_append] definiert eine Funktion, in der zwei Zeichenketten als Liste
 konkateniert werden, um sie anschließend in ein Wort umzuwandeln bzw. zwei Listen in zwei
 Wörter umwandelt und dann die beiden Wörter miteinander verknüpft.*)
Lemma list_to_word_rec_append {A : Type} (l1 l2 : list A) :
  list_to_word_rec (l1 ++ l2) = concat_word (list_to_word_rec l1) (list_to_word_rec l2).
Proof.
induction l1.
  - simpl.
    rewrite (concat_word_eps (list_to_word_rec l2)).
    reflexivity.
  - simpl.
    rewrite IHl1.
    apply eq_sym.
    apply concat_word_associative.
Defined.

(** Die Funktionen [list_to_word_rec] und [list_to_word''], sowie [list_to_word'''] und [list_to_word'']
 liefern das gleiche Ergebnis, welches in den Lemata [list_to_word_rec_Lemma], [list_to_word_Lemma]
 bzw. [list_to_word'_Lemma] bewiesen ist. Eines der beiden letzteren Lemmata kann noch entfernt
 werden. Dies wird sich im Laufe der Arbeit herausstellen, welche Richtung häufiger Verwendung findet.*)
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

(** * Ein Wort in eine Liste umwandeln: *)

(** Wie auch schon bei der Umwandlung bei einer Liste in einem Wort, besteht das Problem mit der
 Reihenfolge aufgrund der Konstruktoren auch hier. Daher entsteht durch die eins zu eins Implementierung
 der Umwandling von [word_to_list] eine Liste in umgedrehter Reihenfolge.*)
Fixpoint word_to_list {A : Type} (w : @Word A) : list A :=
  match w with
    | eps           => nil
    | snoc w' x  => cons x (word_to_list w')
  end.

(** Wie schon bei [list_to_word] kann bei [word_to_list] die Reihenfolge durch das drehen der Liste nach der
 Umwandlung mit [rev] oder das zuvorige Drehen gewährleistet werden. Dies wird durch die Funktionen
 [word_to_list''] und [word_to_list'''] dargestellt.*)
Definition word_to_list'' {A : Type} (w : @Word A) : list A := rev (word_to_list w).

Definition word_to_list''' {A : Type} (w : @Word A) : list A := word_to_list (word_reverse w).

(** Analog zu [list_to_word_rec] wird die Reihenfolge bei [word_to_list_rec] durch die Konkatenation von
 Listen durch [app] erhalten.*)
Fixpoint word_to_list_rec {A: Type} (w : @Word A) : list A :=
  match w with
  | eps           => nil
  | snoc w' x  => app (word_to_list_rec w') (cons x nil)
end.

(** Die Abarbeitung eines Zeichens von [word_to_list_rec].*)
Lemma word_to_list_rec_single {A : Type} (a : A) :
  word_to_list_rec (snoc eps a) = cons a nil.
Proof.
simpl.
reflexivity.
Defined.

(** [word_to_list] ist ein Antihomomorphismus bzgl. der Konkatenation. *)
Lemma  word_to_list_antihom {A: Type} (w1 w2 : @Word A) :
  word_to_list (concat_word w1 w2) = (word_to_list w2) ++ (word_to_list w1).
Proof.
induction w2.
- simpl.
  reflexivity.
- simpl.
  rewrite IHw2.
  reflexivity.
Defined.

(** Analog zu [list_to_word_singleappend] und [list_to_word_rec_singleappend] wird das Wort zuerst
 in eine Liste umgewandelt und dann das zusätzliche Zeichen verarbeitet oder anders herum. In
 Abhängigkeit welcher Weg gewählt wird, wird das Zeichen hinten an die Liste angehängt bzw. am
 Wort um die Reihenfolge zu wahren.*)
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

(** Die Konkatenation von Wörtern und anschließender Umwandlung in einer Liste bzw.
 erst die einzelnen Wörter in eine Liste umzuwandeln und dann zu verknüpfen wird durch die
 Funktion [word_to_list_rec_append] beschrieben.*)
Lemma word_to_list_rec_append {A : Type} (w1 w2 : @Word A) :
  word_to_list_rec (concat_word w1 w2) = word_to_list_rec w1 ++ word_to_list_rec w2.
Proof.
induction w2.
  - simpl.
    rewrite (concat_nil (word_to_list_rec w1)).
    reflexivity.
  - simpl.
    rewrite IHw2.
    apply concat_associative.
Defined.

(*### andere Formulierung?###*)
(** Die Funktionen [word_to_list_rec] und [word_to_list''], sowie [word_to_list'''] und [word_to_list'']
 liefern das gleiche Ergebnis, welches in den Lemata [word_to_list_rec_Lemma], [word_to_list_Lemma]
 bzw. [word_to_list'_Lemma] bewiesen ist. Eines der beiden letzteren Lemmata kann noch entfernt
 werden. Dies wird sich im Laufe der Arbeit herausstellen, welche Richtung häufiger Verwendung findet.*)
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

(** Um die Schreibweise innerhalb der Kommentare etwas zu vereinfachen, werden nachfolgend die
 Funktionen [list_to_word], [list_to_word''], [list_to_word'''] und [list_to_word_rec] durch [list_to_word*]
 bzw. [word_to_list], [word_to_list'], [word_to_list''] und [word_to_list_rec] durch [word_to_list*] benannt.*)

(** Mit den bisher definierten Funktionen können weitere Eigenschaften abgeleitet werden.
 Wendet man die Funktionen [list_to_word*] und [word_to_list*] aufeinander an, erhält man die
 Identität.*)
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
