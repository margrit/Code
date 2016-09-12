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

(** Einheit der Word-Monade: *)
Definition unit_w {A : Type} (a : A) : @Word A := snoc eps a.

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

Lemma commute_snoc_concat_w {A} (w w': @Word A) (a : A) :
  concat_word (snoc w a) w' = concat_word w (concat_word (snoc eps a) w').
Proof.
destruct w; simpl.
- rewrite concat_word_eps. reflexivity.
- induction w'; simpl.
  + reflexivity.
  + rewrite IHw'.
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

Lemma word_reverse_snoc {A : Type} (w : @Word A) (a : A) :
            word_reverse (snoc w a) = concat_word [a] (word_reverse w). 
Proof.
  simpl.
  reflexivity.
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

(** [word_reverse] ist injektiv.*)
Lemma word_reverse_injective {A : Type} (w1 w2 : @Word A) :
      word_reverse w1 = word_reverse w2 -> w1 = w2.
Proof.
intro revEq.
apply (f_equal word_reverse) in revEq.
rewrite <- (word_reverse_idempotent w1).
rewrite <- (word_reverse_idempotent w2).
exact revEq.
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


(* Weitere Lemmata zu Word-List und List-Word-Umwandlungen *)

Lemma lw_pres_eq {A} (l : list A) : forall (w : @Word A),
              l = word_to_list w -> list_to_word l = w.
Proof.
intros w eq.
rewrite <- word_list_word.
rewrite eq. reflexivity.
Defined.

Lemma wl_pres_length {A : Type} (w : @Word A) :
             length (word_to_list w) = word_length w.
Proof.
induction w.
- simpl. reflexivity.
- simpl.
  rewrite app_length.
  simpl.
  rewrite <- plus_n_Sm. 
  rewrite <- plus_n_O.
  rewrite IHw. 
reflexivity.
Defined.

Lemma lw_concat {A} (l1 l2: list A) (a : A):
              { w1 :  @Word A & { w2 : @Word A &
                concat_word (list_to_word l1) (list_to_word (a :: l2))  
                = concat_word (snoc w1 a) w2 } }. 
Proof.
exists (list_to_word l1).
exists (list_to_word l2).
simpl.
rewrite <- commute_snoc_concat_w.
reflexivity.
Defined.



(* --------------------------------------------------------------------------*)

(** ** Inits und Tails *)

(* --------------------------------------------------------------------------*)

(* TODO-Frage: Waere ein Typsynonym fuer @Word (@Word X) sinnvoll? *)


(* unbenutzt, aber ok als Standard ? *)
Fixpoint tails_w {X : Type} (w : @Word X) : @Word (@Word X) :=
  match w with
  | eps       => snoc eps eps
  | snoc xs x => snoc (map_word (fun w => snoc w x) (tails_w xs)) eps 
  end.

(** * Verschiedene inits-Varianten *)

Fixpoint inits_l {X : Type} (l : list X) : list (list X) :=
  match l with
  | nil       => nil :: nil
  | x :: xs => nil :: map (cons x) (inits_l xs)
  end.

(* die fuer PL_w benutzte benutzte Variante *)
Fixpoint inits_w {X : Type} (w : @Word X) : @Word (@Word X) :=
 match w with
  | eps => snoc eps eps
  | snoc w' x => snoc (inits_w w') w
 end.

Definition inits_w'{X : Type} (w : @Word X) : @Word (@Word X) :=
 list_to_word (map (list_to_word) (inits_l (word_to_list w))).


Fixpoint inits_w''{X : Type} (w : @Word X) : @Word (@Word X) :=
 match w with
  | eps       => snoc eps eps
  | snoc w' x => 
        concat_word (snoc eps eps) 
                    (map_word (fun w'' => concat_word w'' (snoc eps x)) 
                              (inits_w w'))
 end.

(* Beispiele: *)
Eval compute in (inits_w (snoc (snoc ( snoc eps 1 ) 2) 3)).
Eval compute in (tails_w (snoc (snoc ( snoc eps 1 ) 2) 3)).
Eval compute in (inits_l nil : list (list nat)).


Definition inits_list_w {X : Type} (w : @Word X) : list (@Word X) :=
 map (list_to_word) (inits_l (word_to_list w)).

Eval compute in (inits_list_w (snoc (snoc ( snoc eps 1 ) 2) 3)).


Fixpoint removelast_w {A} (w : @Word A) :=
match w with
|eps => eps
|snoc w' _ => w'
end.


(* --------------------------------------------------------------------------*)

(** * Lemmata zu inits, concat, map *)

(* --------------------------------------------------------------------------*)

Lemma inits_len_l : forall X : Type, forall l : list X,
  length (inits_l l) = S (length l).
Proof.
  induction l as [ | x l' IHl].
  - simpl.
    reflexivity.
  - simpl.
    rewrite map_length.
    rewrite IHl.
    reflexivity.
Defined.

Lemma inits_len_w : forall X : Type, forall w : @Word X,
  word_length (inits_w w) = S (word_length w).
Proof.
  intros X w.
  induction w as [ | w' IHw x].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHw.
    reflexivity.
Defined.

Lemma commute_inits_concat_w {A} (w w': @Word A) :
  inits_w (concat_word w w') 
  = concat_word (removelast_w (inits_w w)) 
                (map_word (concat_word w) (inits_w w')).
Proof.
induction w'.
- simpl. induction w.
  + simpl. reflexivity.
  + simpl (inits_w (snoc w a)).
    simpl (removelast_w (snoc (inits_w w) (snoc w a))).
    reflexivity.
- simpl. rewrite IHw'.
  reflexivity.
Defined.

Lemma commute_concat_map_w {A B} (w w': @Word A) (f : A -> B) :
  map_word f (concat_word w w') = concat_word (map_word f w) (map_word f w').
Proof.
induction w'.
- simpl. reflexivity.
- simpl. rewrite IHw'. reflexivity.
Defined.


Lemma commute_removelast_map_w {A B} (w : @Word A) (f : A -> B) :
  map_word f (removelast_w w) = removelast_w (map_word f w).
Proof.
induction w; simpl;reflexivity.
Defined.


Lemma inits_last_w {A : Type} (w : @Word A) : 
      inits_w w = snoc (removelast_w (inits_w w)) w.
Proof.
destruct w; simpl; reflexivity.
Defined.


Lemma app_length_w {A : Type} : forall (w w' : @Word A), 
              word_length (concat_word w w') = word_length w + word_length w'.
Proof.
intros w w'.
induction w'.
- simpl.
  rewrite <- plus_n_O.
  reflexivity.
- simpl.
  rewrite <- plus_n_Sm.
  rewrite IHw'.
  reflexivity.
Defined.


Lemma absurd_eps_eq_concat_snoc {A : Type} (w w' : @Word A) (a : A) : 
       eps = concat_word (snoc w a) w' -> False.
Proof.
intro eps_eq_waw'.
destruct w'; 
simpl in eps_eq_waw';
inversion eps_eq_waw'.
Defined. 


Lemma ex_snoc_map {A B : Type} (w : @Word A) (v : @Word B) (b : B) (f : A -> B) : 
             map_word f w = snoc v b -> 
               { w' : @Word A & { a : A & 
                ((w = snoc w' a) * (map_word f w' = v) * (b = f a))%type } }.
Proof.
destruct w as [| w' a']; intro eq.
- simpl in eq. inversion eq.
- exists w'. exists a'.
  simpl in eq.
  inversion eq.
  repeat split; reflexivity.
Defined.




(* 
   TODO-Frage : Die nachfolgenden Lemmata ggf. in eine eigene Datei ? 
                Unterbibliothek?   
*)



(* --------------------------------------------------------------------------*)

(** * Die groesseren "Zerlegungs"-Lemmata fuer inits *)

(* --------------------------------------------------------------------------*)

(** Vorbereitung fuer das PL,
    um von einer Zerlegung von [inits w] auf eine Zerlegung von [w] 
    mit den benoetigten Eigenschaften schliessen zu koennen. *)

Lemma inits_diff_w {A : Type} (w : @Word A) : 
   forall (w1 : @Word A) (inits1 inits2 : @Word (@Word A)),
            inits_w w = concat_word (snoc inits1 w1) inits2 
            -> { w2 : @Word A & w = concat_word w1 w2 }.
Proof.
  induction w as [ | w' IHw a]; intros w1 inits1 inits2 iw_eq_i1w1i2.
 
  - (* w = eps *)
    exists eps.
    simpl in iw_eq_i1w1i2.
    destruct inits2 as [ | inits2' w3] ; simpl in *.

    + (* inits2 = eps *)
      inversion iw_eq_i1w1i2.
      reflexivity.

    + (* inits2 = snoc initis2' w3 *)
      inversion iw_eq_i1w1i2 as [[eps_eq_i1w1i2 eps_eq_w]].
      destruct inits2' as [ | inits2'' w3']; simpl in *.

      * (* inits2 = eps *)
        inversion eps_eq_i1w1i2.

      * (* inits2 = snoc initis2'' w3' *)
        inversion eps_eq_i1w1i2.

  - (* w = snoc w' a *)
    simpl in iw_eq_i1w1i2.
    destruct inits2 as [ | inits2' w3]; simpl in *.

    + (* inits2 = eps *)
      inversion iw_eq_i1w1i2.
      exists eps.
      simpl.
      reflexivity.

    + (* inits2 = snoc inits2' w3 *)
      inversion iw_eq_i1w1i2 as [[iw'_eq_i1w1i2 w'a_eq_w]].

      apply IHw in iw'_eq_i1w1i2 as ex_w2.
      destruct ex_w2 as [w2' w'_eq_w1w2].

      exists (snoc w2' a).
      simpl.
      rewrite w'_eq_w1w2.
      reflexivity.
Defined.


Lemma inits_diff_pref_w {A : Type} (w : @Word A) : 
  forall 
    (p1 p2 : @Word A) 
    (inits1 inits2 inits3 : @Word (@Word A)),
      inits_w w = concat_word (concat_word 
                     (snoc inits1 p1) (snoc inits2 p2)) inits3 
       -> { diff_p1p2 : @Word A & 
            ((p2 = concat_word p1 diff_p1p2) * 
             (word_length diff_p1p2 > 0))%type }.
Proof.

  induction w as [ |w' IHw a]; 
  intros p1 p2 inits1 inits2 inits3 iw_eq_i1p1i2p2i3.
  
  - (* w = eps *)
    (* ---> unmoeglich, da |inits_w eps| = 1 und 
            |i1p1i2p2i3| >= 2 durch die 2 snocs. *)

    destruct inits3 as [ | inits3' p3].

    + simpl in iw_eq_i1p1i2p2i3.
      inversion iw_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2 eps_eq_p2]].

      apply absurd_eps_eq_concat_snoc in eps_eq_i1p1i2 as ff.
      destruct ff.

    + simpl in iw_eq_i1p1i2p2i3.
      inversion iw_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2p2p3 eps_eq_p3]].

      apply absurd_eps_eq_concat_snoc in eps_eq_i1p1i2p2p3 as ff.
      destruct ff.

  - (* w = snoc w' a *)
    destruct w' as [ | w'' a'].

    + (* w = snoc eps a *)
      simpl in iw_eq_i1p1i2p2i3.
      destruct inits3 as [ | inits3' p3].

      * (* w = snoc eps a
           ---> inits w = (snoc inits1 p1) (snoc inits2 p2) 
           ---> p1 = eps, p2 = (snoc eps a), diff = (snoc eps a) *)
        simpl in iw_eq_i1p1i2p2i3.
        inversion iw_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2 a_eq_p2]].
        exists (snoc eps a).
        destruct inits2 as [ | inits2' p2'].

        { simpl in eps_eq_i1p1i2.
          inversion eps_eq_i1p1i2.
          simpl.
          split.
          - reflexivity.
          - apply Gt.gt_Sn_O.
        }

        { simpl in eps_eq_i1p1i2.
          inversion eps_eq_i1p1i2 as [[eps_eq_i1p1i2' eps_eq_p2']].
          destruct inits2' as [ | inits2''  p2''].

          - simpl in eps_eq_i1p1i2'.
            inversion eps_eq_i1p1i2'.

          - simpl in eps_eq_i1p1i2'.
            inversion eps_eq_i1p1i2'.
         }

       * (* w = snoc eps a 
            inits w = (snoc inits1 p1) . (snoc inits2 p2) . (snoc inits3' p3) 
            ---> wegen 3. snoc zu lang, also unmoeglich.  *)
         simpl in iw_eq_i1p1i2p2i3.
         inversion iw_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2p2i3 a_eq_p3]].
         destruct inits3' as [ | inits3''  p3''].

         { simpl in eps_eq_i1p1i2p2i3.
           inversion eps_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2 eps_eq_p2]].
           destruct inits2 as [ | inits2' p2'].

           - simpl in eps_eq_i1p1i2.
             inversion eps_eq_i1p1i2.
 
           - simpl in eps_eq_i1p1i2.
             inversion eps_eq_i1p1i2.
         }

         { simpl in eps_eq_i1p1i2p2i3. 
           inversion eps_eq_i1p1i2p2i3 as [[eps_eq_i1p1i2p3i3'' eps_eq_p3']].
           destruct inits3'' as [ | inits3''' p3'''].

           - simpl in eps_eq_i1p1i2p3i3''.
             inversion eps_eq_i1p1i2p3i3''.
 
           - simpl in eps_eq_i1p1i2p3i3''.
             inversion eps_eq_i1p1i2p3i3''.
         }

    + (* w = snoc (snoc w'' a') a *)
      remember (snoc w'' a') as w'.

      (* ----> inits w = snoc (snoc inits w'' w') (snoc w' a) *)

      destruct inits3 as [ | inits3' p3].

      * (* inits3 = eps 
           ---> inits w = (snoc inits1 p1) (snoc inits2 p2) *)
        simpl in iw_eq_i1p1i2p2i3.
        inversion iw_eq_i1p1i2p2i3 as [[w''w''a'_eq_i1p1i2 w''a'a_eq_p2]].

        destruct inits2 as [ | inits2' p2'].

         { (* inits2 = eps 
              ---> inits w = snoc (snoc inits1 p1) p2 
              ---> p1 = w' , p2 = (snoc w' a) , diff = (snoc eps a) *)
           simpl in *.
           inversion w''w''a'_eq_i1p1i2 as [[iw''_eq_i1 w''a'p1]].
           rewrite inits_last_w in iw''_eq_i1. 
           
           inversion iw''_eq_i1 as [[riw_eq_inits1 w'_eq_p1]]. 
           rewrite <- w'_eq_p1.
           
           exists (snoc eps a).
           split.

           - simpl. reflexivity.
           - apply Gt.gt_Sn_O.
         }

         { (* inits2 = snoc init2' p2' 
              ---> inits w = concat_word (snoc inits1 p1) 
                             (snoc (snoc ints2' p2') p2) *)
 
           pose (IHw p1 p2' inits1 inits2' eps) as IHw_inst.
           simpl in IHw_inst. simpl in w''w''a'_eq_i1p1i2.
           apply IHw_inst in w''w''a'_eq_i1p1i2 as ex_diff.
           destruct ex_diff as [d_p1p2 diff_props].
           destruct diff_props as [p2'_eq_p1dp12 len_diff].

           rewrite inits_last_w in w''w''a'_eq_i1p1i2.
           inversion w''w''a'_eq_i1p1i2 as [[riw'_eq_i1p1i2' w'_eq_p2']].

           (* ---> p1 = p2-diff , p2 = (snoc p2' a) , diff = (snoc d_p1p2 a) *)
           exists (snoc d_p1p2 a). 
           rewrite p2'_eq_p1dp12.
           simpl.

           split.

           - reflexivity.
           - apply Gt.gt_Sn_O.

         }

       * rewrite inits_last_w in iw_eq_i1p1i2p2i3.
         simpl in iw_eq_i1p1i2p2i3.
         inversion iw_eq_i1p1i2p2i3 as [[iw'_eq_i1p1i2p2i3' w'a_eq_p3]].

         (* kurze Variante: 

            apply (IHw p1 p2 inits1 inits2 inits3' iw'_eq_i1p1i2p2i3').

         *)

         (* Ausfuehrlichere Variante: *) 

         apply IHw in iw'_eq_i1p1i2p2i3' as ex_diff.
         destruct ex_diff as [d_p1p2 diff_props].

         (* ---> p1 = p2-d_p1p2 , p2 = p1 d_p1p2 , diff = d_p1p2 *)
         exists d_p1p2.
         exact diff_props.

Defined.


(* Hier werden nur die beiden vorhergehenden Lemmata zusammengefasst. *)
Lemma w_decomp_of_initsw_decomp {A : Type} (w : @Word A): 
  forall (p1 p2 : @Word A)
         (inits1 inits2 inits3 : @Word (@Word A)),
  inits_w w = concat_word (concat_word 
                (snoc inits1 p1) (snoc inits2 p2)) inits3 
  -> { diff_p1p2 : @Word A &
       ((p2 = concat_word p1 diff_p1p2) * 
        (word_length diff_p1p2 > 0))%type } *
        { diff_p2w : @Word A & w = concat_word p2 diff_p2w }.

Proof.
  intros p1 p2 inits1 inits2 inits3 iw_eq_i1p1i2p2i3p3.
  split.

  - apply inits_diff_pref_w in iw_eq_i1p1i2p2i3p3 as ex_dp1p2.
    exact ex_dp1p2.

  - simpl in iw_eq_i1p1i2p2i3p3.
    apply inits_diff_w in iw_eq_i1p1i2p2i3p3 as ex_dp2w.
    exact ex_dp2w.

Defined.


(* --------------------------------------------------------------------------*)

(** * Die groesseren "Zerlegungs"-Lemmata fuer map *)

(* --------------------------------------------------------------------------*)

(** Vorbereitung fuer das PL,
    um von einer Zerlegung von [trace w] auf eine Zerlegung von [inits w] 
    schliessen zu koennen. *)


Lemma map_decomp_2_w : forall X Y :Type, forall f : X -> Y, forall w : @Word X,
  forall v1 v2 : @Word Y,
  map_word f w = concat_word v1 v2 -> 
     { w1 : @Word X & { w2 : @Word X &
          w = concat_word w1 w2 /\ map_word f w1 = v1 /\ map_word f w2 = v2 } }.
Proof.
  intros X Y f.
  induction w.
  (* w = eps *)
  - intros v1 v2 H.
    exists eps.
    exists eps.
    simpl in H.
    split.
    + simpl.
      reflexivity.
    + assert (v2 = eps).
      * { destruct v2.
          - reflexivity.
          - inversion H.
        }
      * { rewrite H0 in *.
          simpl in *.
          split.
          - exact H.
          - reflexivity.
        }
  (* w = snoc w' a *)
   - intros v1 v2 H.
    simpl in H.
    destruct v2 as [|v2' y2].
    (* v2' = eps *)
    + simpl in H.
      destruct v1 as [|v1' y1].
      (* v1' = eps *)
      * { inversion H. }
      (* v1' = snoc v1' y1 *)
      * { simpl in H.
          
          inversion H.
          exists (snoc w a).
          exists eps.
          simpl.
          split.
          - reflexivity.
          - split ; reflexivity.
        } 
    (* v2' = snoc v2' y2 *)
    + simpl in H.
      assert (map_word f w = concat_word v1 v2').
      * { inversion H.
          reflexivity.
        }
      * pose (IHw v1 v2' H0) as ex_w1_w2.
        destruct ex_w1_w2 as [w1' ex_w2].
        destruct ex_w2 as [w2' IHw_eqs].
        destruct IHw_eqs as [w_eq_w1'w2' [fw1'_eq_v1 fw2'_eq_v2']].
        inversion H as [[fw_eq_v1v2' fa_eq_y2]].
        exists w1'.
        exists (snoc w2' a).
        simpl.
        rewrite w_eq_w1'w2'.
        rewrite fw1'_eq_v1.
        rewrite fw2'_eq_v2'.
        rewrite fa_eq_y2.
        repeat split; reflexivity.
Defined.



Lemma map_decomp_3 : forall X Y : Type, forall f : X -> Y, forall w : @Word X,
  forall v1 v2 v3 : @Word Y,
  map_word f w = concat_word (concat_word v1 v2) v3 ->
  { w1 : @Word X & { w2 : @Word X & { w3 : @Word X &
  w = concat_word (concat_word w1 w2) w3 /\
  map_word f w1 = v1 /\ map_word f w2 = v2 /\ map_word f w3 = v3 } } }.
Proof.
  intros X Y f w v1 v2 v3 H.

  pose (concat_word v1 v2) as v12.
  apply map_decomp_2_w in H as decomp_w12'w3'.

  destruct decomp_w12'w3' as [w12' decomp_w3'].
  destruct decomp_w3' as [w3' decomp_eqs].
  destruct decomp_eqs as [w_eq_w12'w3' decomp_eqs].
  destruct decomp_eqs as [fw12'_eq_v1v2 fw3'_eq_v3].

  apply map_decomp_2_w in fw12'_eq_v1v2 as decomp_w1'w2'.

  destruct decomp_w1'w2' as [w1' decomp_w2'].
  destruct decomp_w2' as [w2' decomp_eqs'].
  destruct decomp_eqs' as [w12'_eq_w1'w2' decomp_eqs'].
  destruct decomp_eqs' as [fw1'_eq_v1 fw2'_eq_v2].

  exists w1'.
  exists w2'.
  exists w3'.

  rewrite w_eq_w12'w3'.
  rewrite w12'_eq_w1'w2'.
  rewrite fw1'_eq_v1. 
  rewrite fw2'_eq_v2.
  rewrite fw3'_eq_v3.

  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * { reflexivity. }
      * { reflexivity. }
Defined.


(* TODO: Lemma map_decomp_snoc *)
