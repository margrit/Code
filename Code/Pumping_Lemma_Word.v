(* Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Dfa.v *)

(** Veraltet: 

Die Datei wurde dahin verändert, dass nur noch einfache Taktiken verwerdet werden. 
Die Beweise sind in die einzelnen Teilbeweise unterteilt und dies wird durch die Zeichen
-, +, * Sichtbar gemacht. Um mehr als 3 Ebenen zu schachteln, werden die gleichen Zeichen
wiederverwendet, nur dass sie mit einer geschweiften Klammer umrahmt sind. Statt Listen über 
[Sigma] werden Wörter über [Sigma] verwendet.

(Von der urspruenglichen Datei ist nicht mehr viel uebrig...)

*)


(* TODO-Frage: Wie waere anstatt ausschliesslich einer Zerlegung der Beweise 
               in elementare Schritte eine "paedagogische" Illustration, wie Beweise 
               in mehreren Etappen verkuerzt werden koennen? *)



Require Import Arith.

Load DFA_Def.
Load Repeats.
Load Repeats_List.
Load Conv_Vec_List_Word.

(*--------------------------------------------------------------------------------------------*)

(** ** Vorbereitung *)

(*--------------------------------------------------------------------------------------------*)

Fixpoint pump_w (n : nat) (w : @Word Sigma) : @Word Sigma :=
  match n with
  | O    => eps
  | S n' => concat_word w (pump_w n' w)
  end.

(* Wenn es eine Schleife im Automaten gibt, kann man diese nutzen,
um das Wort aufzublähen an dieser Stelle und bleibt im gleichen Zustand. *)
Theorem pump_loop: forall n : nat, forall q : Q, forall xs : @Word Sigma,
  delta_hat q xs = q -> delta_hat q (pump_w n xs) = q.
Proof.
  induction n as [ | n' IHn'].

  - intros q xs H.
    simpl.
    reflexivity.

  - intros q xs H.
    simpl.
    rewrite delta_hat_app.
    rewrite H.
    apply IHn'.
    assumption.
Defined.


(*--------------------------------------------------------------------------------------------*)

(** ** Das Pumping-Lemma *)

(*--------------------------------------------------------------------------------------------*)

Theorem pumping_lemma :

  forall w : @Word Sigma, Lang_delta w -> Q_size <= word_length w ->

  { x : @Word Sigma &
  { y : @Word Sigma &
  { z : @Word Sigma &

   ((word_length y > 0) *
    (w = concat_word (concat_word x y) z) *
    (forall k : nat, Lang_delta (concat_word (concat_word x (pump_w k y)) z))

    )%type } } }.

Proof.
  intros w w_in_lang len_w.

  (** Vorbereitung : 
      [tr_w]: "Trace" von [w]: Die Liste der Zustaende, die bei der Abarbeitung 
              des Wortes [w] von [q0] ausgehend durchlaufen werden.
      [tr_w_len]: Die Laenge dieser Zustandliste (immer > 0) im Verhaeltnis
                  zur Laenge des Eingabeworts.
  *)

  pose (trace_w q0 w) as tr_w.
  pose (trace_length_w w q0) as tr_w_len.

  (** Umschreiben des Verhaeltnisses zwischen Wortlaenge des Eingabeworts 
      und [Q_size] anhand 
      - der arithmetischen Lemmata [le_n_S], [le_lt_n_Sm] und [lt_S_n] sowie
      - des Lemmas [tr_w_len] ueber das Verhaeltnis der Laenge von [w] und 
        des Traces von w, 
      so dass die Hypothese [S_len_w] die Form bekommt,
      in der das Pigeonhole-Prinzip darauf angewendet werden kann *)

  apply le_n_S in len_w as S_len_w.
  apply le_lt_n_Sm in S_len_w.
  apply lt_S_n in S_len_w.
  
  rewrite <- tr_w_len in S_len_w.

  (** Anwendung des Pigeonhole-Prinzips *)

  apply pigeonhole_w in S_len_w as pigeonhole_rp_tr_w.

  clear len_w S_len_w tr_w_len.

  (** Durch das Pigeonhole-Prinzip haben wir nun als Hypothese zur Verfuegung,
      dass die Zustandliste [tr_w] eine Wiederholung enthaelt.
      Auf diese Hypothese koennen wir nun das Dekompositionslemma 
      [Repeats_decomp_w] anwenden, das uns die Liste entlang des sich 
      wiederholenden Zustands zerlegt als 
      [trw1 q_rp trw2 q_rp trw3], wobei 
      [q_rp] der sich wiederholende Zustand und die
      [trwi] jeweils der i-te Teil des Traces [tr_w] sind. *) 

  apply Repeats_decomp_w in pigeonhole_rp_tr_w as ex_decomp_tr_w.

  destruct ex_decomp_tr_w as [q_rp ex_decomp_tr_w'].
  destruct ex_decomp_tr_w' as [trw1 [trw2 [trw3 trw_eq_trw1trw2trw3]]].

  (** Der Trace [tr_w] ist durch Anwendung der Funktion [trace_w] 
      entstanden, die durch eine [map] auf die Liste der Praefixe
      [inits] des Wortes [w] realisert ist. Daher koennen wir nun mit 
      Hilfe des Dekompositionslemmas [map_decomp_3] aus der Dekomposition
      von [tr_w] eine korrespondierende Zerlegung von [inits w] 
      in drei Teile erzeugen. 
      Dort, wo in der Zerlegung der Zustandsliste [q_rp]
      vorkam, finden sich jetzt die Praefixe [x] und [xy] von [w]. *)

  unfold trace_w in trw_eq_trw1trw2trw3.
  apply map_decomp_3_snoc in trw_eq_trw1trw2trw3 as ex_decomp_iw. 

  destruct ex_decomp_iw as [inits1 [inits2 [inits3 ex_decomp_iw']]].
  destruct ex_decomp_iw' as [x [xy ex_decomp_iw_eqs]].
  destruct ex_decomp_iw_eqs as [[iw_eq_i1xi2xyi3 dhq0x_eq_qrp] dhq0xy_eq_qrp].

  (** Nun koennen wir das Dekompositionslemma [w_decomp_of_initsw_decomp]
      benutzen, um aus der Zerlegung der Praefixliste [inits w] eine 
      korrespondierende Zerlegung des Eingabeworts [w] in 
      die drei Teilwoerter [x], [y] und [z] zu erhalten.
      Dabei ergeben sich [y] und [z] als Differenzen zwischen 
      - den Praefixen [x] und [xy] sowie
      - dem Praefix [xy] und dem gesamten Eingabewort [w]. *)

  apply w_decomp_of_initsw_decomp in iw_eq_i1xi2xyi3 as ex_decomp_w.

  destruct ex_decomp_w as [ex_y ex_z].
  destruct ex_y as [y [xy_eq_x_y y_len]].
  destruct ex_z as [z w_eq_xyz].

  (** Aufraeumarbeiten: 
      Wir entfernen nicht mehr benoetigte Hypothesen. *)

  clear trw_eq_trw1trw2trw3 iw_eq_i1xi2xyi3.
  clear tr_w trw1 trw2 trw3.
  clear inits1 inits2 inits3.

  (** Jetzt haben wir die benoetigten Zeugen [x],[y], und [z] 
      mit den gewuenschten Eigenschaften als Hypothesen zur Verfuegung.
      Demenentsprechend koennen wir die Existenzquantoren in der 
      Konklusion instanziieren und muessen dann nur noch die 
      geforderten drei Eigenschaften beweisen. *)

  exists x.
  exists y.
  exists z.

  repeat split.

  - (** Die Bedingung an die Laenge von [y] ist bereits exakt als 
        Hypothese vorhanden. *)

    exact (y_len).

  - (** Dass die Zusammensetzung von [x],[y] und [z] dem Eingabewort [w] 
        entspricht, ergibt sich aus den Eigenschaften der Zerlegung 
        des Eingabeworts, die aus der Zerlegung der Praefixliste 
        erzeugt wurde. *)

    rewrite <- xy_eq_x_y.
    rewrite <- w_eq_xyz.
    reflexivity.

  - (** Es bleibt zu zeigen, dass die aufgepumpte Version des Wortes 
        fuer beliebige [k] wiederum in der Sprache des Automaten liegt. *)

    unfold Lang_delta.
    unfold Lang_delta in w_in_lang.

    intro k.

    (** Zunaechst benutzen wir das Lemma [delta_hat_app], das 
        Verhalten von delta_hat auf verketteten Woertern beschreibt,
        und koennen dann die Hypothese verwenden, die besagt, dass nach
        der Abarbeitung der Eingabe [x] von [q0] aus der sich 
        wiederholende Zustand [q_rp] ergibt. *)

    repeat rewrite delta_hat_app.
    rewrite dhq0x_eq_qrp.

    (** Nun koennen wir benutzen, dass bei Abarbeitung des Worts [xy] von
       [q0] aus ebenfalls q_rp erreicht wird und damit ebenso bei Abarbeitung 
       des Worts [y] von Zustand [q_rp] selbst aus. *)

    pose dhq0xy_eq_qrp as dhq0xy_eq_dhq0x.
    rewrite <- dhq0x_eq_qrp in dhq0xy_eq_dhq0x. 
    rewrite xy_eq_x_y in dhq0xy_eq_dhq0x.

    rewrite delta_hat_app in dhq0xy_eq_dhq0x.
    rewrite dhq0x_eq_qrp in dhq0xy_eq_dhq0x.

    (** Jetzt koennen wir das Lemma [pump_loop] anwenden, und 
        erhalten damit die Hypothese, dass bei beliebigen
        Wiederholungen des Teilworts [y] von [q_rp] aus wiederum
        [q_rp] erreicht wird.  *)

    apply (pump_loop k) in dhq0xy_eq_dhq0x as pump_y.
    rewrite pump_y.

    (** Es bleibt lediglich zu zeigen, dass bei Eingabe des Teilworts [z] von
        [q_rp] aus wiederum ein Endzustand erreicht wird, was sich durch
        die Gleichheit von [q_rp] und [delta_hat q0 x y] sowie
        von [xyz] und [w] moeglich ist. *)

    rewrite <- dhq0xy_eq_qrp.
    rewrite <- delta_hat_app.
    rewrite <- w_eq_xyz.

    exact (w_in_lang).

Defined.
