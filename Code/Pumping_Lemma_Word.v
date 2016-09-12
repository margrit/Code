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
      und [Q_size] anhand arithmetischer Lemmata, so dass es die Form bekommt, 
      in der das Pigeonhole-Prinzip darauf angewendet werden kann *)

  apply le_n_S in len_w as S_len_w.
  rewrite <- tr_w_len in S_len_w.
  apply le_lt_n_Sm in S_len_w.
  apply lt_S_n in S_len_w.

  (** Anwendung des Pigeonhole-Prinzips *)

  apply pigeonhole_w in S_len_w as pigeonhole_rp_tr_w.

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
  destruct ex_decomp_tr_w' as [trw1 ex_decomp_tr_w''].
  destruct ex_decomp_tr_w'' as [trw2 ex_decomp_tr_w'''].
  destruct ex_decomp_tr_w''' as [trw3 trw_eq_trw1trw2trw3].

  (** Der Trace [tr_w] ist durch Anwendung der Funktion [trace_w] 
      entstanden, die durch eine [map] auf die Liste der Praefixe
      [inits] des Wortes [w] realsisert ist. Daher koennen wir nun mit 
      Hilfe des Dekompositionslemmas [map_decomp_3] aus der Dekomposition
      von [tr_w] eine korrespondierende Zerlegung von [inits w] 
      in drei Teilwoerter erzeugen. *)

  unfold trace_w in trw_eq_trw1trw2trw3.
  apply map_decomp_3 in trw_eq_trw1trw2trw3 as ex_decomp_w. 
  destruct ex_decomp_w as [inits1 ex_decomp_w'].
  destruct ex_decomp_w' as [inits2 ex_decomp_w''].
  destruct ex_decomp_w'' as [inits3 ex_decomp_w_eqs].
  destruct ex_decomp_w_eqs as [iw_eq_i1i2i3 ex_decomp_w_eqs'].
  destruct ex_decomp_w_eqs' as [mi1_eq_trw1qrp ex_decomp_w_eqs''].
  destruct ex_decomp_w_eqs'' as [mi2_eq_trw2qrp mi2_eq_trw3].

  (* TODO: Das sollte noch zu den inits-Lemmata
           ausgelagert werden. *) 

  apply ex_snoc_map in mi1_eq_trw1qrp as ex_snoc_i1.
  destruct ex_snoc_i1 as [inits1' ex_snoc_i1'].
  destruct ex_snoc_i1' as [p1 ex_snoc_i1_props].
  destruct ex_snoc_i1_props as [ex_snoc_i1_props' qrp_eq_dhq0p1].
  destruct ex_snoc_i1_props' as [i1_eq_inits1'p1 mi1'_eq_trw1].

  apply ex_snoc_map in mi2_eq_trw2qrp as ex_snoc_i2.
  destruct ex_snoc_i2 as [inits2' ex_snoc_i2'].
  destruct ex_snoc_i2' as [p2 ex_snoc_i2_props].
  destruct ex_snoc_i2_props as [ex_snoc_i2_props' qrp_eq_dhq0p2].
  destruct ex_snoc_i2_props' as [i2_eq_inits2'p2 mi2'_eq_trw2].

  rewrite i1_eq_inits1'p1 in iw_eq_i1i2i3.
  rewrite i2_eq_inits2'p2 in iw_eq_i1i2i3.

  (** Nun koennen wir das Dekompositionslemma [w_decomp_of_initsw_decomp]
      benutzen, um aus der Zerlegung der Praefixliste [inits w] eine 
      korrespondierende Zerlegung des Eingabeworts [w] zu erhalten. *)

  apply w_decomp_of_initsw_decomp in iw_eq_i1i2i3 as ex_decomp_w.
  destruct ex_decomp_w as [ex_y ex_z].

  destruct ex_y as [y y_props].
  destruct y_props as [p2_eq_p1y y_len].

  destruct ex_z as [z w_eq_p2z].

  remember p1 as x.

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

  - (** Dass die Zusammensetung von [x],[y] und [z] das Eingabewort [w] 
          ergibt sich aus Eigenschaften Zerlegung der Praefixliste. *)

    rewrite <- p2_eq_p1y.
    rewrite <- w_eq_p2z.
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
    rewrite <- qrp_eq_dhq0p1.

    (** Nun koennen wir benutzen, dass bei Abarbeitung des Worts [xy] von
       [q0] aus ebenfalls q_rp erreicht wird und damit ebenso bei Abarbeitung 
       des Worts [y] von Zustand [q_rp] selbst aus. *)

    pose qrp_eq_dhq0p2 as dhq0x_eq_dhq0p2.
    rewrite qrp_eq_dhq0p1 in dhq0x_eq_dhq0p2.
    rewrite p2_eq_p1y in dhq0x_eq_dhq0p2.

    rewrite delta_hat_app in dhq0x_eq_dhq0p2.
    rewrite <- qrp_eq_dhq0p1 in dhq0x_eq_dhq0p2.

    (** Jetzt koennen wir das Lemma [pump_loop] anwenden, und 
        erhalten damit die Hypothese, dass bei beliebigen
        Wiederholungen des Teilworts [y] von [q_rp] aus wiederum
        [q_rp] erreicht wird.  *)

    apply eq_sym in dhq0x_eq_dhq0p2.
    apply (pump_loop k) in dhq0x_eq_dhq0p2 as pump_y.
    rewrite pump_y.

    (** Es bleibt lediglich zu zeigen, dass bei Eingabe des Teilworts [z] von
        [q_rp] aus wiederum ein Endzustand erreicht wird, was sich durch 
        die Gleichheit von [q_rp] und [delta_hat q0 x y] sowie  
        [xyz] und [w] moeglich ist. *)

    rewrite qrp_eq_dhq0p2.
    rewrite <- delta_hat_app.
    rewrite <- w_eq_p2z.

    exact (w_in_lang).

Defined.
