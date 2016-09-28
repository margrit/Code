(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Dfa.v*)

(* In this file we try to formalize some notions from the 
   formal languages field, precisely 
   Deterministic Finite-State Automata.
 *)

(** Die Datei wurde dahin verändert, dass nur noch einfache Taktiken verwerdet werden. 
Die Beweise sind in die einzelnen Teilbeweise unterteilt und dies wird durch die Zeichen
-, +, * Sichtbar gemacht. Um mehr als 3 Ebenen zu schachteln, werden die gleichen Zeichen
wiederverwendet, nur dass sie mit einer geschweiften Klammer umrahmt sind. Statt Listen über 
[Sigma] werden Wörter über [Sigma] verwendet.
*)
Load DFA_Def_accept_Prop.
Load Repeats_List.
Section Transitions.


SearchAbout split.
Print split.

Definition split_conf_list (q : Q) (w : @Word Sigma) : list Q * list (@Word Sigma) 
              := split (conf_list w q).
Print split_conf_list. 

Definition state_list (l: list Conf_DFA) := fst (split l).
Definition tails_list (l: list Conf_DFA) := snd (split l).


(* Definition state_list (q : Q) (w : @Word Sigma) : list Q := fst (split_conf_list q w).

Definition tails_list (q : Q) (w : @Word Sigma) : list (@Word Sigma) := snd (split_conf_list q w).
*)

Lemma length_conf_list (w : @Word Sigma) : forall q, S (word_length w) = (length (conf_list w q)).
Proof.
induction w.
- simpl.
  reflexivity.
- simpl.
  intro q.
  rewrite (IHw (delta q a)).
  reflexivity.
Defined.
  
 

Fixpoint word_replicate (n : nat) (w : @Word Sigma) : @Word Sigma :=
  match n with
  | O    => eps
  | S n' => concat_word w (word_replicate n' w)
  end.

(* Wenn es eine Schleife im Automaten gibt, kann man diese nutzen,
um das Wort aufzublähen an dieser Stelle und bleibt im gleichen Zustand. *)
Theorem ext_loop: forall n : nat, forall q : Q, forall xs : @Word Sigma,
  delta_hat q xs = q -> delta_hat q (word_replicate n xs) = q.
Proof.
  induction n as [|n'].
  - intros q xs H.
    simpl.
    reflexivity.
  (* n = S n; *)
  - intros q xs H.
    simpl.
    rewrite delta_hat_app.
    rewrite H.
    apply IHn'.
    assumption.
Qed.



Fixpoint tails_w {X : Type} (w : @Word X) : @Word (@Word X) :=
  match w with
  | eps       =>  snoc eps eps
  | snoc xs x => snoc (map_word (fun w => snoc w x) (tails_w xs)) eps 
  end.


Fixpoint inits_l {X : Type} (l : list X) : list (list X) :=
  match l with
  | nil       => nil :: nil
  | x :: xs => nil :: map (cons x) (inits_l xs)
  end.


Definition inits_w {X : Type} (w : @Word X) : @Word (@Word X) :=
 list_to_word (map (list_to_word) (inits_l (word_to_list w))).

Eval compute in (inits_w (snoc (snoc ( snoc eps 1 ) 2) 3)).
Eval compute in (inits_l nil : list (list nat)).

(* Aber sinnvoller erscheint mir: *)

Definition inits_list_w {X : Type} (w : @Word X) : list (@Word X) :=
 map (list_to_word) (inits_l (word_to_list w)).

Eval compute in (inits_list_w (snoc (snoc ( snoc eps 1 ) 2) 3)).


(* Als Datenstruktur fuer die Verwaltung von Zustandsfolgen, Konfigurationsfolgen etc. 
   erscheinen mir Listen als die natuerlichere Wahl. *) 

Theorem inits_len_l : forall X : Type, forall l : list X,
  length (inits_l l) = S (length l).
Proof.
  induction l as [ | x l' IHl].
  - simpl.
    reflexivity.
  (* l = cons x l' *)
  - simpl.
    rewrite map_length.
    rewrite IHl.
    reflexivity.
Defined.

Theorem inits_len_w : forall X : Type, forall w : @Word X,
  length (inits_list_w w) = S (word_length w).
Proof.
  intros X w.
  unfold inits_list_w.
  rewrite map_length.
  rewrite <- wl_pres_length.
  apply inits_len_l.
Defined.

Theorem inits_decomp_1_l :
  forall X : Type,
  forall l : list X,
  forall y : list X, 
  forall xs ys : list (list X),
   inits_l l = xs ++ (y :: ys) ->
    exists zs : list X, l = y ++ zs.
Proof.
  intros X l.
  induction l as [|h l'].
  (* l ist nil *)
  - intros y xs ys H.
    (* y muss nil sein *)
    simpl in H.
    assert (xs = nil) as Hxs.
    + destruct xs.
      * { reflexivity. }
      * { destruct xs.
          - simpl in H.
            inversion H.
          - simpl in H.
            inversion H.
        }
    + subst xs.
      simpl in H.
      inversion H.
      exists nil.
      simpl.
      reflexivity.
  (* l ist h :: l' *)
  - intros y xs ys H.
    simpl in H.
    destruct xs.
    + simpl in H.
      inversion H.
      exists (h :: l').
      simpl.
      reflexivity.
    + simpl in H.
      inversion H.
      apply map_dec_2_l in H2.
      destruct H2 as [xss].
      destruct H0 as [yss].
      destruct H0.
      destruct H2.
      destruct yss as [|y0 yss].
      * { inversion H3. }
      * { simpl in H3.
          apply IHl' in H0.
          destruct H0 as [zs].
          inversion H3.
          simpl.
          exists zs.
          subst.
          reflexivity.
        }
Qed.

Theorem inits_decomp_2_l :
  forall X : Type,
  forall l : list X,
  forall y z : list X,
  forall xs ys zs : list (list X),
   inits_l l = xs ++ (y :: ys) ++ (z :: zs) ->
    exists ds : list X, z = y ++ ds /\ length ds > 0.
Proof.
  intros X l.
  induction l as [|h l'].
  - intros y z xs ys zs H.
  (* Impossible case, inits nil has 1 elem,
     the list on RHO has >= 2 elems *)
    destruct xs.
    + simpl in H.
      inversion H.
      subst y.
      simpl in *.
      inversion H.
      destruct ys.
      * { simpl in *.
          inversion H1.
        }
      * { simpl in *.
          inversion H1.
        }
    + simpl in *.
      inversion H.
      subst l.
      inversion H.
      destruct xs.
      * { simpl in *.
          inversion H2.
        }
      * { simpl in *.
          inversion H1.
        }
  (* l = h :: l' *)
  (* we need more info *)
  - destruct l' as [|h' ls].
    + intros y z xs ys zs H.
      simpl in *.
      destruct xs.
      * { simpl in *.
          inversion H.
          subst y.
          inversion H.
          destruct ys.
          - simpl in *.
            inversion H1.
            exists (h :: nil).
            split.
            + reflexivity.
            + simpl.
               unfold gt.
               unfold lt.
               apply le_n.
          - inversion H1.
            simpl in *.
            clear H2.
            clear H.
            destruct ys.
            * { simpl in *.
                inversion H4.
              }
            * { simpl in *.
                inversion H4.
              } }
      * { inversion H.
          destruct xs.
          - simpl in *.
            inversion H2.
            destruct ys.
            + simpl in *.
              inversion H4.
            + simpl in *.
              inversion H4.
          - inversion H2.
            destruct xs.
            + simpl in H4.
              inversion H4.
            + simpl in H4.
              inversion H4.
        }
    (* l = h :: h' :: ls *)
    (* finally we can use the ind. hyp. *)
    + intros y z xs ys zs H.
      remember (h' :: ls) as l.
      simpl in *.
      destruct xs.
      * { simpl in *.
          inversion H.
          exists z.
          split.
          - simpl.
          reflexivity.
          - apply map_dec_2_l in H2.
            destruct H2 as [xss].
            destruct H0 as [yss].
            destruct H0.
            destruct H2.
            destruct yss.
            + simpl in *.
              inversion H3.
            + simpl in *.
              inversion H3.
              simpl.
              unfold gt.
              unfold lt.
              apply le_n_S.
              apply le_0_n.
        }
      * { simpl in *.
          inversion H.
          subst l0. 
          clear H.
          assert (map (cons h) (inits_l l) = xs ++ (y :: ys) ++ (z :: zs)).
          - simpl.
            assumption.
          - apply map_decomp_3_l in H.
            destruct H as [xss].
            destruct H as [yss].
            destruct H as [zss].
            destruct H.
            destruct H0.
            destruct H1.
            destruct yss.
            + simpl in *.
              inversion H1.
            + simpl in *.
              inversion H1.
              destruct zss.
              * { simpl in *.
                  inversion H3.
                }
              * { simpl in *.
                  inversion H3.
                  apply IHl' in H.
                  destruct H as [ds].
                  destruct H.
                  exists ds.
                  split.
                  - subst.
                    reflexivity.
                  - assumption.
                } }
Qed.

Theorem inits_dec_l : 
  forall X : Type, 
  forall l : list X,
  forall b c : list X, 
  forall ass bs cs : list (list X),
  inits_l l = ass ++ (b :: bs) ++ (c :: cs) ->
  (exists ds : list X, c = b ++ ds /\ length ds > 0) /\
  exists es : list X, l = c ++ es.
Proof.
  intros X l b c ass bs cs H.
  remember H as H2.
  clear HeqH2.
  apply inits_decomp_2_l in H.
  destruct H as [ds].
  split.
  - exists ds.
    destruct H.
    split.
    + apply H.
    + apply H0.
  - rewrite app_assoc in H2.
    apply inits_decomp_1_l in H2.
    assumption.
Qed.

Definition prefixes (q : Q) (w : @Word Sigma) : list Q :=
  map (delta_hat q) (inits_list_w w).

Lemma prefixes_len : forall w : @Word Sigma, forall q : Q,
  length (prefixes q w) = S (word_length w).
Proof.
  intros.
  unfold prefixes.
  rewrite map_length.
  apply inits_len_w.
Defined.


Require Import Arith.
Load vec_word_conv.

(** Das Pumping Lemma: *)
Theorem pumping_lemma : forall w : @Word Sigma,
  accepted_word w -> Q_size <= word_length w ->
  exists x : @Word Sigma,
  exists y : @Word Sigma,
  exists z : @Word Sigma,
  word_length y > 0 /\
 (* length y < Q_size -> *)
  w = concat_word (concat_word x y) z /\
  forall k : nat,
  accepted_word (concat_word (concat_word x (word_replicate k y)) z).
Proof.
  intros w w_in_lang len_w.
  
  
 (* Alles lustig, aber die urspruengliche Herangehensweise war cleverer, weil die Indizes 
    der Zustaende zu den Zeichen des Eingabeworts passen. *)

 (* Berechnen der Konfigurationsliste vom Startzustand ausgehend, bei Eingabe von w.
     Zerlegen dieser Liste in den Zustands- und den Restwort-Teil. *)
  pose (conf_list w q0) as conf_list_q0_w.
  pose (state_list conf_list_q0_w) as states_list_q0_w.
  pose (tails_list conf_list_q0_w) as tails_list_w.
  pose (length_conf_list w q0) as len_cl_eq_Sw.


  apply le_n_S in len_w as S_len_w. 
  rewrite len_cl_eq_Sw in S_len_w.
  apply le_lt_n_Sm in S_len_w.
  apply lt_S_n in S_len_w.

  pose (split_length_l conf_list_q0_w) as len_states_list.
  unfold state_list in *.
  unfold conf_list_q0_w in len_states_list.
  unfold Conf_DFA in S_len_w.
  rewrite <- len_states_list in S_len_w.

  apply states_size in S_len_w as pigeonhole_principle_rp_sl.

 


(** Das Pumping Lemma: *)
Theorem pumping_lemma : forall w : list Sigma,
  accepted_word w -> Q_size <= length w ->
  exists xs : list Sigma,
  exists ys : list Sigma,
  exists zs : list Sigma,
  length ys > 0 /\
 (* length ys < Q_size -> *)
  w = xs ++ ys ++ zs /\
  forall n : nat,
  accepted_word (xs ++ (word_replicate n ys) ++ zs).
Proof.
  intros w acc len_w.
  (* Let's look at which state the DFA is after reading
  epsilon, w0, w0w1, .. w. *)
  set (pref := prefixes q0 w).
  assert (Hpref : Q_size < length pref).
  - unfold pref.
    rewrite prefixes_len.
    unfold lt.
    apply le_n_S.
    apply len_w.
  - assert (HRep : repeats pref).
    + apply states_size.
      apply Hpref.
    + set (Hx := repeats_decomp Q pref HRep).
      destruct Hx.
      destruct H.
      destruct H.
      destruct H.
      unfold pref in H.
      unfold prefixes in H.
      set (Hx := map_dec_3 (list Sigma) Q (ext q0)
      (inits w) x0 (x :: x1) (x :: x2) H).
      destruct Hx.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      destruct H2.
      (* x4 und x5 können nicht nil sein *)
      destruct x4 as [|y x4].
      * { inversion H2. }
      * { destruct x5 as [|y2 x5].
          - inversion H3.
          - set (Hx := inits_dec _ w y y2 x3 x4 x5 H0).
            destruct Hx.
            destruct H4.
            destruct H5.
            destruct  H4.
            exists y.
            exists x6.
            exists x7.
            split.
            + apply H6.
            + split.
              * { subst y2.
                  rewrite H5.
                  rewrite app_assoc.
                  reflexivity.
                }
              * { unfold accepted_word in *.
                  intros n.
                  assert (ext q0 (y ++ (word_replicate n x6) ++ x7) = ext q0 w).
                  - rewrite ext_app.
                    rewrite ext_app.
                    simpl in H2.
                    inversion H2.
                    simpl in H3.
                    inversion H3.
                    assert (ext (ext q0 y) x6 = ext q0 y).
                    + pattern (ext q0 y) at 2.
                      rewrite H8.
                      rewrite <- H10.
                      rewrite H4.
                      rewrite ext_app.
                      reflexivity.
                    + rewrite ext_loop.
                       rewrite H5.
                       rewrite ext_app.
                       congruence.
                       rewrite H7.
                       reflexivity.
                  - rewrite H7.
                    apply acc.
                } }
Qed.