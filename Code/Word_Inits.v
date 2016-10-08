(*Load Word_Prop.*)
(* --------------------------------------------------------------------------*)

(** * Die groesseren "Zerlegungs"-Lemmata fuer inits *)

(* --------------------------------------------------------------------------*)

(** Vorbereitung fuer das PL,
    um von einer Zerlegung von [inits w] auf eine Zerlegung von [w]
    mit den benoetigten Eigenschaften schliessen zu koennen. *)

Lemma inits_diff_w {A : Type} (w : @Word A) :
      forall (w1 : @Word A) (inits1 inits2 : Word2),
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
      forall (p1 p2 : @Word A)
     (inits1 inits2 inits3 : Word2),
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

(** Zusammenfassen der beiden vorhergehenden Lemmata. *)

Lemma w_decomp_of_initsw_decomp {A : Type} (w : @Word A):
      forall (p1 p2 : @Word A)
     (inits1 inits2 inits3 : Word2),
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

(*Eval compute in ( w_decomp_of_initsw_decomp(snoc (snoc (snoc eps 1)2)3)).*)
