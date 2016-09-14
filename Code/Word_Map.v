

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
  ((w = concat_word (concat_word w1 w2) w3) *
   (map_word f w1 = v1) * 
   (map_word f w2 = v2) * 
   (map_word f w3 = v3)
  )%type } } }.
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

  repeat split.
Defined.


Lemma map_decomp_3_snoc_full {X Y : Type} (f : X -> Y) (w : @Word X)
  (v1 v2 v3 : @Word Y) (y1 y2 : Y) :
  map_word f w = concat_word (concat_word (snoc v1 y1) (snoc v2 y2)) v3 ->
  { w1 : @Word X & { w2 : @Word X & { w3 : @Word X &
  { x1 : X & { x2 : X & 
  ((w = concat_word (concat_word (snoc w1 x1) (snoc w2 x2)) w3) *
   (map_word f (snoc w1 x1) = (snoc v1 y1)) * 
   (map_word f (snoc w2 x2) = (snoc v2 y2)) * 
   (map_word f w3 = v3) *
   (map_word f w1 = v1) *
   (map_word f w2 = v2) *
   (f x1 = y1) *
   (f x2 = y2)
  )%type } } } } }.
Proof.
 intro mfw_eq_v1y1v2y2v3.

 apply map_decomp_3 in mfw_eq_v1y1v2y2v3 as ex_decomp_w.
 destruct ex_decomp_w as [w1' ex_decomp_w'].
 destruct ex_decomp_w' as [w2' ex_decomp_w''].
 destruct ex_decomp_w'' as [w3 ex_decomp_w_eqs].
 destruct ex_decomp_w_eqs as [ex_decomp_w_eqs' mw3_eq_v3 ].
 destruct ex_decomp_w_eqs' as [ex_decomp_w_eqs'' mw2'_eq_v2y2 e].
 destruct ex_decomp_w_eqs'' as [w_eq_w1'w2'w3 mw1'_eq_v1y1].

 apply ex_snoc_map in mw1'_eq_v1y1 as ex_snoc_w1.
 destruct ex_snoc_w1 as [w1 ex_snoc_w1'].
 destruct ex_snoc_w1' as [x1 ex_snoc_w1_props].
 destruct ex_snoc_w1_props as [ex_snoc_w1_props' y1_eq_fx1].
 destruct ex_snoc_w1_props' as [w1'_eq_w1x1 fw1_eq_v1].

 apply ex_snoc_map in mw2'_eq_v2y2 as ex_snoc_w2.
 destruct ex_snoc_w2 as [w2 ex_snoc_w2'].
 destruct ex_snoc_w2' as [x2 ex_snoc_w2_props].
 destruct ex_snoc_w2_props as [ex_snoc_w2_props' y2_eq_fx2].
 destruct ex_snoc_w2_props' as [w2'_eq_w2x2 fw2_eq_v2].

 exists w1.
 exists w2.
 exists w3.
 exists x1.
 exists x2.

 rewrite <- w1'_eq_w1x1.
 rewrite <- w2'_eq_w2x2.

 repeat split.

 - exact w_eq_w1'w2'w3.
 - exact mw1'_eq_v1y1.
 - exact mw2'_eq_v2y2.
 - exact mw3_eq_v3.
 - exact fw1_eq_v1.
 - exact fw2_eq_v2.
 - apply eq_sym in y1_eq_fx1. 
   exact y1_eq_fx1.
 - apply eq_sym in y2_eq_fx2. 
   exact y2_eq_fx2.

Defined.


Lemma map_decomp_3_snoc {X Y : Type} (f : X -> Y) (w : @Word X)
  (v1 v2 v3 : @Word Y) (y1 y2 : Y) :
  map_word f w = concat_word (concat_word (snoc v1 y1) (snoc v2 y2)) v3 ->
  { w1 : @Word X & { w2 : @Word X & { w3 : @Word X &
  { x1 : X & { x2 : X & 
  ((w = concat_word (concat_word (snoc w1 x1) (snoc w2 x2)) w3) *
   (f x1 = y1) *
   (f x2 = y2)
  )%type } } } } }.
Proof.
 intro mfw_eq_v1y1v2y2v3.

 apply map_decomp_3_snoc_full in mfw_eq_v1y1v2y2v3 as ex_decomp_w.
 destruct ex_decomp_w as [w1' ex_decomp_w'].
 destruct ex_decomp_w' as [w2' ex_decomp_w''].
 destruct ex_decomp_w'' as [w3 ex_decomp_w'''].
 destruct ex_decomp_w''' as [x1' ex_decomp_w''''].
 destruct ex_decomp_w'''' as [x2' ex_decomp_w_eqs].

 destruct ex_decomp_w_eqs as [ex_decomp_w_eqs' fx2'_eq_y2].
 destruct ex_decomp_w_eqs' as [ex_decomp_w_eqs'' fx1'_eq_y1].
 destruct ex_decomp_w_eqs'' as [ex_decomp_w_eqs2 mfw2'_eq_v2].
 destruct ex_decomp_w_eqs2 as [ex_decomp_w_eqs2' mfw1'_eq_v1].
 destruct ex_decomp_w_eqs2' as [ex_decomp_w_eqs2'' mfw3_eq_v3].
 destruct ex_decomp_w_eqs2'' as [ex_decomp_w_eqs2''' mfw2'x2'_eq_v2y2].
 destruct ex_decomp_w_eqs2''' as [w_eq_w1'x1'w2'x2'w3 mfw1'x1'_eq_v1y1].

 exists w1'.
 exists w2'.
 exists w3.
 exists x1'.
 exists x2'.

 repeat split.

- exact w_eq_w1'x1'w2'x2'w3.
- exact fx1'_eq_y1.
- exact fx2'_eq_y2.
Defined.
