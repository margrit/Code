
(*Load Repeats.
Load Repeats_List. 
Load Pigeonhole_vector.*)


(*--------------------------------------------------------------------------------------------*)

(* Conversion fuer Listen *)

(*--------------------------------------------------------------------------------------------*)

(* Vorbereitung *)

Lemma cons_commute_to_list {A} {n} (v : Vector.t A n) (a : A) : 
                            List.cons a (to_list v) = to_list (Vector.cons A a n v).
Proof.
dependent induction v; compute; reflexivity.
Defined.

Lemma to_list_of_list : forall{A} (l : list A), 
                                   (l = to_list (of_list l)).
Proof.
induction l.
- compute.
  reflexivity.
- simpl.
  rewrite IHl.
  pose (cons_commute_to_list (of_list l) a) as cons_comm.
  rewrite <- IHl in *.
  exact cons_comm.
Defined.


Fixpoint Appears_to_appears_l {A} {n} (v : Vector.t A n) (x : A) (ap_v : Appears_in x v) : 
  appears_l x (to_list v).
Proof.
dependent destruction ap_v.
- pose (cons_commute_to_list v x) as cons_comm.
  rewrite <- cons_comm.
  apply ai_here_l.
- pose (cons_commute_to_list v b) as cons_comm.
  rewrite <- cons_comm.
  apply ai_later_l.
  apply Appears_to_appears_l.
  exact ap_v.
Defined.


Fixpoint Repeats_to_repeats_l {A} {n} (v : Vector.t A n) (rep_v : Repeats v) : 
  repeats_l (to_list v).
Proof.
dependent destruction rep_v.
- pose (cons_commute_to_list v x) as cons_comm.
  rewrite <- cons_comm.
  apply rp_ext_l.
  apply Repeats_to_repeats_l.
  exact rep_v.
- pose (cons_commute_to_list v x) as cons_comm.
  rewrite <- cons_comm.
  apply rp_intr_l.
  apply Appears_to_appears_l.
  exact a.
Defined.


(* Pigeonhole fuer Listen *)

Lemma pigeonhole_l: forall {n} (l : list (@Fin.t n)), length l > n ->
  repeats_l l.
Proof.
intros n l gt_length_q.
pose (of_list l) as v.
unfold gt in gt_length_q.
pose (pigeon_hole_Repeats n (length l) gt_length_q v) as rp.
pose (to_list v) as l'.
pose (to_list_of_list l) as l_v_l.
rewrite l_v_l.
apply Repeats_to_repeats_l.
exact rp.
Defined.


(*--------------------------------------------------------------------------------------------*)

(* Conversion fuer Woerter *)

(*--------------------------------------------------------------------------------------------*)

(* Vorbereitung *)

Definition to_word {A} {n} (v : Vector.t A n) := list_to_word (to_list v).

Definition of_word {A} (w : @Word A) := of_list (word_to_list w).


Lemma to_word_of_word : forall {A} (w : @Word A), 
                                   (w = to_word (of_word w)).
Proof.
unfold of_word in *.
unfold to_word in *.
intros A w.
pose (to_list_of_list (word_to_list w)) as tl_ol.
rewrite <- tl_ol.
apply eq_sym.
apply word_list_word.
Defined.


Lemma lw_pres_repeats {A} (l : list A) :
                        repeats_l l -> Repeats_Word (list_to_word l).
Proof.
intro rp_l.

apply repeats_l_decomp in rp_l as split_l.
destruct split_l as [a split_l'].
destruct split_l' as [l1 [l2 [l3 l_eq_l1al2al3]]].

rewrite <- list_word_list in l_eq_l1al2al3.
repeat rewrite list_to_word_hom in l_eq_l1al2al3.

rewrite l_eq_l1al2al3.
rewrite word_list_word.
rewrite <- concat_word_associative.

pose (lw_concat l1 l2 a) as ex_l1al2.
destruct ex_l1al2 as [w1 [w2 l1al2_eq_w1aw2]].

rewrite l1al2_eq_w1aw2.
rewrite concat_word_associative.
rewrite <- (word_list_word w2).

pose (lw_concat (word_to_list w2) l3 a) as ex_w2al3.
destruct ex_w2al3 as [w2' [w3 w2al3_eq_w2'aw3]].

rewrite w2al3_eq_w2'aw3.
rewrite <- concat_word_associative.

apply Repeats_decomp_rev_w.
exists a.
exists w1.
exists w2'.
exists w3.

reflexivity.
Defined.

Lemma wl_pres_repeats {A} (w : @Word A) :
                  repeats_l (word_to_list w) -> Repeats_Word w.
Proof.
rewrite <- (word_list_word w).
rewrite list_word_list.
apply lw_pres_repeats.
Defined.


(* Pigeonhole fuer Woerter *)

Lemma pigeonhole_w: forall {n} (w : @Word (@Fin.t n)),
                                word_length w > n -> Repeats_Word w.
Proof.
intros n w w_len.
pose (word_to_list w) as w_as_l.
pose (wl_pres_length w) as w_as_l_len.
pose w_len as l_len.
rewrite <- w_as_l_len in l_len.
pose (pigeonhole_l w_as_l l_len) as rp_l.
apply wl_pres_repeats.
exact rp_l.
Defined.


