(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v*)

Require Import List.
Load Word_Prop.

(* Vorkommen von x in einem Word. *)
Inductive Appears_Word {X : Type} (a : X) : @Word X -> Type :=
  | ai_here_w : forall w, Appears_Word a (snoc w a)
  | ai_there_w : forall b w, Appears_Word a w -> Appears_Word a (snoc w b).
(*
Lemma Appears_app_w : forall {X : Type} (w1 w2 : @Word X) (x : X),
     Appears_Word x (concat_word w1 w2) -> Appears_Word x w1 + Appears_Word x w2.
Proof.
  intros X w1 w2 x.
  induction w2.
  - simpl.
    intro H1.
    left.
    assumption.
  - intro H.
    inversion H as [w [w_eq_w1w2 x_eq_a] | x' w App_x_w1w2 [w_eq_w1w2 x'_eq_a ]].
    + right.
      apply ai_here_w.
    + apply IHw2 in App_x_w1w2.
       destruct App_x_w1w2.
      * { left.
           assumption.
        }
      * { right.
          apply ai_there_w.
          assumption.
        }
Qed.

(* Liste verknüpft mit der leeren Liste ergibt die ursprüngliche Liste *)
Lemma app_w_nil : forall {X : Type} (w : @Word X),
 concat_word w eps = w.
Proof.
intros.
simpl.
reflexivity.
Qed.
(*
(* Wenn x in Liste 1 oder Liste 2 vorkommt, 
dann kommt x auch in der Konkatenation der Listen vor. *)
Lemma app_Appears : forall {X : Type} (w1 w2 : @Word X) (x : X),
     Appears x w1 + Appears x w2 -> Appears x (concat_word w1 w2).
Proof.
  intros X w1 w2 x H.
  destruct H as [xInw1 | xInw2].
  - induction w2.
    + simpl.
       assumption.
    + inversion xInw1.
      * { rewrite H.
...
          apply IHw2.
          apply ai_here. }
      * { simpl.
          apply ai_later.
          apply IHxs.
          assumption.
        }
  - induction xs.
    + simpl.
      assumption.
    + simpl.
      apply ai_later.
      assumption.
Qed.
*)*)
(*Vorkommen von x in einer Teilliste. *)
Lemma Appears_app_split_w : forall {X : Type} (x : X) (w : @Word X),
  Appears_Word x w ->
  exists w1, exists w2, w = concat_word (snoc w1 x) w2.
Proof.
  intros X x w A.
  induction A.
  - exists w.
    exists eps.
    simpl.
    reflexivity.
  - destruct IHA as [w1'].
    destruct H as [w2'].
    exists w1'.
    exists (snoc w2' b).
    simpl.
    rewrite H.
    reflexivity.
Qed.

Inductive Repeats_Word {X : Type} : @Word X -> Type :=
  (* extend *)
| rp_intr_w : forall x : X, forall w : @Word X, Appears_Word x w -> Repeats_Word (snoc w x)
| rp_ext_w : forall x : X, forall w : @Word X, Repeats_Word w -> Repeats_Word (snoc w x).

(*Das müsste die eigentliche Zerlegung eines Wortes sein, die für das Pumping Lemma benötigt wird.*)
Lemma Repeats_decomp_w : forall X : Type, forall w : @Word X,
  Repeats_Word w ->
  exists x : X,
  exists xs : @Word X,
  exists ys : @Word X,
  exists zs : @Word X,
  w = concat_word (concat_word (snoc xs x) (snoc ys x)) zs.
Proof.
  intros X w H.
  induction H.
  - apply Appears_app_split_w in a.
    destruct a as [w1'].
    destruct H as [w2'].
    exists x.
    exists w1'.
    exists w2'.
    exists eps.
    rewrite H.
    simpl.
    reflexivity.
  - destruct IHRepeats_Word as [x'  IH].
    destruct IH as [xs'  IH].
    destruct IH as [ys'  IH].
    destruct IH as [zs'  IH].
    exists x'.
    exists xs'.
    exists ys'.
    exists (snoc zs' x).
    rewrite IH.
    simpl.
    reflexivity.
Qed.

(*Länge von konkatenierten Listen und einem Element ist gleich. *)
Lemma length_app_2_w : forall X:Type, forall x:X, forall xs ys: @Word X,
  word_length (concat_word (snoc xs x) ys) = word_length (concat_word xs (snoc ys x)).
Proof.
  induction ys.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHys.
    simpl.
    reflexivity.
Qed.

Lemma map_decomp_2_w : forall X Y :Type, forall f : X -> Y, forall w : @Word X,
  forall v1 v2 : @Word Y,
  map_word f w = concat_word v1 v2 -> exists w1 : @Word X, exists w2 : @Word X,
  w = concat_word w1 w2 /\ map_word f w1 = v1 /\ map_word f w2 = v2.
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
  exists w1 : @Word X, exists w2 : @Word X, exists w3 : @Word X,
  w = concat_word (concat_word w1 w2) w3 /\
  map_word f w1 = v1 /\ map_word f w2 = v2 /\ map_word f w3 = v3.
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
