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
  forall xs ys : @Word Y,
  map_word f w = concat_word xs ys -> exists xs' : @Word X, exists ys' : @Word X,
  w = concat_word xs'  ys' /\ map_word f xs' = xs /\ map_word f ys' = ys.
Proof.
  intros X Y f.
  induction w.
  (* w = eps *)
  - intros xs ys H.
    exists eps.
    exists eps.
    simpl in H.
    split.
    + simpl.
      reflexivity.
    + assert (ys = eps).
      * { destruct ys.
          - reflexivity.
          - inversion H.
        }
      * { subst.
          simpl in *.
          split.
          - exact H.
          - reflexivity.
        }
  (* w = snoc w' a *)
  - intros xs ys H.
    simpl in H.
    destruct xs as [|xs x].
    (* xs = eps *)
    + simpl in H.
      destruct ys.
      (* ys = eps *)
      * { inversion H. }
      (* ys = snoc ys' y *)
      * { simpl in H.
          rewrite concat_word_eps in H.
          inversion H.
          exists eps.
          exists (snoc w a).
          simpl.
          rewrite concat_word_eps.
          split.
          - reflexivity.
          - split ; reflexivity.
        } (**)
    + pose (IHw (snoc xs x) ys).
       assert
       rewrite e.
simpl in H.
 rewrite IHw.


          assert (map_word f w = ys).
          - inversion H.
            reflexivity.
          - set (Hx := IHl nil ys H0).
            destruct Hx as [xs'].
            destruct H1 as [ys'].
            clear IHl.
            destruct H1.
            destruct H2.
            exists nil.
            simpl in *.
            exists (a :: l).
            split.
            + reflexivity.
            + split.
              * { reflexivity. }
              * { simpl.
                  apply H.
                } }
    (* xs = x :: xs *)
    + simpl in H.
      assert (map f l = xs ++ ys).
      * { inversion H.
          reflexivity.
        }
      * { set (Hx := IHl xs ys H0).
          destruct Hx as [xs'].
          destruct H1 as [ys'].
          destruct H1.
          destruct H2.
          clear IHl.
          exists (a :: xs').
          exists ys'.
          subst.
          split.
            - simpl.
              reflexivity.
            - split.
              + simpl.
                inversion H.
                reflexivity.
              + reflexivity.
        } 
Qed.

Lemma map_dec_3 : forall X Y : Type, forall f : X -> Y, forall l : @Word X,
  forall xs ys zs : @Word Y,
  map_word f w = concat_word (concat_word xs ys) zs ->
  exists xs' : @Word X, exists ys' : @Word X, exists zs' : @Word X,
  w = concat_word (concat_word xs' ys') zs' /\
  map_word f xs' = xs /\ map_word f ys' = ys /\ map_word f zs' = zs.
Proof.
  intros X Y f l xs ys zs H.
  remember (ys ++ zs) as ls.
  remember H as H2.
  clear HeqH2.
  apply map_dec_2 in H2.
  destruct H2.
  destruct H0.
  destruct H0.
  destruct H1.
  exists x.
  rewrite Heqls in H2.
  remember H2 as H3.
  clear HeqH3.
  apply map_dec_2 in H3.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  exists x1.
  exists x2.
  subst.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * { reflexivity. }
      * { reflexivity. }
Qed.
