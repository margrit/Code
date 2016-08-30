(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v*)

Require Import List.
Load Word_Prop.

(* Vorkommen von x in einer Liste. *)
Inductive appears_in {X : Type} (a : X) : @Word X -> Type :=
  | ai_here : forall w, appears_in a (snoc w a)
  | ai_later : forall b w, appears_in a w -> appears_in a (snoc w b).

Lemma appears_in_app : forall {X : Type} (w1 w2 : @Word X) (x : X),
     appears_in x (concat_word w1 w2) -> appears_in x w1 + appears_in x w2.
Proof.
  intros X w1 w2 x.
  induction w2.
  - simpl.
    intro H1.
    left.
    assumption.
  - intro H.
    inversion H.
    + right.
      apply ai_here.
    + apply IHw2 in X0.
       destruct X0.
      * { left.
           assumption.
        }
      * { right.
          apply ai_later.
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

(* Wenn x in Liste 1 oder Liste 2 vorkommt, 
dann kommt x auch in der Konkatenation der Listen vor. *)
Lemma app_appears_in : forall {X : Type} (w1 w2 : @Word X) (x : X),
     appears_in x w1 + appears_in x w2 -> appears_in x (concat_word w1 w2).
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

(*Vorkommen von x in einer Teilliste. *)
Lemma appears_in_app_split : forall {X : Type} (x : X) (l : list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x :: l2).
Proof.
  intros X x l A.
  induction A.
  - exists nil.
    exists l.
    simpl.
    reflexivity.
  - destruct IHA as [x0].
    destruct H as [x1].
    exists (b :: x0).
    exists (x1).
    simpl.
    intros.
    rewrite H.
    reflexivity.
Qed.

Inductive repeats {X : Type} : list X -> Type :=
  (* extend *)
| rp_ext : forall x : X, forall l : list X, repeats l -> repeats (x :: l)
| rp_intr : forall x : X, forall l : list X, appears_in x l -> repeats (x :: l).

Lemma repeats_decomp : forall X : Type, forall l : list X,
  repeats l ->
  exists x : X,
  exists xs : list X,
  exists ys : list X,
  exists zs : list X,
  l = xs ++ (x :: ys) ++ (x :: zs).
Proof.
  intros X l H.
  induction H.
  - inversion IHrepeats.
    inversion H0.
    inversion H1.
    inversion H2.
    clear IHrepeats H0 H1 H2.
    exists x0.
    exists (x :: x1).
    exists x2.
    exists x3.
    simpl in *.
    rewrite H3.
    reflexivity.
  - apply appears_in_app_split in a.
    destruct a as [l1].
    destruct H as [l2].
    rewrite H.
    exists x.
    exists nil.
    simpl.
    exists l1.
    exists l2.
    reflexivity.
Qed. 

(*Länge von konkatenierten Listen und einem Element ist gleich. *)
Lemma length_app_2 : forall X:Type, forall x:X, forall xs ys: list X,
  length (xs ++ x :: ys) = length (x :: xs ++ ys).
Proof.
  induction xs.
  - simpl.
    reflexivity.
  - intro ys.
    simpl.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

Lemma map_dec_2 : forall X Y :Type, forall f : X -> Y, forall l : list X,
  forall xs ys : list Y,
  map f l = xs ++ ys -> exists xs' : list X, exists ys' : list X,
  l = xs' ++ ys' /\ map f xs' = xs /\ map f ys' = ys.
Proof.
  intros X Y f.
  induction l.
  (* l = [] *)
  - intros xs ys H.
    exists nil.
    exists nil.
    simpl in H.
    split.
    + simpl.
      reflexivity.
    + assert (xs = nil).
      * { destruct xs.
          - reflexivity.
          - inversion H.
        }
      * { subst.
          simpl in *.
          split.
          - reflexivity.
          - apply H.
        }
  (* l~ = a :: l *)
  - intros xs ys H.
    simpl in H.
    destruct xs as [|x xs].
    (* xs = nil *)
    + simpl in H.
      destruct ys.
      (* ys = nil *)
      * { inversion H. }
      (* ys = y :: ys *)
      * { assert (map f l = ys).
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

Lemma map_dec_3 : forall X Y : Type, forall f : X -> Y, forall l : list X,
  forall xs ys zs : list Y,
  map f l = xs ++ ys ++ zs ->
  exists xs' : list X, exists ys' : list X, exists zs' : list X,
  l = xs' ++ ys' ++ zs' /\
  map f xs' = xs /\ map f ys' = ys /\ map f zs' = zs.
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
