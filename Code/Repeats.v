(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v*)

Require Import List.
(* Require Import Arith. *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
  least once as a member of a list [l]. 
   Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs ys x.
  induction xs. 
  - simpl. 
    intros.
    right.
    assumption.
  - intros H.
    inversion H.
    + left.
      apply ai_here.
    + apply IHxs in H1.
      inversion H1.
      * left.
        apply ai_later.
        assumption.
      * right.
        assumption.
Qed.

Lemma app_l_nil: forall {X:Type} (l: list X),
  l ++ nil = l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x H.
  destruct H.
  - induction xs.
    + inversion H.
    + inversion H.
      * apply ai_here.
      * simpl.
        apply ai_later.
        apply IHxs.
        assumption.
  - induction xs.
    + simpl.
      assumption.
    + simpl.
      apply ai_later.
      assumption.
Qed.
  
Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l A.
  induction A.
  - exists nil. 
    exists l. 
    simpl.
    reflexivity.
  - destruct IHA as [x0]. 
    destruct H as [x1].
    exists (b::x0).
    exists (x1).
    simpl. 
    congruence.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  (* extend *)
  rp_ext : forall x:X, forall l: list X, 
   repeats l -> repeats (x::l) |
  rp_intr : forall x:X, forall l: list X,
    appears_in x l -> repeats (x :: l).

Lemma repeats_decomp: forall X: Type, forall l: list X,
  repeats l -> 
  exists x:X, 
  exists xs: list X, 
  exists ys: list X,
  exists zs: list X,
  l = xs ++ (x::ys) ++ (x::zs).
Proof.
  intros X l H.
  induction H.
  - inversion IHrepeats.
    inversion H0.
    inversion H1.
    inversion H2.
    clear IHrepeats H0 H1 H2.
    exists x0. 
    exists (x::x1). 
    exists x2. 
    exists x3.
    simpl in *. 
    congruence.
  - apply appears_in_app_split in H.
    destruct H as [l1].
    destruct H as [l2].
    rewrite H.
    exists x. 
    exists nil. 
    simpl. 
    exists l1. 
    exists l2.
    reflexivity.
Qed. 


Lemma length_app_2 : forall X:Type, forall x:X, forall xs ys: list X,
  length (xs ++ x :: ys) = length (x :: xs ++ ys).
Proof.
  induction xs.
  - simpl. 
    reflexivity.
  - intros. 
    simpl. 
    rewrite IHxs. 
    simpl.
    reflexivity.
Qed.
Lemma map_dec_2 : forall X Y:Type, forall f: X->Y, forall l: list X,
  forall xs ys: list Y, 
  map f l = xs ++ ys -> exists xs': list X, exists ys': list X,
  l = xs' ++ ys' /\ map f xs' = xs /\ map f ys' = ys.
Proof.
  intros X Y f. 
  induction l.
  (* l = [] *)
  - intros. 
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

Lemma map_dec_3 : forall X Y:Type, forall f: X->Y, forall l: list X,
  forall xs ys zs: list Y, 
  map f l = xs ++ ys ++ zs -> 
  exists xs': list X, exists ys': list X, exists zs': list X,
  l = xs' ++ ys' ++ zs' /\ 
  map f xs' = xs /\ map f ys' = ys /\ map f zs' = zs.
Proof.
  intros.
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