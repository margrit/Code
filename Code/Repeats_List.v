(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v *)

(* Load Word_Prop.*)
Require Import List.

(** Vorkommen von x in einer Liste. *)

Inductive appears_l {X : Type} (a : X) : list X -> Type :=
  | ai_here_l : forall l, appears_l a (a :: l)
  | ai_later_l : forall b l, appears_l a l -> appears_l a (b :: l).

(** Wenn x der Konkatenation zweier Listen vorkommt, dann kommt x in
der ersten oder zweiten Teilliste vor. *)

Lemma appears_l_app : forall {X : Type} (xs ys : list X) (x : X),
      appears_l x (xs ++ ys) -> appears_l x xs + appears_l x ys.
Proof.
  intros X xs ys x.
  induction xs.
  - simpl.
    intro H1.
    right.
    exact H1.
  - intro H.
    inversion H.
    + left.
      apply ai_here_l.
    + apply IHxs in X0.
       inversion H1.
       destruct X0.
      * { left.
           apply ai_later_l.
           exact a0.
        }
      * { right.
           exact a0.
        }
Qed.

(** Liste verknuepft einer Liste mit der leeren Liste ergibt die urspruengliche Liste. *)

Lemma app_l_nil : forall {X : Type} (l : list X),
      l ++ nil = l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* Wenn x in Liste xs oder Liste ys vorkommt,
dann kommt x auch in der Konkatenation der Listen vor. *)

Lemma app_appears_l : forall {X : Type} (xs ys : list X) (x : X),
      appears_l x xs + appears_l x ys -> appears_l x (xs ++ ys).
Proof.
  intros X xs ys x H.
  destruct H as [xInxs | xInys].
  - induction xs.
    + inversion xInxs.
    + inversion xInxs.
      * { apply ai_here_l. }
      * { simpl.
          apply ai_later_l.
          apply IHxs.
          exact X0.
        }
  - induction xs.
    + simpl.
      exact xInys.
    + simpl.
      apply ai_later_l.
      exact IHxs.
Defined.

(** Wenn x in einer Liste vorkommt, dann gibt es eine Zerlegung in zwei
 Teillisten, so dass x Suffix der zweiten Teilliste ist. *)

Lemma appears_l_app_split : forall {X : Type} (x : X) (l : list X),
      appears_l x l ->
      { l1 : list X & { l2 : list X & l = l1 ++ (x :: l2) } }.
Proof.
  intros X x l A.
  induction A.
  - exists nil.
    exists l.
    simpl.
    reflexivity.
  - destruct IHA as [x0].
    destruct s as [x1].
    exists (b :: x0).
    exists (x1).
    simpl.
    intros.
    rewrite e.
    reflexivity.
Defined.

(** Wiederholung von x in einer Liste. *)

Inductive repeats_l {X : Type} : list X -> Type :=
  | rp_ext_l : forall x : X, forall l : list X, repeats_l l -> repeats_l (x :: l)
  | rp_intr_l : forall x : X, forall l : list X, appears_l x l -> repeats_l (x :: l).

(** Wenn es eine Wiederholung von x in einer Liste gibt, so gibt es eine
 Zerledung in drei Teillisten, wobei x Praefix von der zweiten und dritten
 Teilliste ist. *)

Lemma repeats_l_decomp : forall X : Type, forall l : list X,
      repeats_l l ->
      { x : X &
      { xs : list X &
      { ys : list X &
      { zs : list X &
      l = xs ++ (x :: ys) ++ (x :: zs) } } } }.
Proof.
  intros X l H.
  induction H.
  - inversion IHrepeats_l.
    inversion X0.
    inversion X1.
    inversion X2.
    (* clear IHrepeats_l H0 H1 H2. *)
    exists x0.
    exists (x :: x1).
    exists x2.
    exists x3.
    simpl in *.
    rewrite H0.
    reflexivity.
  - apply appears_l_app_split in a.
    destruct a as [l1].
    destruct s as [l2].
    rewrite e.
    exists x.
    exists nil.
    simpl.
    exists l1.
    exists l2.
    reflexivity.
Defined. 

(** Die Laenge von konkatenierten Listen und einem Element ist gleich. *)

Lemma length_app_2_l : forall X:Type, forall x:X, forall xs ys: list X,
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
Defined.

(** Map Funktion auf eine List bestehend aus zwei Teillisten. *)

Lemma map_dec_2_l : forall X Y :Type, forall f : X -> Y, forall l : list X,
      forall xs ys : list Y,
      map f l = xs ++ ys -> { xs' : list X & { ys' : list X &
      l = xs' ++ ys' /\ map f xs' = xs /\ map f ys' = ys } }.
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
            destruct s as [ys'].
            clear IHl.
            destruct a0.
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
          destruct s as [ys'].
          destruct a0.
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
Defined.

(** Map Funktion auf eine List bestehend aus drei Teillisten. *)

Lemma map_decomp_3_l : forall X Y : Type, forall f : X -> Y, forall l : list X,
      forall xs ys zs : list Y,
      map f l = xs ++ ys ++ zs ->
      { xs' : list X & { ys' : list X & { zs' : list X &
      l = xs' ++ ys' ++ zs' /\
      map f xs' = xs /\ map f ys' = ys /\ map f zs' = zs } } }.
Proof.
  intros X Y f l xs ys zs H.
  remember (ys ++ zs) as ls.
  remember H as H2.
  clear HeqH2.
  apply map_dec_2_l in H2.
  destruct H2.
  destruct s.
  destruct a.
  destruct H1.
  exists x.
  rewrite Heqls in H2.
  remember H2 as H3.
  clear HeqH3.
  apply map_dec_2_l in H3.
  destruct H3.
  destruct s.
  destruct a.
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
Defined.

Print nth_error.

(** Zusaetzlich zur Ursprungsdatei wurden noch die beiden nachfolgenden
 Lemmata definiert, um die Indizes der Wiederholungen zu berechnen. *)

Lemma pos_appears_l {A : Type} : forall (a : A) (l : list A), 
      appears_l a l -> {i : nat & nth_error l i  = Some a }.
Proof.
  intros a l ap_a.
  induction ap_a as [l' | a' l' ap_a IHap_a].
  - exists 0.
    simpl.
    reflexivity.
  - destruct IHap_a as [i' nth_i'_eq_a].
    exists (S i').
    simpl.
    exact nth_i'_eq_a.
Defined.

Lemma pos_repeats_l {A : Type} : forall (l : list A), 
      repeats_l l -> {i : nat & { j : nat & nth_error l i = nth_error l j } }.
Proof.
  intros l rp_l.
  induction rp_l. (* as [l' | a' l' rp_a IHrp_a].*)
  - destruct IHrp_l as [i' IH'rp_l].
    destruct IH'rp_l as [j' nth_i'_eq_j'].
    exists (S i').
    exists (S j').
    simpl.
    exact nth_i'_eq_j'.
  - exists 0.
    pose (pos_appears_l x l a).
    destruct s.
    exists (S x0).
    simpl.
    rewrite e.
    reflexivity.
Defined.
