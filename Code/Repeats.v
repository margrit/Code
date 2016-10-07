(** Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v *)

Require Import List.
(* Load Word_Prop. *)


(*---------------------------------------------------------------------------*)

(** * Appears *)

(*---------------------------------------------------------------------------*)

(** Vorkommen von x in einem Word. *)

Inductive Appears_Word {X : Type} (a : X) : @Word X -> Type :=
  | ai_here_w : forall w, Appears_Word a (snoc w a)
  | ai_there_w : forall b w, Appears_Word a w -> Appears_Word a (snoc w b).

(** Wenn x in w1 oder w2 vorkommt, dann kommt x auch in der
 Konkatenation der Woerter vor. *)

Lemma app_Appears_w : forall {X : Type} (w1 w2 : @Word X) (x : X),
      Appears_Word x w1 + Appears_Word x w2
      -> Appears_Word x (concat_word w1 w2).
Proof.
  intros X w1 w2 x H.
  destruct H as [xInw1 | xInw2].
  - induction w2.
    + simpl.
       assumption.
    + inversion xInw1.
      * { rewrite H.
          simpl.
          apply ai_there_w.
          exact IHw2.
        }
      * { simpl.
          apply ai_there_w.
          rewrite H.
          exact IHw2.
        }
  - destruct w1.
    + rewrite concat_word_eps.
      assumption.
    + rewrite commute_snoc_concat_w.
      induction w2.
      * inversion xInw2.
      * simpl. inversion xInw2.
        { apply ai_here_w. }
        { apply ai_there_w.
          apply (IHw2 X0).
        }
Defined.

(** Wenn x im Wort w vorkommt, dann gibt es eine Zerlegung in zwei
 Teilwoertern (w1 w2), wobei x das Suffix von w1 und das Praefix von w2 ist. *)

Lemma Appears_app_split_w : forall {X : Type} (x : X) (w : @Word X),
      Appears_Word x w ->
      { w1 : @Word X & { w2 : @Word X & w = concat_word (snoc w1 x) w2 } }.
Proof.
  intros X x w A.
  induction A.
  - exists w.
    exists eps.
    simpl.
    reflexivity.
  - destruct IHA as [w1' [w2' w_eq_w1'xw2']].
    exists w1'.
    exists (snoc w2' b).
    simpl.
    rewrite w_eq_w1'xw2'.
    reflexivity.
Defined.

(*-------- Das Lemma ist zusaetzlich --------*)

(** Wenn x das Suffix vom ersten Teilwort w1 und Praefix vom zweitem Teilwort
 w2 ist, dann kommt x in der Konkatenation w1 x w2 vor. *)

Lemma Appears_app_split_rev_w {X : Type} (x : X) (w : @Word X) :
      { w1 : @Word X & { w2 : @Word X & w = concat_word (snoc w1 x) w2 } }
      -> Appears_Word x w.
Proof.
  intro ex_decomp.
  destruct ex_decomp as [w1 [w2 w_eq_w1xw2]].
  destruct w2.
  - simpl in w_eq_w1xw2.
    rewrite w_eq_w1xw2.
    apply ai_here_w.
  - simpl in w_eq_w1xw2. 
    rewrite w_eq_w1xw2.
    apply ai_there_w.
    apply app_Appears_w.
    left.
    apply ai_here_w.
Defined.

(*---------------------------------------------------------------------------*)

(** * Repeats *)

(*---------------------------------------------------------------------------*)

(** Mehrfaches Vorkommen von x in einem Wort. *)

Inductive Repeats_Word {X : Type} : @Word X -> Type :=
  (* extend *)
  | rp_intr_w : forall (x : X) (w : @Word X), 
               Appears_Word x w -> Repeats_Word (snoc w x)
  | rp_ext_w : forall (x : X) (w : @Word X),
               Repeats_Word w -> Repeats_Word (snoc w x).

(** Wenn x mehrfach in einem Wort vorkommt, dann gibt es eine Zerlegung in
 drei Teilwoerter, wobei x Suffix von den ersten beiden Teilwoertern ist. *)

Lemma Repeats_decomp_w : forall X : Type, forall w : @Word X,
      Repeats_Word w ->
      { x : X &
      { xs : @Word X &
      { ys : @Word X &
      { zs : @Word X &
      w = concat_word (concat_word (snoc xs x) (snoc ys x)) zs } } } }.
Proof.
  intros X w H.
  induction H.
  - apply Appears_app_split_w in a.
    destruct a as [w1' [w2' w_eq_w1'xw2']].
    exists x.
    exists w1'.
    exists w2'.
    exists eps.
    rewrite w_eq_w1'xw2'.
    simpl.
    reflexivity.
  - destruct IHRepeats_Word as [x'  [xs'  [ys' [zs' w_eq_xs'x'ys'x'zs']]]].
    exists x'.
    exists xs'.
    exists ys'.
    exists (snoc zs' x).
    rewrite w_eq_xs'x'ys'x'zs'.
    simpl.
    reflexivity.
Defined.

(** Wenn es eine Zerlegung in drei Teilwoerter, wobei x Suffix von den ersten
 beiden Teilwoertern ist, dann kommt x mehrfach in einem Wort vor. *)

Lemma Repeats_decomp_rev_w {X : Type} : forall w : @Word X,
      { x : X &
      { xs : @Word X &
      { ys : @Word X &
      { zs : @Word X &
      w = concat_word (concat_word (snoc xs x) (snoc ys x)) zs } } } }
      -> Repeats_Word w.
Proof.
  intros w decomp_w.

  destruct decomp_w as [a [w1 [w2 [w3 w_eq_w1aw2aw3]]]].

  simpl (concat_word (snoc w1 a) (snoc w2 a)) in w_eq_w1aw2aw3.
  rewrite w_eq_w1aw2aw3. 
  clear w_eq_w1aw2aw3.
  induction w3.
  - simpl in *. 
    apply rp_intr_w.
    apply app_Appears_w.
    left.
    apply ai_here_w.
  - simpl in *.
    apply rp_ext_w.
    exact IHw3.
Defined.

