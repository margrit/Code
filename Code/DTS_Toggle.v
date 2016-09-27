Require DTS_Prop.
Module DTS_Example <: DTS_Def.DTS_Par.
(*Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.*)

Inductive Q' := on : Q' | off : Q'.
Definition Q := Q'.
Inductive Sigma' := press : Sigma'.
Definition Sigma := Sigma'.
Definition is_accepting (q : Q) : Type :=
  match q with
    | on => True
    | off => False
  end.

Definition q0 := off.

(*Definition, welche Uebergaenge moeglich sind.*)
Definition delta (p : Q) (a : Sigma) : Q :=
  match p with
    | on  => off
    | off  => on
  end.

End DTS_Example.

Module Ex_Prop := DTS_Def.DTS_Fun DTS_Example.
Import Word_Prop.
Import DTS_Example.
Import Ex_Prop.
(* Was muss alles bewiesen werden?
- zwei Sprachen definieren
** press gerade
** press ungerade
-> typwertiges Praedikat
*)

Inductive even_press : @Word Sigma -> Type :=
  | eps_even : even_press eps
  | snoc_even {w : @Word Sigma} {a : Sigma} : odd_press w -> even_press (snoc w a)
with odd_press : @Word Sigma -> Type :=
  | snoc_odd {w : @Word Sigma} {a : Sigma} : even_press w -> odd_press (snoc w a).

(* Beweis, dass die Sprache des DTS = odd_press 
- forall w, odd_press w -> Lang_delta w 
  forall w, Lang_delta w -> odd_press w *)

Lemma xyz : forall w,
      ((even_press w * (delta_hat q0 w = off)) +
      (odd_press w * (delta_hat q0 w = on)))%type.
Proof.
  induction w.
  - simpl.
    left.
    split.
    + exact eps_even.
    + reflexivity.
  - simpl.
    destruct IHw as [[peven x] | [podd y]].
    + right.
       split.
       * exact (snoc_odd peven).
       * rewrite x.
         simpl.
         reflexivity.
    + left.
       split.
       * exact (snoc_even podd).
       * rewrite y.
         simpl.
         reflexivity.
Defined.

Lemma even_odd_disjoint (w : @Word Sigma) :
      even_press w -> odd_press w -> False.
Proof.
  intros even odd.
  induction w.
  - inversion odd.
  - inversion even.
    inversion odd.
    exact (IHw X0 X).
Defined.

(* z.z. forall w, Lang_delta w -> odd_press w *)

Lemma lala : forall w, Lang_delta w -> odd_press w.
Proof.
  unfold Lang_delta.
  intros w w_in_L.
  pose (xyz w) as decide_L.
  destruct decide_L as [[even off] |[odd on]].
  - rewrite off in w_in_L.
    simpl in w_in_L.
    destruct w_in_L.
  - exact odd.
Defined.

Lemma lala2 : forall w, odd_press w -> Lang_delta w.
Proof.
  unfold Lang_delta.
  intros w odd.
  pose (xyz w) as decide_L.
  destruct decide_L as [[even off] |[odd' on]].
  - pose (even_odd_disjoint w even odd) as ff.
    destruct ff.
  - rewrite on.
    simpl.
    exact I.
Defined.

(** Aequivalenz zwischen odd_press und Lang_delta. Die Sprache die von dem 
Toggle Automaten akzeptiert wird besteht genau aus den Woertern, deren Laenge
ungerade ist. *)
Require Import Equivalences.
Module Lang_Toggle : Logical_EQ_type_valued_pred.
Definition  base := @Word Sigma.
Definition P := odd_press.
Definition Q := Lang_delta.
Definition pq := lala2.
Definition qp := lala.
End Lang_Toggle.
