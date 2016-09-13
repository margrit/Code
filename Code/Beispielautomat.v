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

(*Definition, welche Übergänge möglich sind.*)
Definition delta (p : Q) (a : Sigma) : Q :=
match p with
  | on  => off
  | off  => on
end.

End DTS_Example.

Module Ex_Fun := DTS_Def.DTS_Fun DTS_Example.
Import Word_Prop.
Import DTS_Example.
Import Ex_Fun.
(* Was muss alles bewiesen werden?
- zwei Sprachen definieren
** press gerade
** press ungerade
-> typwertiges Prädikat
*)

Inductive even_press : @Word Sigma -> Type := 
  | eps_even : even_press eps
  | snoc_even {w : @Word Sigma} {a : Sigma} : odd_press w -> even_press (snoc w a)
with odd_press : @Word Sigma -> Type :=
  | snoc_odd {w : @Word Sigma} {a : Sigma} : even_press w -> odd_press (snoc w a).

(* Beweis, dass die Sprache des DTS = even_press 
- forall w, even_press w -> Lang_delta w 
  forall w, Lang_delta w -> even_press w *)

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












