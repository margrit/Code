Load Finite_Set2.

(* recursion and induction "principles"...
   idea: things about finite types are determined
         if they are determined for the standard finite types
   very preliminary
*)

Lemma recFinite0 (B : Type) (onFin : forall (card : nat), B) (X : FiniteType) : B.
Proof.
  destruct X as [_ [card _]].
  exact (onFin card).
Defined.

Lemma indFinite0 (B : nat -> Type)
                 (onFin : forall (card : nat), B card)
                 (X : FiniteType) : recFinite0 Type B X.
Proof.
  destruct X as [X [card iso]].
  simpl.
  exact (onFin card).
Defined.

Lemma recFinite (B : Type)
                (onFin : forall (card : nat) (i : @Fin.t card), B)
                {X : FiniteType}
                (x : (projT1 X)) : B.
Proof.
  destruct X as [X [card iso]].
  destruct iso as [to from toFrom fromTo].
  simpl in x.
  exact (onFin card (to x)).
Defined.

(*
Lemma indFinite (B : nat -> Type)
                (onFin : forall (card : nat) (i : @Fin.t card), B card)
                {X : FiniteType}
                (x : (projT1 X)) : recFinite Type ...
*)