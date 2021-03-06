Require Import List.

(** Pruefen, ob zwei Listen gleich sind (die gleichen Elemente haben). *)

Fixpoint eqb_list {A : Type} (eqbA: A -> A -> bool) (l l': list A) : bool :=
  match l with
    | nil  =>
      match l' with 
        | nil => true
        | _   => false
      end
    | cons n m  =>
    match l' with
      | nil => false
      | cons n' m' =>andb (eqbA n n') (eqb_list  eqbA m m')
    end
  end.
