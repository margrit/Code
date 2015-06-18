(* in Idris könnte es so aussehen *)

Variables A B: Prop.

Inductive finite : nat -> Type :=
  new : forall n, finite (S n)
| inj : forall n, finite n -> finite (S n).

(* Isomorphismus *)
Inductive Iso : Type -> Type -> Type :=
  Mk_Iso : A B :Type -> (f: A -> B) -> (g: B -> A) 
  -> (prod a:A, g(f a) = a) 
  -> (prod b:B, f(g b) = b)
  -> Iso A.


Inductive Is_Finite : Type -> Type :=
  Mk_Finite : A : Type -> card : nat 
  -> Iso (A, finite card) -> Is_Finite A.

(* endliche Teilmenge *)
Inductive Finite_Sub: Type -> Type :=
  Mk_Finite_Sub : A : Type -> (card : nat)
  -> (f: A -> finite n) -> (g: (finite n) -> A)
  -> (prod x: finite n (f(g x)=x))
  -> Finite_Sub.


