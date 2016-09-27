Load DFA_Def.
Load FiniteClass.

(* Q x (Sigma u {eps}) -> P(Q), wobei P die Potenzmenge beschreibt.*)

(* Definition Included (B C: Q) : Set := forall x: list Q, In B x -> In C x.
*)
Variable U : Type.
Definition Ensemble := U -> Prop.
Definition In (A:Ensemble) (x:U) : Prop := A x.
Definition Included (B C: Ensemble) : Prop :=  forall x : U, In B x -> In C x.
Inductive Empty_set : Ensemble :=.

  Inductive Full_set : Ensemble :=
    Full_intro : forall x:U, In Full_set x.


(*Inductive Power_set (A:Ensemble U) : Ensemble (Ensemble U) :=
    Definition_of_Power_set :
      forall X:Ensemble U, Included U X A -> In (Ensemble U) (Power_set A) X.
*)
Print Included.

Inductive Power (A : list Q) : list (list Q) :=
    Definition_of_Power :
      forall X: list Q, Included Q X A -> In (list Q) (Power A) X.

(*
Plan n-elementige Teilmengen von [a, b, c, d] mit Iso zu Fin.4 mit a->0, b->1 ...
n aus @Fin.t card +1
n=0 ist [ø]
einelementige Teilmengen für card n > 0
[ø]
    [{a}, {b}, {c}, {d}]
                              [{a,b}, {a,c}, {a,d}, {b,c}, {b,d}]
*)
Inductive Power (X : Set) (X_is_Finite : Finite X) : Type :=
  match card X with
    | 0    => @Fin.t 1
    | S _ => Power
  end.

Definition Power_Q := Power_set Q.
Print Power_Q.

(** Die Transitionsfunktion - delta.*)
Parameter nfa_delta : Q -> Sigma -> Power_Q.

Fixpoint nfa_delta_hat (q : Q) (w eps : @Word Sigma) : Power_Q :=
   match w with
    | eps          => q
    | snoc w' h => delta (delta_hat q w' ) h
  end.
