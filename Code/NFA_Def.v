Load DFA_Def.

(* Q x (Sigma u {eps}) -> P(Q), wobei P die Potenzmenge beschreibt.*)

(* Definition Included (B C: Q) : Set := forall x: list Q, In B x -> In C x.

Inductive Power_set (A: list Q) : list Q :=
    Definition_of_Power_set :
      forall X: list Q, Included U X A -> In (list Q) (Power_set A) X.
 *)
Definition Power_Q := Power_set Q.
Print Power_Q.

(** Die Transitionsfunktion - delta.*)
Parameter nfa_delta : Q -> Sigma -> Power_Q.

Fixpoint nfa_delta_hat (q : Q) (w eps : @Word Sigma) : Power_Q :=
   match w with
    | eps          => q
    | snoc w' h => delta (delta_hat q w' ) h
  end.
