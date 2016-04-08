
(* Erweiterte Überführungsfunktion über *)
Theorem delta_dach_append : forall (xs : list Sigma) (ys : list Sigma) (q : Q),
  delta_dach q (xs ++ ys) = delta_dach (delta_dach q xs) ys.
Proof.
  induction xs.
  - simpl.
    intros ys q.
    reflexivity.
  - simpl.
    intros.
    apply IHxs.
Qed.
