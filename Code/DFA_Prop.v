
(* Erweiterte Überführungsfunktion über *)
Theorem delta_hat_append : forall (xs : list Sigma) (ys : list Sigma) (q : Q),
  delta_hat q (xs ++ ys) = delta_hat (delta_hat q xs) ys.
Proof.
  induction xs.
  - simpl.
    intros ys q.
    reflexivity.
  - simpl.
    intros.
    apply IHxs.
Qed.
