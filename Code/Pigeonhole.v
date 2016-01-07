
Load Definitions.
Require Import Fin.
Require Import Arith.

(* Keine Verwendung von Axiomen. *)
Theorem states_size: forall l : list Q, length l > Q_size ->
  repeats l.
Proof.
induction l.
- intros.
  simpl in H.
  inversion H.
- simpl.
  intros.
  (*induction H.*)
  unfold gt in H.
  unfold lt in H.
  apply le_S_n in H.
  induction H.

(*  + apply rp_ext.
     apply IHl.
     .
*)
Show 2.
  apply rp_ext.

