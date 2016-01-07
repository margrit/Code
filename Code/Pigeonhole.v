
Load Definitions.
Require Import Fin.
Require Import Arith.
Require Import Decidable.
Require Import Program.

Theorem fin_eq_dec : forall n : nat, forall a b : Finite_Set n, decidable (a = b).
Proof.
intros.
induction n.
- inversion a.
- dependent destruction a;
  dependent destruction b;
  unfold decidable.
 + left.
    reflexivity.
 + right.
    discriminate.
 + right.
    discriminate.
 + destruct (IHn a b).
    * left.
      rewrite H.
      reflexivity.
    * right.

      unfold.
      contradict H.
      inversion H.
      dependent rewrite -> H1.
      injection H.

      


apply IHn a b.
unfold decidable in IHn.
apply IHn

dependent destruction a; dependent destruction b.
unfold decidable.
 left.
 reflexivity.
 unfold decidable.
 right.
 discriminate.
 unfold decidable.
 right.
discriminate.
induction n.
  + inversion a.
  + unfold decidable.
     


Theorem dec_appears_in : forall a : Q, forall l : list Q, decidable (appears_in a l).
Proof.
intros.

Theorem appears_in_Q_size_eq_length 

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
 + apply rp_intr.
     apply IHl.

Show 2.
  apply rp_ext.

