
Load Definitions.
Require Import Fin.
Require Import Arith.
Require Import Decidable.
Require Import Program.

Lemma eq_app : forall (A B : Type) (f : A -> B) (x y  : A), x = y -> (f x = f y).
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Lemma subst : forall {A : Type} {x y : A} (B : A -> Type) (p : x = y), B x -> B y.
Proof.
intros.
destruct p.
assumption.
Defined.


Print subst.
Print eq_rect.
(*
Lemma subst_computation :  forall {A : Type} {x : A} (B : A -> Type) (b : B x), subst B eq_refl b = b.
*)
Lemma eq_app_dep : forall {A : Type} {x y : A} {B : A -> Type} (f : forall (x : A ), (B x)) (p : x = y), 
    (subst B p (f x) = f y).
Proof.
intros.
destruct p.
simpl.
reflexivity.
Defined.

Print projT2.
Print projT1.

Theorem fin_eq_dec : forall n : nat, forall a b : @Fin.t n, decidable (a = b).
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
      simplify_eq.
      dependent destruction H0.
      destruct H.
      reflexivity.
Defined.

(*Theorem dec_appears_in : forall a : Q, forall l : list Q, decidable (appears_in a l).*)

(*Theorem appears_in_Q_size_eq_length *)

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

