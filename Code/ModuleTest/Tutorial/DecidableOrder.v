Require Import Utf8.

(* File: DecidableOrder.v
 * Part 1
 *)
Module Type Sig.
Parameter A : Type.
Parameter le : A → A → Prop.

Infix "≤" := le : order_scope.
Open Scope order_scope.

Axiom le_refl : ∀ x, x ≤ x.
Axiom le_antisym : ∀ x y, x ≤ y → y ≤ x → x = y.
Axiom le_trans : ∀ x y z, x ≤ y → y ≤ z → x ≤ z.
Axiom le_total : ∀ x y, (x ≤ y) + (y ≤ x).

Parameter le_dec : ∀ x y, (x ≤ y) + (¬ x ≤ y). 
End Sig.


(* File: DecidableOrder.v
 * Part 2
 *)
Module Min (Ord : Sig).
Import Ord.

Hint Resolve le_refl.

Definition min a b : A := if (le_dec a b) then a else b.

Lemma case_min : ∀ P : A -> Type, ∀ x y, (x ≤ y -> P x) -> (y ≤ x -> P y) -> P (min x y).
Proof.
intros.
unfold min.
destruct (le_dec x y).
+ exact (X l).
+ destruct (le_total x y).
  - absurd (le x y).
    * exact n.
    * exact l.
  - exact (X0 l). 
Qed.

Lemma min_glb : ∀ x y z, z ≤ x -> z ≤ y -> z ≤ min x y.
Proof.
intros.
apply case_min.
+ intro; exact H.  
+ intro; exact H0.
Qed.

Lemma min_sym : ∀ x y, min x y = min y x.
Proof.
intros.
set (H:=le_antisym).
(* das schliesst den Beweis ab:
do 2 apply case_min; auto.x *)
(* die Tippeltappeltour geht so : *)
apply case_min.
+ intro.
  apply case_min.
  - intro.
    exact (H _ _ H0 H1).
  - intro.
    exact (H _ _ (le_refl x) (le_refl x)).
+ intro.
  apply case_min.
  - intro.
    exact (H _ _ (le_refl y) (le_refl y)).
  - intro.
    exact (H _ _ H0 H1).
Qed.

Lemma min_left : ∀ x y, min x y ≤ x.
Proof.
intros.
apply case_min; auto.
Qed.

Lemma min_right : ∀ x y, min x y ≤ y.
Proof.
intros.
apply case_min; auto.
Qed.

End Min.