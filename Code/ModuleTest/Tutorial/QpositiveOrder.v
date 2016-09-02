(* File: QpositiveOrder.v
 * Part 1
 *)
Require Import Utf8.
Require Export Qpositive_order.
Require DecidableOrder.

Module QDecidableOrderSig <: DecidableOrder.Sig.

Definition A := Qpositive.
Definition le := Qpositive_le.
Definition le_refl := Qpositive_le_refl.
Definition le_antisym := Qpositive_le_antisym.
Definition le_trans := Qpositive_le_trans.
Definition le_total := Qpositive_le_total.
Infix "≤" := le : Qpos_scope.
Bind Scope Qpos_scope with Qpositive. 
Open Scope Qpos_scope.

Lemma le_dec : ∀ x y, {x ≤ y} + {¬ x ≤ y}.
Proof.
intros.
unfold le, Qpositive_le.
decide equality.
Defined.

Print Qpositive_le_total.

End QDecidableOrderSig.