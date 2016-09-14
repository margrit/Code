Module Type Logical_EQ.
Parameter A : Type.
Parameter B : Type.
Parameter ab : A -> B.
Parameter ba : B -> A.
End Logical_EQ.

Module Type ISO.
Parameter A : Type.
Parameter B : Type.
Parameter ab : A -> B.
Parameter ba : B -> A.
Axiom abba : forall b : B, ab (ba b) = b.
Axiom baab : forall a : A, ba (ab a) = a.
End ISO.

Module ISO_EQ (iso : ISO) : Logical_EQ.
Import iso.
Definition A := A.
Definition B := B.
Definition ab := ab.
Definition ba := ba.
End ISO_EQ.

Module Type Logical_EQ_type_valued_pred.
Parameter base : Type.
Parameter P : base -> Type.
Parameter Q : base -> Type.
Parameter pq : forall b : base, P b -> Q b.
Parameter qp : forall b : base, Q b -> P b.
End Logical_EQ_type_valued_pred.


