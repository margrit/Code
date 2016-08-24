Require Import Fin.
Require Import Program.


(* type isomorphisms a.s.o. *)

Record Iso (A B : Type) : Type :=
  MkIso {
      to : A -> B;
      from : B -> A;
      toFrom : forall (b : B), (to (from b) = b);
      fromTo : forall (a : A), (from (to a) = a)
  }.

(* identity isomorphism *)
Lemma idIso (A : Type) : Iso A A.
Proof.    
  exact (MkIso A A id id (fun b => eq_refl) (fun b => eq_refl)).  
Defined.

(* inversion of isomorphisms *)
Lemma symIso (A B : Type) : Iso A B -> Iso B A.
Proof.
  intro isoAB.
  destruct isoAB as [to from toFrom fromTo].
  exact (MkIso B A from to fromTo toFrom).
Defined.

(* composition of isomorphisms *)
Lemma transIso (A B C : Type) : Iso B C -> Iso A B -> Iso A C.
Proof.
  intros isoBC isoAB.  
  destruct isoBC as [bc cb bccb cbbc].
  destruct isoAB as [ab ba abba baab].
  cut (forall c : C, bc (ab (ba (cb c))) = c).
    - intro acca.
      cut (forall a : A, ba (cb (bc (ab a))) = a).
      + intro caac.
        exact (MkIso A C (compose bc ab) (compose ba cb) acca caac).
      + intro a.
        rewrite (cbbc (ab a)).
        exact (baab a).
     - intro c.
       rewrite (abba (cb c)).
       exact (bccb c).
Defined.      

(* finite types *)

Record Finite (X : Type) : Type :=
  MkFinite {
      card : nat;
      isoFin : Iso X (@Fin.t card)
  }.

Definition FiniteType : Type :=
  sigT Finite.

(* for any cardinality, we have the standard finite type
   of that cardinality *)

Definition FinFinite (card : nat) : FiniteType.
Proof.
  unfold FiniteType.  
  exact (existT Finite (@Fin.t card) (MkFinite (@Fin.t card) card (idIso (@Fin.t card)))).
Defined.

(* recursion and induction "principles"...
   idea: things about finite types are determined
         if they are determined for the standard finite types
   very preliminary
 *)

Lemma recFinite0 (B : Type) (onFin : forall (card : nat), B) (X : FiniteType) : B.
Proof.
  destruct X as [_ [card _]].
  exact (onFin card).
Defined.

Lemma indFinite0 (B : nat -> Type)
                 (onFin : forall (card : nat), B card)
                 (X : FiniteType) : recFinite0 Type B X.
Proof.
  destruct X as [X [card iso]].
  simpl.
  exact (onFin card).
Defined.

Lemma recFinite (B : Type)
                (onFin : forall (card : nat) (i : @Fin.t card), B)
                {X : FiniteType}
                (x : (projT1 X)) : B.
Proof.
  destruct X as [X [card iso]].
  destruct iso as [to from toFrom fromTo].
  simpl in x.
  exact (onFin card (to x)).
Defined.

(*
Lemma indFinite (B : nat -> Type)
                (onFin : forall (card : nat) (i : @Fin.t card), B card)
                {X : FiniteType}
                (x : (projT1 X)) : recFinite Type ...
*)

(* let's do the operations we need "by hand" *)

Fixpoint optionFin {n : nat} (f : @Fin.t (S n)) : option (Fin.t n) :=
match f with
| F1 => None
| FS f' => Some f'
end.

Fixpoint optionFinite (X : FiniteType) : FiniteType.
Proof.
  destruct X as [X [card iso]].
  destruct iso as [xf fx xffx fxxf].
  assert (oxsf : option X -> @Fin.t (S card)).
  - intro ox.
    induction ox.
    + exact (FS (xf a)).
    + exact F1.
  - assert (sfox : @Fin.t (S card) -> option X).
    + intro sf.
      pose (optionFin sf) as osf.
      induction osf.
      * exact (Some (fx a)).
      * exact None.
    + assert (sfoxoxsf : forall (ox: option X), sfox (oxsf ox) = ox).
      * intro ox.
        induction ox.
        { - compute.