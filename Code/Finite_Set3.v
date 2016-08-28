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
  exact (MkIso _ _ id id (fun _ => eq_refl) (fun _ => eq_refl)).  
Defined.

(* inversion of isomorphisms *)
Lemma symIso {A B : Type} : Iso A B -> Iso B A.
Proof.
  intro isoAB.
  destruct isoAB as [to from toFrom fromTo].
  exact (MkIso _ _ from to fromTo toFrom).
Defined.

(* we even have (but never use..) *)
Lemma symIsoIso {A B : Type} : Iso (Iso A B) (Iso B A).
Proof.
  apply (MkIso _ _ symIso symIso);
  intro isoab; destruct isoab; compute; reflexivity.
Defined.
  
(* composition of isomorphisms *)
Lemma transIso {A B C : Type} : Iso B C -> Iso A B -> Iso A C.
Proof.
  intros isoBC isoAB.  
  destruct isoBC as [bc cb bccb cbbc].
  destruct isoAB as [ab ba abba baab].
  apply (MkIso _ _ (bc ∘ ab) (ba ∘ cb)).
  + intro c; compute; rewrite (abba (cb c)); rewrite (bccb c); reflexivity.
  + intro a; compute; rewrite (cbbc (ab a)); rewrite (baab a); reflexivity.
Defined.      

(* "flipped" version just for convenience *)
Lemma transIso' {A B C : Type} : Iso A B -> Iso B C -> Iso A C.
Proof.
  intros isoab isobc.  
  exact (transIso isobc isoab).
Defined.
  
(*
(* with function extensionality, we would even have: *)
Lemma transIsoIso (A B C : Type) (isoBC : Iso B C) : Iso (Iso A B) (Iso A C).
Proof.
  apply (MkIso _ _ (transIso A _ _ isoBC) (transIso A _ _ (symIso _ _ isoBC))).
  + intro isoAB.
    destruct isoAB as [ab ba abba baab].
    destruct isoBC as [bc cb bccb cbbc].

  but not here... 
*)

(* to make proofs more readable: 
   allows reducing goal Iso A' B' to Iso A B
   by giving Iso A A' and Iso B B' *)
Lemma shiftIso {A A' B B' : Type} : 
         Iso A A' -> Iso B B' -> Iso A B -> Iso A' B'.
Proof.
  intros isoaa' isobb' isoab.
  apply (transIso isobb') in isoab as isoab'.
  exact (transIso isoab' (symIso isoaa')).
Defined.

(* finite types *)

Record Finite (X : Type) : Type :=
  MkFinite {
      card : nat;
      isoFin : Iso X (t card)
  }.

Definition FiniteType : Type := sigT Finite.

(* for any cardinality, we have the standard finite type
   of that cardinality *)

Definition FinFinite (card : nat) : FiniteType.
Proof.
  unfold FiniteType.
  exists (t card).
  apply (MkFinite (t card) card (idIso (t card))).
Defined.

(* let's do the operations we need "by hand" *)

(* towards optionFinite *)

Fixpoint optionFinTo {n : nat} (f : t (S n)) : option (t n) :=
match f with
| F1 => None
| FS f' => Some f'
end.
 
Fixpoint optionFinFrom {n : nat} (of : option (t n)) : t (S n) :=
match of with
| None => F1
| Some f' => FS f'
end.

Fixpoint optionFinIso {n : nat} : Iso (t (S n)) (option (t n)).
Proof.
  apply (MkIso (t (S n)) (option (t n)) (@optionFinTo n) (@optionFinFrom n)).
  - induction n; intro b; destruct b; simpl; reflexivity.
  - induction n; intro a; apply (caseS' a); simpl; reflexivity.
Defined.

(* option is a functor: here is map *)
Fixpoint mapOption {A B : Type} (f: A -> B) (oa : option A) : option B :=
match oa with
| None   => None
| Some a => Some (f a)
end.

(* option is a functor: map respects isomorphisms *)
Fixpoint optionIso {A B : Type} (AIsoB : Iso A B) : Iso (option A) (option B).
Proof.
  destruct AIsoB as [ab ba abba baab].
  apply (MkIso (option A) (option B) (mapOption ab) (mapOption ba)).
  - intro ob; destruct ob as [ b | ]; simpl.
    + rewrite (abba b); reflexivity.
    + reflexivity.
  - intro oa; destruct oa as [ a | ]; simpl.
    + rewrite (baab a); reflexivity.
    + reflexivity.
Defined.

(* option induces map FiniteType -> FiniteType *)
Fixpoint optionFinite (X : FiniteType) : FiniteType.
Proof.
  destruct X as [X [cardX isoX]].
  apply optionIso in isoX as isoOXOtc.
  apply (transIso (symIso (@optionFinIso cardX))) in isoOXOtc as isoOXtSc.
  exists (option X).
  apply (MkFinite (option X) (S cardX) isoOXtSc).
Defined.

(* to be done: define Hom, id, comp,... to make FiniteType
   a category and prove that optionFinite canonically extends
   to a functor, i.e. define map, prove id- and comp-preservation,
   and in particular iso-preservation! ... *)

(* any finite type is either isomorphic to False or isomorphic to
   optionFinite of some (t ..) 
   need's a nicer formulation
   have to figure out how this can be used for 
   "induction" analoguous to nat induction    *)
Fixpoint decideFin (X : Type) (Xfin : Finite X) : 
         (Iso X (Fin.t 0)) + {n : nat & Iso X (option (Fin.t n))}.
Proof.
  destruct Xfin as [cardX isoX].
  induction cardX.
  + left; exact isoX.
  + right.
    exists cardX.
    apply (@transIso X (t (S cardX))).
    - apply optionFinIso.    
    - exact isoX.
Defined.

(* towards optionSumIso *)

Fixpoint optionSumTo (X Y : Type) ( sumOXY : (option X) + Y) : option (X + Y) :=
  match sumOXY with
      | (inl None)      => None
      | (inl (Some x))  => Some (inl x)
      | (inr y)         => Some (inr y)
  end.

Fixpoint optionSumFrom (X Y : Type) (oSumXY : option (X + Y)) : (option X) + Y :=
  match oSumXY with
      | None            => inl None
      | Some (inl x)    => inl (Some x)
      | Some (inr y)    => inr y
  end.
                               
Lemma optionSumIso (X Y : Type) : Iso ((option X) + Y) (option (X + Y)).
Proof.
  apply (MkIso _ _ (optionSumTo X Y) (optionSumFrom X Y)).  
  + intro oxy; destruct oxy as [xy | ].    
    - destruct xy; simpl; reflexivity.
    - simpl; reflexivity.
  + intro oxy; destruct oxy as [ox | y].
    - destruct ox as [x | ]; simpl; reflexivity.
    - simpl; reflexivity.
Defined.

(* towards sumCummutative *)
Fixpoint sumFlip (X Y : Type) (xy : X + Y) : (Y + X) :=
  match xy with
      | inl x => inr x
      | inr y => inl y
  end.

Lemma sumCommutative (X Y : Type) : Iso (X + Y) (Y + X).
Proof.
  apply (MkIso _ _ (sumFlip X Y) (sumFlip Y X)).
  intro yx; destruct yx; simpl; reflexivity.
  intro xy; destruct xy; simpl; reflexivity.
Defined.

(* universal property of sum *)

Definition univSum {X Y Z : Type} (f : X -> Z) (g : Y -> Z) (xy: X + Y) : Z :=
  match xy with
      | inl x => f x
      | inr y => g y
  end.

Notation " f ▿ g " := (univSum f g) (at level 10). 

Definition sumMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : 
                  (X + Y) -> (Z + W) := (inl ∘ f) ▿ (inr ∘ g).

Notation " f ⊞ g " := (sumMap f g) (at level 10). 

Lemma sumIso {X Y Z W : Type} (isoXY : Iso X Y) (isoZW : Iso Z W) :
                                       Iso (X + Z) (Y + W).
Proof.
  destruct isoXY as [xy yx xyyx yxxy].
  destruct isoZW as [zw wz zwwz wzzw].
  apply (MkIso _ _ (xy ⊞ zw) (yx ⊞ wz)).
  + intro sumYW; destruct sumYW as [y | w].
    - compute; rewrite (xyyx y); reflexivity.
    - compute; rewrite (zwwz w); reflexivity.
  + intro sumXZ; destruct sumXZ as [x | z].
    - compute; rewrite (yxxy x); reflexivity.
    - compute; rewrite (wzzw z); reflexivity.
Defined.

Lemma sumIsoLeft {X Y : Type} (Z : Type) (isoXY: Iso X Y) : Iso (X + Z) (Y + Z).
Proof.
  exact (sumIso isoXY (idIso Z)).
Defined.  

Lemma sumIsoRight {X Y : Type} (Z : Type) (isoXY: Iso X Y) : Iso (Z + X) (Z + Y).
Proof.
  exact (sumIso (idIso Z) isoXY).
Defined. 

(* we'll often need that (t 0) is uninhabitad, i.e. isomorphic to False *)

Lemma falseFromFin0 (x : t 0) : False.
Proof.
  dependent destruction x.
Defined.

Lemma isoFalseFin0 : Iso False (t 0).
Proof.
  apply (MkIso _ _ (False_rect (t 0)) falseFromFin0).
  + intro x; dependent destruction x.
  + intro a; destruct a.
Defined.

(* in particular, False is Finite *)
Lemma falseIsFinite : Finite False.
Proof.
   apply (MkFinite _ 0).
   exact isoFalseFin0.
Defined.

Lemma sumFalseIso (X : Type) : Iso (False + X) X.
Proof.
  apply (MkIso _ _ ((False_rect X) ▿ id) inr).
  + intro x; compute; reflexivity.
  + intro fx; destruct fx as [f | x].
    - destruct f.  
    - compute; reflexivity.
Defined.

Lemma sumFiniteLemma (n m : nat) : forall (X Y : Type),
                                   (Iso X (Fin.t n)) -> (Iso Y (Fin.t m)) ->
                                   (Iso (X + Y) (Fin.t (n + m))).
Proof.
  induction n.
  + intros X Y isoXt0 isoYtm.
    compute.
    apply (transIso (sumFalseIso (t m))).
    apply (transIso (sumIsoLeft (t m) (symIso isoFalseFin0))).
    exact (sumIso isoXt0 isoYtm).
  + intros X Y isoXtSn isoYtm.
    apply (transIso (symIso (@optionFinIso (n + m)))).
    apply (transIso (optionIso (IHn (t n) (t m) (idIso (t n)) (idIso (t m))))).
    apply (transIso (optionSumIso (t n) (t m))).
    apply (transIso (sumIsoLeft (t m) (@optionFinIso n))).
    exact (sumIso isoXtSn isoYtm).
Defined.
    
Lemma sumFinite (X Y : Type) (Xfin : Finite X) (Yfin : Finite Y) : Finite (X + Y).
Proof.
  destruct Xfin as [cardX isoX].
  destruct Yfin as [cardY isoY].
  apply (MkFinite _ (cardX + cardY)).
  apply (sumFiniteLemma cardX cardY X Y isoX isoY).
Defined.
      
Fixpoint addFinite (X Y : FiniteType) : FiniteType.
Proof.
   destruct X as [X Xfin].
   destruct Y as [Y Yfin].
   exists (sum X Y).
   exact (sumFinite X Y Xfin Yfin).
Defined.
