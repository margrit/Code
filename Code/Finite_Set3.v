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

Notation " A ≅ B " := (Iso A B) (at level 9).

(* identity isomorphism *)
Lemma idIso (A : Type) : A ≅ A.
Proof.    
  exact (MkIso _ _ id id (fun _ => eq_refl) (fun _ => eq_refl)).  
Defined.

(* inversion of isomorphisms *)
Lemma symIso {A B : Type} : A ≅ B -> B ≅ A.
Proof.
  intro isoAB.
  destruct isoAB as [to from toFrom fromTo].
  exact (MkIso _ _ from to fromTo toFrom).
Defined.

(* we even have (but never use..) *)
Lemma symIsoIso {A B : Type} : (A ≅ B) ≅ (B ≅ A).
Proof.
  apply (MkIso _ _ symIso symIso);
  intro isoab; destruct isoab; compute; reflexivity.
Defined.
  
(* composition of isomorphisms *)
Lemma transIso {A B C : Type} : B ≅ C -> A ≅ B -> A ≅ C.
Proof.
  intros isoBC isoAB.  
  destruct isoBC as [bc cb bccb cbbc].
  destruct isoAB as [ab ba abba baab].
  apply (MkIso _ _ (bc ∘ ab) (ba ∘ cb)).
  + intro c; compute; rewrite (abba (cb c)); rewrite (bccb c); reflexivity.
  + intro a; compute; rewrite (cbbc (ab a)); rewrite (baab a); reflexivity.
Defined.      

(* "flipped" version just for convenience *)
Lemma transIso' {A B C : Type} : A ≅ B -> B ≅ C -> A ≅ C.
Proof.
  intros isoab isobc.  
  exact (transIso isobc isoab).
Defined.
  
(*
(* with function extensionality, we would even have: *)
Lemma transIsoIso (A B C : Type) (isoBC : B ≅ C) : (A ≅ B) ≅ (A ≅ C).

  but not here... 
*)

(* to make proofs more readable: 
   allows reducing goal Iso A' B' to Iso A B
   by giving Iso A A' and Iso B B' *)
Lemma shiftIso {A A' B B' : Type} : A ≅ A' -> B ≅ B' -> A ≅ B -> A' ≅ B'.
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

(* towards optionFinIso *)

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

(* option is a functor *)
Fixpoint mapOption {A B : Type} (f: A -> B) (oa : option A) : option B :=
match oa with
| None   => None
| Some a => Some (f a)
end.

(* option is a functor: map respects isomorphisms *)
Fixpoint optionIso {A B : Type} (isoAB : A ≅ B) : (option A) ≅ (option B).
Proof.
  destruct isoAB as [ab ba abba baab].
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
         (X ≅ (t 0)) + {n : nat & X ≅ (option (t n))}.
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

(* universal property of sum *)

Definition univSum {X Y Z : Type} (f : X -> Z) (g : Y -> Z) (xy: X + Y) : Z :=
  match xy with
      | inl x => f x
      | inr y => g y
  end.

Notation " f ▿ g " := (univSum f g) (at level 10). 

(* sum is a functor in both arguments *)

Definition sumMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : 
                  (X + Y) -> (Z + W) := (inl ∘ f) ▿ (inr ∘ g).

Notation " f ⊞ g " := (sumMap f g) (at level 10). 

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
                               
Lemma optionSumIso (X Y : Type) : ((option X) + Y) ≅ (option (X + Y)).
Proof.
  apply (MkIso _ _ (optionSumTo X Y) (optionSumFrom X Y)).  
  + intro oxy; destruct oxy as [xy | ].    
    - destruct xy; simpl; reflexivity.
    - simpl; reflexivity.
  + intro oxy; destruct oxy as [ox | y].
    - destruct ox as [x | ]; simpl; reflexivity.
    - simpl; reflexivity.
Defined.

(* sum is commutative (up to iso) *)

Lemma sumCommutative (X Y : Type) : (X + Y) ≅ (Y + X).
Proof.
  apply (MkIso (X + Y) (Y + X) (inr ▿ inl) (inr ▿ inl));
  intro xy; destruct xy; simpl; reflexivity.
Defined.

(* sum is a functor: it respects isomorphisms *)

Lemma sumIso {X Y Z W : Type} : X ≅ Y -> Z ≅ W -> (X + Z) ≅ (Y + W).
Proof.
  intros isoXY isoZW.
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

Lemma sumIsoLeft {X Y : Type} (Z : Type) (isoXY: X ≅ Y) : (X + Z) ≅ (Y + Z).
Proof.
  exact (sumIso isoXY (idIso Z)).
Defined.  

Lemma sumIsoRight {X Y : Type} (Z : Type) (isoXY: X ≅ Y) : (Z + X) ≅ (Z + Y).
Proof.
  exact (sumIso (idIso Z) isoXY).
Defined. 

(* we'll often need that (t 0) is uninhabitad, i.e. isomorphic to False *)

Lemma falseFromFin0 (x : t 0) : False.
Proof.
  dependent destruction x.
Defined.

Lemma isoFalseFin0 : False ≅ (t 0).
Proof.
  apply (MkIso _ _ (False_rect (t 0)) falseFromFin0).
  + intro x; dependent destruction x.
  + intro a; destruct a.
Defined.

(* in particular, False is Finite *)
Lemma falseIsFinite : Finite False.
Proof.
   exists 0.
   exact isoFalseFin0.
Defined.

(* t 1 is isomorphic to True *)
Lemma isoTrueFin1 : True ≅ (t 1).
Proof.
  apply (MkIso _ _ (fun _ => F1) (fun _ => I)).
  + intro i.
    dependent destruction i.
    - reflexivity.
    - dependent destruction i.
  + intro a; destruct a; reflexivity.      
Defined.
    
Lemma trueIsFinite : Finite True.
Proof.
  exists 1.
  exact isoTrueFin1.
Defined.

(* False is neutral element for + *)
Lemma sumFalseIso (X : Type) : (False + X) ≅ X.
Proof.
  apply (MkIso _ _ ((False_rect X) ▿ id) inr).
  + intro x; compute; reflexivity.
  + intro fx; destruct fx as [f | x].
    - destruct f.  
    - compute; reflexivity.
Defined.

(* (t 0) is also neutral for + *)
Lemma sumFin0Iso (X : Type) : ((t 0) + X) ≅ X.
Proof.
  apply (transIso (sumFalseIso X)).
  exact (sumIsoLeft X (symIso isoFalseFin0)).
Defined.

(* adding (t 1) is option *)
Fixpoint sumFin1IsoTo (X : Type) (t1X : (t 1) + X ) : (option X) :=
   match t1X with
   | inl _ => None
   | inr x => Some x
   end.

Fixpoint sumFin1IsoFrom (X : Type) (OX : option X) : (t 1) + X  :=
   match OX with
   | None   => inl F1
   | Some x => inr x
   end.

Lemma sumFin1Iso (X : Type) : ((t 1) + X) ≅ (option X).
Proof.
  apply (MkIso _ _ (sumFin1IsoTo X) (sumFin1IsoFrom X)).
  + intro OX; destruct OX; simpl; reflexivity.
  + intro sumt1X; destruct sumt1X as [t | x].
    - simpl. 
      dependent destruction t. 
      * reflexivity.
      * dependent destruction t.
    - simpl; reflexivity.
Defined.

Lemma sumFin1FinNIso (n : nat) : ((t 1) + (t n)) ≅ (t (S n)).
Proof.
  apply (transIso (symIso (@optionFinIso n))).
  exact (sumFin1Iso (t n)).
Defined.

(* the sum of two finite types is finite *)

Lemma sumIsFiniteLemma (n m : nat) : forall (X Y : Type),
                          (X ≅ (t n)) -> (Y ≅ (t m)) -> ((X + Y) ≅ (t (n + m))).
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
    
Lemma sumIsFinite (X Y : Type) (Xfin : Finite X) (Yfin : Finite Y) : Finite (X + Y).
Proof.
  destruct Xfin as [cardX isoX].
  destruct Yfin as [cardY isoY].
  apply (MkFinite _ (cardX + cardY)).
  apply (sumIsFiniteLemma cardX cardY X Y isoX isoY).
Defined.
      
Fixpoint sumFinite (X Y : FiniteType) : FiniteType.
Proof.
   destruct X as [X Xfin].
   destruct Y as [Y Yfin].
   exists (sum X Y).
   exact (sumIsFinite X Y Xfin Yfin).
Defined.

(* towards prodFinite *)
(* universal property of prod *)

Definition univProd {X Y Z : Type} (f : X -> Y) (g : X -> Z) (x : X) : Y * Z :=
   (f x , g x).

Notation " f ▵ g " := (univProd f g) (at level 10). 

(* prod is a functor in both arguments *)

Definition prodMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : 
                  (X * Y) -> (Z * W) := (f ∘ fst) ▵ (g ∘ snd).

Notation " f ⊠ g " := (prodMap f g) (at level 10). 


(* prod is commutative *)
Lemma prodCommutative (X Y : Type) : (X * Y) ≅ (Y * X).
Proof.
  apply (MkIso (X * Y) (Y * X) (snd ▵ fst) (snd ▵ fst));
  intro pair; destruct pair; compute; reflexivity.
Defined.    

(* prod is a functor: it respects isomorphisms *)
Lemma prodIso {X Y Z W : Type} : X ≅ Y -> Z ≅ W -> (X * Z) ≅ (Y * W).
Proof.
  intros isoXY isoZW. 
  destruct isoXY as [xy yx xyyx yxxy].
  destruct isoZW as [zw wz zwwz wzzw].
  apply (MkIso _ _ (xy ⊠ zw) (yx ⊠ wz)).
  + intro pairYW; destruct pairYW as [y w];
    compute; rewrite (xyyx y); rewrite (zwwz w); reflexivity.
  + intro pairXZ; destruct pairXZ as [x z];
    compute; rewrite (yxxy x); rewrite (wzzw z); reflexivity.
Defined.

Fixpoint prodIsoLeft {X Y : Type} (Z : Type) (isoXY : X ≅ Y) : (X * Z) ≅ (Y * Z) :=
                                  (prodIso isoXY (idIso Z)).

Fixpoint prodIsoRight {X Y : Type} (Z : Type) (isoXY : X ≅ Y) : (Z * X) ≅ (Z * Y) :=
                                  (prodIso (idIso Z) isoXY).

Lemma prodFalseIso (X : Type) : (False * X) ≅ False.  
Proof.
  apply (MkIso _ _ fst (id ▵ (False_rect X))).
  + intro f; destruct f.
  + intro fx; destruct fx as [f x]. destruct f.
Defined.

Lemma prodTrueIso (X : Type) : (True * X) ≅ X.
Proof.
  apply (MkIso _ _ snd ((fun _ => I) ▵ id)).
  + intro x; compute; reflexivity.
  + intro tx; destruct tx as [t x]; destruct t; compute; reflexivity.
Defined.

Fixpoint prodDistSumIsoTo (X Y Z : Type) (xyz : X * (Y + Z)) : (X * Y) + (X * Z) :=
  match xyz with
  | (x , inl y) => inl (x , y)
  | (x , inr z) => inr (x , z)
  end.

Lemma prodDistSumIsoLeft (X Y Z : Type) : (X * (Y + Z)) ≅ ((X * Y) + (X * Z)).
Proof.
  apply (MkIso _ _ (prodDistSumIsoTo X Y Z) ((id ⊠ inl) ▿ (id ⊠ inr))).
  + intro sumXYXZ; destruct sumXYXZ as [pair | pair];
    destruct pair; compute; reflexivity.
  + intro pairXSumYZ. 
    destruct pairXSumYZ as [x [y | z]]; compute; reflexivity.
Defined.

Lemma prodDistSumIsoRight (X Y Z : Type) : ((Y + Z) * X) ≅ ((Y * X) + (Z * X)). 
Proof.
  apply (shiftIso (prodCommutative X (Y + Z)) 
                  (sumIso (prodCommutative X Y) (prodCommutative X Z))).
  exact (prodDistSumIsoLeft X Y Z).
Defined.


Lemma prodIsFiniteLemma (n m : nat) : forall (X Y : Type),
                                   (Iso X (t n)) -> (Iso Y (t m)) ->
                                   (Iso (X * Y) (t (n * m))).
Proof.
  induction n.
  + intros X Y isoXt0 isoYtm.
    compute.
    apply (transIso isoFalseFin0).
    apply (transIso (prodFalseIso (t m))).
    apply (transIso (prodIsoLeft (t m) (symIso isoFalseFin0))).
    exact (prodIso isoXt0 isoYtm).
  + intros X Y isoXtSn isoYtm.
    apply (transIso (sumIsFiniteLemma _ _ _ _ (idIso (t m)) 
                   (idIso (t (n * m))))).
    apply (transIso (sumIsoRight (t m) (IHn (t n) (t m) (idIso _) (idIso _)))).
    pose (prodTrueIso (t m)).
    apply (transIso (sumIsoLeft (t n * t m) (prodTrueIso (t m)))).
    apply (transIso (sumIsoLeft (t n * t m) (prodIsoLeft (t m) (symIso (isoTrueFin1))))).
    apply (transIso (prodDistSumIsoRight (t m) (t 1) (t n))).
    apply (transIso (prodIsoLeft (t m) (symIso (sumFin1FinNIso n)))).
    exact (prodIso isoXtSn isoYtm).
Defined.

Lemma prodIsFinite (X Y : Type) (Xfin : Finite X) (Yfin : Finite Y) : Finite (X * Y).
Proof.
   destruct Xfin as [cardX isoX].
   destruct Yfin as [cardY isoY].
   apply (MkFinite _ (cardX * cardY)).
   apply (prodIsFiniteLemma cardX cardY X Y isoX isoY).
Defined.

Lemma prodFinite (X Y : FiniteType) : FiniteType.
Proof.
   destruct X as [X Xfin].
   destruct Y as [Y Yfin].
   exists (prod X Y).
   exact (prodIsFinite X Y Xfin Yfin).
Defined.
