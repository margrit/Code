Require Import Nat.
Require Import Fin.
Require Import Vector.
Require Import Program.

(****************)
(* Isomorphisms *)
(****************)

(* isomorphism of Types *)
Record Iso (A B : Type) : Type :=
  MkIso {
      to :     A -> B;
      from :   B -> A;
      toFrom : forall (b : B), (to (from b) = b);
      fromTo : forall (a : A), (from (to a) = a)
  }.

Notation " A ≅ B " := (Iso A B) (at level 9).

(* identity isomorphism *)
Definition idIso (A : Type) : A ≅ A := 
  (MkIso _ _ id id (fun _ => eq_refl) (fun _ => eq_refl)).

(* inversion of isomorphisms *)
Definition symIso {A B : Type} : A ≅ B -> B ≅ A.
Proof.
  intro isoAB.
  destruct isoAB as [to from toFrom fromTo].
  exact (MkIso _ _ from to fromTo toFrom).
Defined.

(* we even have (but never use..) *)
Lemma symIsoIso {A B : Type} : (A ≅ B) ≅ (B ≅ A).
Proof.
  apply (MkIso _ _ symIso symIso);
  intro isoab; destruct isoab; simpl; reflexivity.
Defined.
  
(* composition of isomorphisms *)
Definition transIso {A B C : Type} : B ≅ C -> A ≅ B -> A ≅ C.
Proof.
  intros isoBC isoAB.  
  destruct isoBC as [bc cb bccb cbbc].
  destruct isoAB as [ab ba abba baab].
  apply (MkIso _ _ (bc ∘ ab) (ba ∘ cb)).
  + intro c; compute; rewrite (abba (cb c)); rewrite (bccb c); reflexivity.
  + intro a; compute; rewrite (cbbc (ab a)); rewrite (baab a); reflexivity.
Defined.      

(* ∘≅  = \circ\cong *)
Notation " iso1 ∘≅ iso2 " := (transIso iso1 iso2) (at level 20).

Definition flipTransIso {A B C : Type} : A ≅ B -> B ≅ C -> A ≅ C.
Proof.
   intros isoAB isoBC.  
   exact (isoBC ∘≅ isoAB).
Defined.

(* ⇛  = \Rrightarrow , ⇚  = \Lleftarrow *)
Notation " iso ⇛ " := (transIso iso) (at level 19).
Notation " iso ⇚ " := (transIso (symIso iso)) (at level 19).
Notation " ⇛ iso " := (flipTransIso iso) (at level 19).
Notation " ⇚ iso " := (flipTransIso (symIso iso)) (at level 19).
  
(*
(* with function extensionality, we would even have: *)
Lemma transIsoIso (A B C : Type) (isoBC : B ≅ C) : (A ≅ B) ≅ (A ≅ C).

  but not here... 
*)

(****************)
(* Finite Types *)
(****************)

(* property of a type to be finite *)
Record Finite (X : Type) : Type :=
  MkFinite {
      card : nat;
      isoFin : Iso X (Fin.t card)
  }.

(* the type of finite types *)
Definition FiniteType : Type := sigT Finite.

(* for any cardinality, we have the standard finite type
   of that cardinality *)
Definition FinFinite (card : nat) : FiniteType.
Proof.
  unfold FiniteType.
  exists (Fin.t card).
  apply (MkFinite (Fin.t card) card (idIso (Fin.t card))).
Defined.

(**************************************************)
(* operations on FiniteType:                      *)
(**************************************************)

(* Many constructions producing a type from 
   some parameter types yield finite types if 
   the parameter types are finite.

   Examples considered below are 
     option :    Type -> Type
     sum, prod:  Type -> Type -> Type
     Vect.t _ n: Type -> Type (for some n:nat)

   The function type A -> B of finite types
   A and B cannot be shown to be finite, although
   of course any function f : A -> B is extensionally
   determined by the list of values it takes on the
   elements of A. That's why we take Vector.t B (card A)
   as the type of functions between finite sets A and B,
   see below. 

   Remark: Only the finiteness of A is necessary for 
   this indentification to be reasonable, so we will also
   identify a type family on a finite type A - i.e. a 
   function A -> Type - with a Vector of types although 
   of course neither Type nor FiniteType are finite.

*)   

(* ---------------------------------------------*)
(* operations on FiniteType: Option             *)
(* ---------------------------------------------*)

(* option preserves finiteness *)

Definition optionFinTo {n : nat} (f : Fin.t (S n)) : option (Fin.t n) :=
  match f with
    | F1 => None
    | FS f' => Some f'
  end.

Definition optionFinFrom {n : nat} (of : option (Fin.t n)) : Fin.t (S n) :=
  match of with
    | None => F1
    | Some f' => FS f'
  end.

Definition optionFinIso {n : nat} : Iso (Fin.t (S n)) (option (Fin.t n)).
Proof.
  apply (MkIso _ _ (@optionFinTo n) (@optionFinFrom n)).
  - induction n; intro b; destruct b; simpl; reflexivity.
  - induction n; intro a; dependent destruction a; simpl; reflexivity.
Defined.

(* option is a functor: can define map *)
Definition mapOption {A B : Type} (f: A -> B) (oa : option A) : option B :=
  match oa with
    | None   => None
    | Some a => Some (f a)
  end.

(* option is a functor: map respects isomorphisms *)
Lemma optionIso {A B : Type} : A ≅ B -> (option A) ≅ (option B).
Proof.
  intro isoAB.
  destruct isoAB as [ab ba abba baab].
  apply (MkIso _ _ (mapOption ab) (mapOption ba)).
  - intro ob; destruct ob as [ b | ]; simpl.
    + rewrite (abba b); reflexivity.
    + reflexivity.
  - intro oa; destruct oa as [ a | ]; simpl.
    + rewrite (baab a); reflexivity.
    + reflexivity.
Defined.

(* option induces an endofunction on FiniteType *)
Definition optionFinite : FiniteType -> FiniteType.
Proof.
  intro X.
  destruct X as [X [cardX isoX]].
  exists (option X).
  exists (S cardX).
  apply (optionFinIso ⇚).
  exact (optionIso isoX).
Defined.

(* to be done: define Hom, id, comp,... to make FiniteType
   a category and prove that optionFinite canonically extends
   to a functor, i.e. define map, prove id-, comp- and iso-preservation!
*)

(* any finite type is either isomorphic to False or isomorphic to
   optionFinite of some (Fin.t ..) 
   need's a nicer formulation
   have to figure out how this can be used for 
   "induction" analoguous to nat induction
 *)
Lemma decideFin (X : Type) (Xfin : Finite X) : 
         (X ≅ (Fin.t 0)) + {n : nat & X ≅ (option (Fin.t n))}.
Proof.
  destruct Xfin as [cardX isoX].
  induction cardX.
  + left; exact isoX.
  + right.
    exists cardX.
    apply (optionFinIso ⇛).
    exact isoX.
Defined.

(* universal property of sum *)
Definition univSum {X Y Z : Type} (f : X -> Z) (g : Y -> Z) (xy: X + Y) : Z :=
  match xy with
      | inl x => f x
      | inr y => g y
  end.

(* \triangledown *)
Notation " f ▿ g " := (univSum f g) (at level 10). 

(* sum is a functor in both arguments *)
Definition sumMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : 
                  (X + Y) -> (Z + W) := (inl ∘ f) ▿ (inr ∘ g).

(* \boxplus *)
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

(* name cases where iso on one side is identity *)
Definition sumIsoLeft {X Y : Type} (Z : Type) (isoXY: X ≅ Y) :
    (X + Z) ≅ (Y + Z) := (sumIso isoXY (idIso Z)).

Definition sumIsoRight {X Y : Type} (Z : Type) (isoXY: X ≅ Y) :
    (Z + X) ≅ (Z + Y) := (sumIso (idIso Z) isoXY).

(* (Fin.t 0) is uninhabited, i.e. isomorphic to False *)
Lemma falseFromFin0 (x : Fin.t 0) : False.
Proof.
  dependent destruction x.
Defined.

Lemma isoFalseFin0 : False ≅ (Fin.t 0).
Proof.
  apply (MkIso _ _ (False_rect (Fin.t 0)) falseFromFin0).
  + intro x; dependent destruction x.
  + intro a; destruct a.
Defined.

(* in particular, False is Finite *)
Lemma falseIsFinite : Finite False.
Proof.
   exists 0.
   exact isoFalseFin0.
Defined.

(* (Fin.t 1) is isomorphic to True *)
Lemma isoTrueFin1 : True ≅ (Fin.t 1).
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
  + intro x; simpl; reflexivity.
  + intro fx; destruct fx as [f | x].
    - destruct f.  
    - simpl; reflexivity.
Defined.

(* (Fin.t 0) is also neutral for + *)
Lemma sumFin0Iso (X : Type) : ((Fin.t 0) + X) ≅ X.
Proof.
  apply (sumFalseIso _ ⇛).
  exact (sumIsoLeft _ (symIso isoFalseFin0)).
Defined.

(* adding (Fin.t 1) is option (up to iso) *)

Fixpoint sumFin1IsoTo (X : Type) (t1X : (Fin.t 1) + X) : (option X) := 
   match t1X with
   | inl _ => None
   | inr x => Some x
   end.

Fixpoint sumFin1IsoFrom (X : Type) (OX : option X) : (Fin.t 1) + X  :=
   match OX with
   | None   => inl F1
   | Some x => inr x
   end.

Lemma sumFin1Iso (X : Type) : ((Fin.t 1) + X) ≅ (option X).
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

Lemma sumFin1FinNIso (n : nat) : ((Fin.t 1) + (Fin.t n)) ≅ (Fin.t (S n)).
Proof.
  apply (optionFinIso ⇚).
  exact (sumFin1Iso _).
Defined.

(* the sum of two finite types is finite *)

Lemma sumIsFiniteLemma (n m : nat) : forall (X Y : Type),
                          (X ≅ (Fin.t n)) -> (Y ≅ (Fin.t m)) ->
                          ((X + Y) ≅ (Fin.t (n + m))).
Proof.
  induction n.
  + intros X Y isoXt0 isoYtm.
    simpl.
    apply ((sumFalseIso _) ⇛).
    apply ((sumIsoLeft _ isoFalseFin0) ⇚).
    exact (sumIso isoXt0 isoYtm).
  + intros X Y isoXtSn isoYtm.
    apply ((@optionFinIso (n + m)) ⇚).
    apply ((optionIso (IHn _ _ (idIso (Fin.t n)) (idIso (Fin.t m)))) ⇛).
    apply ((optionSumIso _ _) ⇛).
    apply ((sumIsoLeft _ optionFinIso) ⇛).
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

Definition univProd {X Y Z : Type} (f : X -> Y) (g : X -> Z) (x : X) : Y * Z := (f x , g x).

(* \triangle *)
Notation " f ▵ g " := (univProd f g) (at level 10). 

(* prod is a functor in both arguments *)

Definition prodMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : 
                              (X * Y) -> (Z * W) := (f ∘ fst) ▵ (g ∘ snd).

(* \boxtimes *)
Notation " f ⊠ g " := (prodMap f g) (at level 10). 

(* prod is commutative (up to iso) *)
Lemma prodCommutative (X Y : Type) : (X * Y) ≅ (Y * X).
Proof.
  apply (MkIso (X * Y) (Y * X) (snd ▵ fst) (snd ▵ fst));
  intro pair; destruct pair; simpl; reflexivity.
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

Definition prodIsoLeft {X Y : Type} (Z : Type) (isoXY : X ≅ Y) :
                  (X * Z) ≅ (Y * Z) := prodIso isoXY (idIso Z).

Definition prodIsoRight {X Y : Type} (Z : Type) (isoXY : X ≅ Y) :
                  (Z * X) ≅ (Z * Y) := prodIso (idIso Z) isoXY.

(* product with False is False *)
Lemma prodFalseIso (X : Type) : (False * X) ≅ False.  
Proof.
  apply (MkIso _ _ fst (id ▵ (False_rect X))).
  + intro f; destruct f.
  + intro fx; destruct fx as [f x]. destruct f.
Defined.

(* True is neutral for prod *)
Lemma prodTrueIso (X : Type) : (True * X) ≅ X.
Proof.
  apply (MkIso _ _ snd ((fun _ => I) ▵ id)).
  + intro x; simpl; reflexivity.
  + intro tx; destruct tx as [t x]; destruct t; simpl; reflexivity.
Defined.

(* product distributes over sum *)

Definition prodDistSumIsoTo (X Y Z : Type) (xyz : X * (Y + Z)) : (X * Y) + (X * Z) :=
  match xyz with
  | (x , inl y) => inl (x , y)
  | (x , inr z) => inr (x , z)
  end.

Lemma prodDistSumIsoLeft (X Y Z : Type) : (X * (Y + Z)) ≅ ((X * Y) + (X * Z)).
Proof.
  apply (MkIso _ _ (prodDistSumIsoTo X Y Z) ((id ⊠ inl) ▿ (id ⊠ inr))).
  + intro sumXYXZ; destruct sumXYXZ as [pair | pair];
    destruct pair; simpl; reflexivity.
  + intro pairXSumYZ. 
    destruct pairXSumYZ as [x [y | z]]; simpl; reflexivity.
Defined.

Lemma prodDistSumIsoRight (X Y Z : Type) : ((Y + Z) * X) ≅ ((Y * X) + (Z * X)). 
Proof.
  apply (⇚ (prodCommutative X (Y + Z))).
  apply ((sumIso (prodCommutative X Y) (prodCommutative X Z)) ⇛).
  exact (prodDistSumIsoLeft X Y Z).
Defined.

Lemma prodIsFiniteLemma (n m : nat) : forall (X Y : Type),
        (X ≅ (Fin.t n)) -> (Y ≅ (Fin.t m)) -> ((X * Y) ≅ (Fin.t (n * m))).
Proof.
  induction n.
  + intros X Y isoXt0 isoYtm.
    simpl.
    apply (isoFalseFin0 ⇛).
    apply ((prodFalseIso (Fin.t m)) ⇛).
    apply ((prodIsoLeft _ isoFalseFin0) ⇚).
    exact (prodIso isoXt0 isoYtm).
  + intros X Y isoXtSn isoYtm.
    apply ((sumIsFiniteLemma _ _ _ _ (idIso (Fin.t m)) 
                                     (idIso (Fin.t (n * m)))) ⇛).
    apply ((sumIsoRight _  (IHn (Fin.t n) (Fin.t m) (idIso _) (idIso _))) ⇛).
    apply ((sumIsoLeft _ (prodTrueIso (Fin.t m))) ⇛).
    apply ((sumIsoLeft _ (prodIsoLeft _ isoTrueFin1)) ⇚).
    apply ((prodDistSumIsoRight _ _ _) ⇛).
    apply ((prodIsoLeft _ (sumFin1FinNIso n)) ⇚).
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

(* now for the exponential:

   problem: we cannot show that for finite X and Y
   X -> Y is finite: 

   The cardinality should of course be cardY ^ cardX. But then already for
   X ≅ t 0 ≅ False, we would have to show that there is exactly one map 
   False -> Y for any type Y, so we'd have to show that any map 
   False -> Y is equal to False_rect Y, and since we don't have function 
   extensionality, there is no chance to do that.

   Instead, we define Hom for finite types X, Y to be
          Hom X Y  :=  Vect.t Y cardX

   That looks strange since the right hand side does not depend
   on X itself, but only on its cardinality.

   However, since the finite set X comes with an isomorphisms to (t cardX),
   we can define maps

       X -> Y   --- toHom --->   Hom X Y
                <-- fromHom --

   Without function extensionality, we cannot prove

            fromHom . toHom = id (X -> Y).

   But it should be possible to prove 

            toHom . fromHom = id (Hom X Y).

   And it shouldn't be hard to prove 

            (Vect Y cardX ) ≅ t (cardY ^ cardX)),

   i.e. Hom X Y finite for finite X and Y.
 *)

(* first, we define a type for Hom *)
Definition HomFinT (X Y : FiniteType) : Type.
Proof.
  destruct X as [X [cardX isoX]].
  destruct Y as [Y [cardY isoY]].
  exact (Vector.t Y cardX).
Defined.

SearchAbout "nth".
Print VectorDef.nth.
Print VectorDef.nil.
Print VectorDef.cons.

Print "::".
SearchPattern (nat -> nat -> nat).

(* towards vectProdIso *)

Fixpoint vectProdTo (X : Type) (n : nat) (v : Vector.t X (S n)) : X * (Vector.t X n) :=
  match v with
  | (VectorDef.cons _ x _ xs) => (x , xs)
  end.

Fixpoint vectProdFrom (X : Type) (n : nat) (p : X * (Vector.t X n)) : Vector.t X (S n) :=
  match p with
  | (x , xs) => VectorDef.cons X x n xs
  end.

Lemma vectProdIso (X : Type) (n : nat) : (Vector.t X (S n)) ≅ (X * (Vector.t X n)).
Proof.
  apply (MkIso _ _ (vectProdTo X n) (vectProdFrom X n)).
  + intro pair.
    destruct pair as [x v].
    dependent destruction v; simpl; reflexivity.  
  + intro v.
    dependent destruction v.
    dependent destruction v; simpl; reflexivity.  
Defined.    

Fixpoint lemma1To (X : Type) (v : Vector.t X 0) : Fin.t 1 :=
  match v with
  | nil _ => F1
  end.

Lemma lemma1From (X : Type) (i : Fin.t 1) : Vector.t X 0.
Proof.
  exact (nil X).
Defined.

Lemma lemma (n m : nat) : (Vector.t (Fin.t n) m) ≅ (Fin.t (n ^ m)).
Proof.
  induction m.
  + simpl.
    apply (MkIso _ _ (lemma1To (Fin.t n)) (lemma1From (Fin.t n))).
    - intro f; dependent destruction f.
      * simpl; reflexivity.
      * dependent destruction f; simpl.
    - intro v; simpl; dependent destruction v; reflexivity.
  + apply (transIso (prodIsFiniteLemma n (n ^ m)
                        (Fin.t n) (Fin.t (n ^ m)) (idIso _) (idIso _))).
    apply (transIso (prodIsoRight (Fin.t n) IHm)).
    exact (vectProdIso (Fin.t n) m).
Defined.

(* for any n, Vector.t _ n is a functor *)
(*
Definition mapVector ... tbc 
*)
