(* 
   Ich habe dort, wo dependent induction oder destruction vorhommt/kam, Alternativen hingeschrieben, 
   die Schemata aus der Fin-Bibliothek benutzen; so koennten wir auf "Program" verzichten.
*)


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

Print idIso.

(* inversion of isomorphisms *)
Lemma symIso (A B : Type) : Iso A B -> Iso B A.
Proof.
  intro isoAB.
  destruct isoAB as [to from toFrom fromTo].
  exact (MkIso _ _ from to fromTo toFrom).
Defined.

(* we even have (but never use..) *)
Lemma symIsoIso (A B : Type) : Iso (Iso A B) (Iso B A).
Proof.
  apply (MkIso _ _ (symIso A B) (symIso B A));
  intro isoab; destruct isoab; compute; reflexivity.
Defined.
  
(* composition of isomorphisms *)
Lemma transIso (A B C : Type) : Iso B C -> Iso A B -> Iso A C.
Proof.
  intros isoBC isoAB.  
  destruct isoBC as [bc cb bccb cbbc].
  destruct isoAB as [ab ba abba baab].
  apply (MkIso _ _ (compose bc ab) (compose ba cb)).
  + intro c; compute; rewrite (abba (cb c)); rewrite (bccb c); reflexivity.
  + intro a; compute; rewrite (cbbc (ab a)); rewrite (baab a); reflexivity.
Defined.      

(* "flipped" version just for convenience *)
Lemma transIso' (A B C : Type) : Iso A B -> Iso B C -> Iso A C.
Proof.
  intros isoab isobc.
  exact (transIso _ _ _ isobc isoab).
Defined.
  
(*
(* with function extensionality, we would even have:
 *)
Lemma transIsoIso (A B C : Type) (isoBC : Iso B C) : Iso (Iso A B) (Iso A C).
Proof.
  apply (MkIso _ _ (transIso A _ _ isoBC) (transIso A _ _ (symIso _ _ isoBC))).
  + intro isoAB.
    destruct isoAB as [ab ba abba baab].
    destruct isoBC as [bc cb bccb cbbc].

  but not here... 
*)

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

 (* alternativ:

  exists (@Fin.t card).
  apply (MkFinite (@Fin.t card) card (idIso (@Fin.t card))).

*)
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

(* towards optionFinite *)

Fixpoint optionFinTo {n : nat} (f : @Fin.t (S n)) : option (Fin.t n) :=
match f with
| F1 => None
| FS f' => Some f'
end.

Inductive Auto (A : Type) : Type := MkAuto : (A -> A) -> Auto A. 
 
Fixpoint optionFinFrom {n : nat} (of : option (Fin.t n)) : @Fin.t (S n) :=
match of with
| None => F1
| Some f' => FS f'
end.

Fixpoint optionFinIso {n : nat} : Iso (@Fin.t (S n)) (option (Fin.t n)).
Proof.
 apply (MkIso (t (S n)) (option (t n)) (@optionFinTo n) (@optionFinFrom n)); 
 induction n; intro a; dependent destruction a; simpl; reflexivity.

(* Variante, die zwar nicht so kurz ist, aber "dependent destruction" vermeidet:

  apply (MkIso (t (S n)) (option (t n)) (@optionFinTo n) (@optionFinFrom n)).
  - induction n; intro b; destruct b; simpl;reflexivity.
  - induction n; intro a; apply (caseS' a); simpl; reflexivity.

*)
Defined.

Fixpoint mapOption {A B : Type} (f: A -> B) (oa : option A) : option B :=
match oa with
| None   => None
| Some a => Some (f a)
end.
 
Fixpoint optionIso {A B : Type} (AIsoB : Iso A B) : Iso (option A) (option B).
Proof.
  destruct AIsoB as [ab ba abba baab].
  apply (MkIso (option A) (option B) (mapOption ab) (mapOption ba)).
  - intro ob; induction ob as [ b | ]; simpl.
    + rewrite (abba b); reflexivity.
    + reflexivity.
  - intro oa; induction oa as [ a | ]; simpl.
    + rewrite (baab a); reflexivity.
    + reflexivity.
Defined.

Fixpoint optionFinite (X : FiniteType) : FiniteType.
Proof.
  destruct X as [X [card iso]].
  pose (optionIso iso) as oIso.
  pose (transIso _ _ _ 
          (symIso _ _ (@optionFinIso card))
          oIso
          ) as oIso2.
  assert (Finite (option X)) as optionIsFinite.
  apply (MkFinite (option X) (S card) oIso2).
  exact (existT Finite (option X) optionIsFinite).

(* Variante:

  destruct X as [X [card iso]].
  apply optionIso in iso as oIso.
  apply (transIso _ _ _ 
          (symIso _ _ (@optionFinIso card))) in oIso as oIso2.
  exists (option X).
  apply (MkFinite (option X) (S card) oIso2).
*)

Defined.

Print sigT.


Fixpoint decideFin (X : Type) (Xfin : Finite X) : (Iso X (Fin.t 0)) + {n : nat & Iso X (option (Fin.t n))}.
Proof.
  destruct Xfin as [card iso].
  induction card.
  + exact (inl iso). (* Alternativ: "left. exact iso." *)
  + apply inr. (* Die "normale" zugehoerige Taktik waere "right" *)  
    pose (@optionFinIso card0) as iso2.
    pose (transIso _ _ _ iso2 iso) as iso3.
    apply (existT _ card0 iso3). (* oder: "exists card0. exact iso3." *)

(* Alternative:

  + left. exact iso.
  + right.
    exists card0.
    apply (transIso X (t (S card0)) (option (t card0))).
    - apply optionFinIso.
    - exact iso.
*)

Defined.

Fixpoint optionSumTo (X Y : Type) ( oxY : (option X) + Y) : option (X + Y) :=
  match oxY with
      | (inl None)      => None
      | (inl (Some x))  => Some (inl x)
      | (inr y)         => Some (inr y)
  end.

Fixpoint optionSumFrom (X Y : Type) (oXy : option (X + Y)) : (option X) + Y :=
  match oXy with
      | None            => inl None
      | Some (inl x)    => inl (Some x)
      | Some (inr y)    => inr y
  end.
                               

Lemma optionSumIso (X Y : Type) : Iso ((option X) + Y) (option (X + Y)).
Proof.
  apply (MkIso _ _ (optionSumTo X Y) (optionSumFrom X Y)).  
  + intro oxy; induction oxy as [xy | ].    
    - induction xy; simpl; reflexivity. (* oder mit "destruct xy;..." *)
    - simpl; reflexivity.
  + intro oxy; induction oxy as [ox | y].
    - induction ox as [x | ]; simpl; reflexivity.
    - simpl; reflexivity.
Defined.

Fixpoint sumFlip (X Y : Type) (xy : X + Y) : (Y + X) :=
  match xy with
      | inl x => inr x
      | inr y => inl y
  end.

Lemma sumCommutative (X Y : Type) : Iso (X + Y) (Y + X).
Proof.
  apply (MkIso _ _ (sumFlip X Y) (sumFlip Y X)).
  intro yx; induction yx; simpl; reflexivity.
  intro xy; induction xy; simpl; reflexivity.
Defined.

Definition univSum {X Y Z : Type} (f : X -> Z) (g : Y -> Z) (xy: X + Y) : Z :=
  match xy with
      | inl x => f x
      | inr y => g y
  end.

Definition sumMap {X Y Z W : Type} (f : X -> Z) (g : Y -> W) : (X + Y) -> (Z + W) :=
  univSum (compose inl f) (compose inr g).

Lemma sumIsoLeft (X Y Z : Type) (isoXY: Iso X Y) : Iso (X + Z) (Y + Z).
Proof.  
  destruct isoXY as [xy yx xyyx yxxy].
  apply (MkIso _ _ (sumMap xy id) (sumMap yx id)).
  + intro oyz; induction oyz as [y | z].
    - compute; rewrite (xyyx y); reflexivity.
    - trivial.
  + intro oxz; induction oxz as [x | z].
    - compute; rewrite (yxxy x); reflexivity.
    - trivial. 
Defined.

Lemma sumIsoRight (X Y Z : Type) (isoXY: Iso X Y) : Iso (Z + X) (Z + Y).
Proof. (* couldn't we deduce this from sumIsoLeft and symmetry properties ?*)     
  destruct isoXY as [xy yx xyyx yxxy].
  apply (MkIso _ _ (sumMap id xy) (sumMap id yx)).
  + intro ozy; induction ozy as [z | y].
    - trivial.
    - compute. rewrite (xyyx y); reflexivity.
  + intro ozx; induction ozx as [z | x].
    - trivial.
    - compute; rewrite (yxxy x); reflexivity.
Defined.

Lemma falseFromFin0 (x : Fin.t 0) : False.
Proof.
  apply case0; exact x.
Defined.

Lemma finZeroIsoFalse : Iso False (Fin.t 0).
Proof.
  apply (MkIso _ _ (False_rect (t 0)) falseFromFin0).
  + intro x; dependent induction x. (* "case0." wuerde reichen; sonst ginge auch "dependent destruction x" *)
  + intro a; apply False_rect; exact a. (* "intro a; destruct a." reicht *)
Defined.

Lemma sumFalseIso (X : Type) : Iso (False + X) X.
Proof.
  apply (MkIso _ _ (univSum (False_rect X) id) inr).
  + intro x; compute; reflexivity.
  + intro fx; induction fx as [f | x].
    - destruct f.  
    - compute; reflexivity.
Defined.

(* Definition OfCard (n : nat) (X : Type) : Type := Iso X (Fin.t n). *)

Lemma sumFiniteLemma (n m : nat) : forall (X Y : Type),
                                   (Iso X (Fin.t n)) -> (Iso Y (Fin.t m)) ->
                                   (Iso (X + Y) (Fin.t (n + m))).
Proof.
  induction n.
  + intros X Y isoXt0 isoYtm.
    compute.
    pose (transIso _ _ _ (symIso _ _ finZeroIsoFalse) isoXt0) as isoXF.
    pose (sumIsoLeft _ _ Y isoXF) as isoSumXYSumFY.   
    apply (transIso' _ _ (t m) isoSumXYSumFY).
    apply (transIso' _ _ (t m) (sumFalseIso Y)).
    exact isoYtm.
  + intros X Y isoXtSn isoYtm.
    pose (sumIsoLeft _ _ Y isoXtSn) as isoSumXYSumtSnY.
    apply (transIso' _ _ (t (S n + m)) isoSumXYSumtSnY).
    clear isoXtSn isoSumXYSumtSnY X.
    pose (sumIsoLeft _ _ Y (@optionFinIso n)) as isoSumtSnYSumOtn.
    apply (transIso' _ _ (t (S n + m)) isoSumtSnYSumOtn).
    clear isoSumtSnYSumOtn.
    apply (transIso' _ _ (t (S n + m)) (optionSumIso (t n) Y)).
    pose (IHn (t n) Y (idIso (t n)) isoYtm) as isoSumtnYtnm.
    apply (transIso' _ _ (t (S n + m)) (optionIso isoSumtnYtnm)).
    clear isoYtm isoSumtnYtnm Y.
    apply (transIso' _ _ (t (S n + m)) (symIso _ _ (@optionFinIso (n + m)))).
    exact (idIso (t (S n + m))).    
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
   exact (existT Finite (sum X Y) (sumFinite X Y Xfin Yfin)).
Defined.
   