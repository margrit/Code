Load Repeats_vector.
(* Load Comparison. *)
Require Import Vector.
Require Import Arith.
Require Import Decidable.
Require Import Program.
Require Import Structures.Equalities.


(* Spielereien mit Gleichheit *)

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


Lemma eq_app_dep : forall {A : Type} {x y : A} {B : A -> Type} (f : forall (x : A ), (B x)) (p : x = y), 
    (subst B p (f x) = f y).
Proof.
intros.
destruct p.
simpl.
reflexivity.
Defined.


(* Entscheidbarkeit von Appears und Repeats fuer den Fall, 
   dass die Elemente des Vektors vom Typ Fin.t sind        *)

Theorem dec_Appears_fin : forall {n m : nat} (f : @Fin.t n) (v : Vector.t (@Fin.t n) m), 
     (Appears_in f v) + ((Appears_in f v) -> False).
Proof.
  intros.
  apply dec_Appears_in.
  apply fin_eq_dec.
Defined. 

Theorem dec_Repeats_fin : forall {n m : nat} (v : Vector.t (@Fin.t n) m), 
     (Repeats v) + ((Repeats v) -> False).
Proof.
  intros.
  apply dec_Repeats.
  apply fin_eq_dec.
Defined. 


(* "Funktorialitaets" Lemmata *)

Fixpoint funct_Appears_in {A B : Type} {n : nat} (f : A -> B)
                        (x : A) (v : Vector.t A n) :
                        Appears_in x v -> Appears_in (f x) (map f v).
intro.
induction n.
- inversion X.
- dependent destruction X; simpl.
  + apply ai_here.
  + apply ai_later.
    apply IHn.
    assumption.
Defined.

Fixpoint funct_Repeats {A B : Type} {n : nat} (f : A -> B) (v : Vector.t A n) :
                        Repeats v -> Repeats (map f v).
intro.
induction v.
- inversion X.
- dependent destruction X; simpl.
  + apply rp_ext.
    apply IHv.
    assumption.
  + apply rp_intr.
    apply funct_Appears_in.
    assumption.
Defined.



(* Lemmata zum Einfuegen von Elementen *)


(* Einfuegen von a in v an der Position p *)

Lemma insert_at {A : Type} {n : nat} (v : t A n) (p: @Fin.t (S n))
                                     (a : A) : t A (S n).
Proof.
dependent induction p.
- pose (cons A a n v).
  assumption.
- dependent destruction v.
  + inversion p.
  + pose (IHp  n v eq_refl a).
    pose (cons A h (S n) t).
    assumption.
Defined.


(* Eingefuegte Elemente erscheinen im Ergebnisvektor *)

Lemma insert_Appears {A : Type} {n : nat} : 
              forall (x : A) (v : Vector.t A n ) (f : @Fin.t (S n)),
                Appears_in x (insert_at v f x).
Proof.
  intros x v.
  dependent induction v; intro f.
  - dependent induction f.
    + compute.
      apply ai_here.
    + inversion f.
  - dependent induction f.
    + compute.
      apply ai_here.
    + pose (IHv f). 
      apply ai_later.
      assumption.
Defined.


(* Einfuegen in eine leere Liste *)

Lemma insert_nil {A : Type} : 
              forall (x : A) (v : Vector.t A 0) (f : @Fin.t 1),
                cons A x 0 (nil A) = insert_at v f x.
Proof.
intros x v f.
dependent destruction v.
dependent destruction f.
- compute.
  reflexivity.
- inversion f.
Defined. 

(* Anhaengen an eine leere Liste *)

Lemma append_nil {A : Type} {n : nat} : 
              forall (x : A) (v : Vector.t A n),
                append (nil A) v = v.
Proof.
intros x v.
dependent destruction v; simpl; reflexivity.
Defined.


(* Wenn ein Element, das schon in der Liste vorkommt, 
   eingefuegt wird, dann widerholt es sich             *)

Lemma ins_app_Repeats {A : Type} {n : nat}:
          forall (x : A) (v : Vector.t A n) (f : @Fin.t (S n)), 
                  Appears_in x v -> Repeats (insert_at v f x).
Proof.
  intros x v f.
  dependent induction f.
  - induction v; intro ap.
    + inversion ap.
    + simpl.
      apply rp_intr.
      assumption.
  - induction v; intro ap. 
    + inversion ap.
    + inversion ap; dependent destruction H2.
      * pose (insert_Appears h v f) as a.     
        apply rp_intr in a.
        compute.
        assumption.
      * apply rp_ext.
        compute. 
        apply IHf; [apply eq_refl | apply JMeq_refl | assumption].

     (* Alternative fuer den letzten Fall:
        pose (insert_at v f x) as t.
        pose (IHf n x v f eq_refl JMeq_refl X) as r.
        pose (rp_ext h t r) as r0.
        compute.
        assumption. *)
Defined.


(* Map von FS auf einen Vektor *)

Definition map_fs {n m : nat} (v : Vector.t (@Fin.t n) m) := map FS v.

(* Das Einfuegen eines Elements erhaelt im Vektor vorhandene Elemente *)

Lemma ins_pres_app {A : Type} {n : nat} (x y : A):
 forall (v : Vector.t A n) (f: @Fin.t (S n)),
               Appears_in x v -> Appears_in x (insert_at v f y).
Proof.
induction n; intros v f ap.
dependent induction v.
-inversion ap.
- dependent destruction v.
  dependent destruction f.
  + apply ai_later.
    assumption.
  + dependent destruction ap.
    * apply ai_here.
    * apply ai_later.
      apply IHn.
      assumption.
Defined.

(* Das Einfuegen eines Elements erhaelt vorhandene Wiederholungen *)

Lemma ins_pres_rep {A : Type} {n : nat} (x : A) : forall (v : Vector.t A n) (f: @Fin.t (S n)), 
                    Repeats v -> Repeats (insert_at v f x).
Proof.
intros v f r.
dependent induction v.
- inversion r.
- dependent destruction f.
  + compute.
    apply rp_ext.
    assumption.
  + dependent induction r.
    * compute.
      apply rp_ext.
      apply IHv.
      assumption.
    * compute.
      apply rp_intr.
      pose (ins_pres_app h x v f a).
      assumption.
Defined.


(* Entfernen eines im Vektor enthaltenen Elements ergibt einen neuen Vektor 
   und die Information, um den urspruenglichen Vektor wiederherstellen zu koennen *)

Lemma remove_app {A : Type} {n : nat} (x : A) (v : Vector.t A (S n)) :
             Appears_in x v -> { v' : Vector.t A n & { f : @Fin.t (S n) &
             ((insert_at v' f x) = v) }}.
Proof.
  intro ap.
  dependent induction v.
  dependent destruction ap.
  - exists v.
    exists F1.
    cbn.  (*alternativ simpl?*)
    reflexivity.
  - dependent destruction n.
    + inversion ap.
    + pose (IHv n x v eq_refl JMeq_refl ap).
      destruct s as [v' rest].
      destruct rest as [f ins].
      exists (cons A h n v'). 
      exists (FS f).
      rewrite <- ins. 
      compute.
      apply eq_refl.
Defined.


(* Entfernen des Kopfelements erhaelt Nicht-Enthaltensein *)

Lemma not_Appears_in_tl {A : Type} {n : nat} (x y : A) (v : Vector.t A n) : 
                                (Appears_in x (cons A y n v) -> False) ->
                                (Appears_in x v) -> False.
Proof.
intros.
pose (ai_later x y v X).
apply H. 
assumption.
Defined.


(* Wenn F1 nicht in einem Fin (n+1)-Vektor vorkommt, 
   dann entsteht er als Mapping aus einem Fin n-Vektor *)

Lemma fin_vec_from_below {n m : nat} (v : Vector.t (@Fin.t (S n)) m) : 
            (Appears_in F1 v -> False) -> {v' | map FS v' = v}.
Proof.
intro not_ap.
dependent induction v.
- exists (nil (@Fin.t n)).
  simpl.
  reflexivity.
- dependent destruction h. 
  + contradict not_ap.
    apply ai_here.
  + pose (not_Appears_in_tl F1 (FS h) v not_ap) as not_ap_F1.
    pose (IHv not_ap_F1) as ex_v'.
    destruct ex_v' as [v' eq_map].
    exists (cons (Fin.t n) h n0 v').
    simpl.
    rewrite eq_map.
    reflexivity.  
Defined.


(*-------------------------------------------------------------------------------------------*)

(** Das Taubenschlag-Prinzip *)

(*-------------------------------------------------------------------------------------------*)


Theorem pigeon_hole_Repeats: forall (n m : nat) (n_lt_m: n < m) (v : Vector.t (@Fin.t n) m), 
                   Repeats v.
Proof.
dependent induction n; intros m n_lt_m v.
- inversion v. 
  contradict n_lt_m.
  intro ff.
  rewrite <- H in ff.
  inversion ff.
  inversion h.
- dependent induction m.
  + contradict n_lt_m.
    intro ff.
    inversion ff.
  + pose (dec_Repeats_fin v) as dec_rp_tl.
    destruct dec_rp_tl.
    (* Die Liste enthaelt eine Wiederholung *)
    * assumption.

    (* Die Liste enthaelt keine Wiederholung *)
    * pose (dec_Appears_fin F1 v) as dec_ap_tl.
      destruct dec_ap_tl as [ap_f1 | not_ap_f1].

      (* F1 kommt in der Liste vor *)
      pose (remove_app F1 v ap_f1).
      dependent destruction s.
      dependent destruction s.
      pose (dec_Appears_fin F1 x0) as dec_ap_tl'.
      destruct dec_ap_tl' as [ap_f1_x0 | not_ap_f1_x0].

      (* F1 kommt noch einmal in der Liste vor *)
      { pose (ins_app_Repeats F1 x0 x ap_f1_x0).
        rewrite e in r.
        assumption. } 

      (* F1 kommt nicht noch einmal in der Liste vor *)
      { pose (fin_vec_from_below x0 not_ap_f1_x0) as x'_ex.
        dependent destruction x'_ex.
        pose (lt_S_n n m n_lt_m).
        pose (IHn m l x1).
        pose (funct_Repeats FS x1 r).
        rewrite e0 in r0.
        pose (ins_pres_rep F1 x0 x r0).
        rewrite e in r1.
        assumption.
      } 

      (* F1 kommt nicht in der Liste vor *)
      { pose (fin_vec_from_below v not_ap_f1) as v'_ex.
        dependent destruction v'_ex.
        dependent destruction x.
        pose (lt_S_n n m n_lt_m).
        pose (IHn m l x). 
        pose (funct_Repeats FS x r).
        simpl.
        apply rp_ext.
        assumption.
       }
Defined.


(*-------------------------------------------------------------------------------------------*)

(* Anschliessend lassen sich noch die Positionen berechnen, 
   an denen die Wiederholungen vorkommen:                    *)


Lemma pos_Appears {A : Type} {n : nat} : forall (a : A) (v : Vector.t A n), 
    Appears_in a v -> {i : @Fin.t n & nth v i = a }.
Proof.
intros a v ap.
dependent induction ap.
- exists F1.
  simpl.
  reflexivity.
- destruct IHap.
  exists (FS x).
  simpl.
  assumption.
Defined.


Lemma pos_Repeats {A : Type} {n : nat} : forall (v : Vector.t A n), 
    Repeats v -> {i : @Fin.t n & { j : @Fin.t n & nth v i = nth v j } }.
Proof.
intros v rp.
dependent induction rp.
- destruct IHrp.
  destruct s.
  exists (FS x0).
  exists (FS x1).
  simpl.
  assumption.
- exists F1.
  pose (pos_Appears x v a).
  destruct s.
  exists (FS x0).
  simpl.
  rewrite e.
  reflexivity.
Defined.

