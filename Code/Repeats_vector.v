(* Grundsaetzliche Anpassungen: 

   - Benutzung des Fin.t aus der Standard Library 
   - Nicht mit Prop arbeiten sondern mit Type
   - Vector.t aus der Standard Library statt list

*)

(* Urspgl. Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Repeats.v*)

Require Import Vector.
Require Import Program.
Require Import Arith.
Load Fin_ext.

Local Open Scope vector_scope.

(* Vorkommen von x in einer Liste. *)

Inductive appears_in {X : Type} (a : X): forall {n : nat}, (Vector.t X n) -> Type :=
  | ai_here  {m} : forall (v : Vector.t X m), appears_in a (cons X a m v)
  | ai_later {m} : forall b (v : Vector.t X m), appears_in a v -> appears_in a (cons X b m v).

(* Vorkommen von Wiederholungen in einer Liste *)

Inductive repeats {X : Type} : forall {n : nat}, Vector.t X n -> Type :=
 | rp_ext  {m} : forall x : X, forall v : Vector.t X m, repeats v -> repeats (cons X x m v)
 | rp_intr {m} : forall x : X, forall v : Vector.t X m, appears_in x v -> repeats (cons X x m v).


(* Entscheidbarkeit von appears und repeats *)

Theorem dec_appears_in : forall {A : Type}
            (d : forall a a': A, (a = a') + ((a = a') -> False))
            {n : nat} (a : A),
            forall v : (Vector.t A n) , (appears_in a v) + ((appears_in a v) -> False).
Proof.
intros A d n a v.
induction v.
- right.
  intro X.
  inversion X.
- destruct IHv.
  + left.
    apply ai_later.
    assumption.
  + pose (d a h).
    destruct s.
    * left.
      rewrite e.
      apply ai_here.
    * right.
      intro.
      inversion X.
      { contradict H.
        assumption. }
      { dependent destruction H2. 
        contradict f.
        assumption. }
Defined.



Theorem dec_repeats : forall {A : Type} (d : forall a a': A, (a = a') + ((a = a') -> False))
                             {n : nat} (v : Vector.t A n), 
                            (repeats v) + ((repeats v) -> False).
Proof.
intro A.
induction n; intro.
- dependent destruction v.
  right.
  intro. 
  inversion X.
- dependent destruction v.
  + pose (IHn v).
    destruct s. 
    * left.
      apply rp_ext.
      assumption.
    * assert (sum (appears_in h v) ((appears_in h v) -> False)).
      { apply (dec_appears_in d h v). }
      { destruct X.
        - left. 
          apply rp_intr.
          assumption.
        - right.
          intro.
          inversion X.
          + apply f.
            dependent destruction H2.
            assumption.
          + apply f0.
            dependent destruction H2.
            assumption.
       }
Defined. 



(* Wenn x in der Konkatenation von zwei Listen vorkommt, 
   dann kommt x auch entweder in Liste 1 oder Liste 2 vor. *)

Lemma appears_in_app : forall {X : Type} {n m : nat} (xs : Vector.t X n) (ys : Vector.t X m) (x : X),
     appears_in x (append xs ys) -> appears_in x xs + appears_in x ys.
Proof.
  intros X n m xs ys x.
  induction xs.
  - simpl.
    intros.
    right.
    assumption.
  - intros H.
    simpl in H.
    dependent destruction H.
    + left.
      apply ai_here.
    + apply IHxs in H.
      destruct H.
      * { left.
           apply ai_later.
           assumption.
        }
      * { right.
          assumption.
        }
Qed.


(* Wenn x in Liste 1 oder Liste 2 vorkommt, 
   dann kommt x auch in der Konkatenation der Listen vor. *)

Lemma app_appears_in : forall {X : Type} {n m : nat} 
                          (xs : Vector.t X n) (ys : Vector.t X m) (x : X),
               appears_in x xs + appears_in x ys -> appears_in x (append xs ys).
Proof.
  intros X n m xs ys x dec_ap.
  destruct dec_ap.
  - dependent induction xs.
    + inversion a.
    + dependent destruction a.
      * simpl. 
        apply ai_here. 
      * simpl.
          apply ai_later.
          apply IHxs.
          assumption.
  - induction xs.
    + simpl.
      assumption.
    + simpl.
      apply ai_later.
      assumption.
Qed.


(*(* Axiom eq_rect_eq :
  forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.*)

Check (eq_rect_eq nat 0 (Vector.t nat) (nil nat) ......*)

Print eq_rect.
Check (eq_rect 1 (Vector.t nat) (cons nat 2 0 (nil nat)) 1 eq_refl). 


(* Liste verknüpft mit der leeren Liste ergibt die ursprüngliche Liste *)

Lemma app_v_nil {X : Type} {n : nat} : forall (v : @Vector.t X n),
                     {v' : Vector.t X (n+0) & (append v (nil X)) = v'}.
Proof.
   induction n.
   - simpl.
     intro v.
     exists v.
     dependent induction v.
     simpl.
     reflexivity.
   - intro v. 
     dependent induction v. 
     pose (IHn v).
     destruct s.
     exists (cons X h (n + 0) x).
     simpl.
     rewrite e.
     reflexivity.
Defined.


Lemma vec_pl0 {A : Type} {n : nat} (v : @Vector.t A (n + 0)) : @Vector.t A n.
Proof.
  pose (n_plus_0 n).
  rewrite <- e.  
  assumption.
Defined.

Lemma eq_Sn_Sm (n m : nat) (eq : n = m) : S n = S m.
Proof.
rewrite eq.
reflexivity.
Defined.

(*
Lemma permute_cons : forall {X : Type} {n m : nat} (eq : n = m) (x : X) (v : Vector.t X n), 
                 eq_rect (S n) (Vector.t X) (cons X x n v) (S m) (eq_Sn_Sm n m eq) 
                 = cons X x m (eq_rect n (Vector.t X) v m eq).
Proof.
induction n.
- induction m.
  intros eq x v.
  dependent destruction v.
  simpl.
  dependent destruction eq.
  simpl.
  
*)

(*Vorkommen von x in einer Teilliste. *)

Lemma appears_in_app_split : forall {X : Type} {n : nat} (x : X) (v : Vector.t X n),  
                   appears_in x v -> 
                     { n1 : nat &  { v1 : Vector.t X n1 & 
                     { n2 : nat &  { v2 : Vector.t X n2 & 
                     { eq : n1 + S n2 = n &
                       (v = eq_rect (n1 + S n2)(Vector.t X)(append v1 (cons X x n2 v2)) n eq) } }} }}.
Proof.
intros X n x v ap.
dependent induction ap.
- exists 0. exists (nil X).
  exists m. exists v.
  simpl.
  exists eq_refl.
  compute.
  reflexivity.
- destruct IHap  as [n1' IHap'].
  destruct IHap' as [v1' IHap''].
  destruct IHap'' as [n2' IHap'''].
  destruct IHap''' as [v2' IHap''''].
  destruct IHap'''' as [eq_n eq_v].
  exists (S n1'). exists (cons X b n1' v1').
  exists n2'. exists v2'.
  assert (S n1' + S n2' = S m).
  + rewrite <- eq_n.
    simpl.
    reflexivity.
  + exists H.
    simpl in *.
    dependent destruction H.
    simpl.
    reflexivity.
Defined.


(* Wenn eine von zwei Teillisten (mind.) eine Wiederholung besitzt, 
   so enthaelt auch ihre Verkettung eine Wiederholung               *)

Lemma repeats_in_app : forall {X: Type} {n1 n2 : nat} 
                              (v1 : Vector.t X n1) (v2 : Vector.t X n2), 
   repeats v1 + repeats v2 -> repeats (append v1 v2).  
Proof.
intros X n1 n2 v1.
dependent induction v1; intros v2 rp.
- destruct rp.
  + inversion r.
  + simpl.
    assumption.
- destruct rp.
  + dependent destruction r.
    * simpl.
      apply rp_ext.
      apply IHv1.
      left.
      assumption.
    * simpl.
      apply rp_intr.
      apply app_appears_in.
      left.
      assumption.
  + simpl.
    apply rp_ext.
    apply IHv1.
    right.
    assumption.
Defined. 


(* Zerlegung einer Liste mit Wiederholungen *)

Lemma repeats_decomp : forall {X : Type} {n : nat}, forall v : Vector.t X n,
  repeats v ->
    { x  : X   &
    { n1 : nat & { xs : Vector.t X n1  &
    { n2 : nat & { ys : Vector.t X n2  & 
    { n3 : nat & { zs : Vector.t X n3  &
    { eq : n1 + (S n2 + S n3) = n      &
      v = eq_rect (n1 + (S n2 + S n3)) (Vector.t X) 
         (append xs (append (cons X x n2 ys) (cons X x n3 zs))) n eq } }} }} }} }.
Proof.
  intros X n v rp.
  dependent induction rp.

  - destruct IHrp as [x' IHrp1]. 
    destruct IHrp1 as [n1 IHrp2].
    destruct IHrp2 as [v1 IHrp3].
    destruct IHrp3 as [n2 IHrp4].
    destruct IHrp4 as [v2 IHrp5].
    destruct IHrp5 as [n3 IHrp6].
    destruct IHrp6 as [v3 IHrp7].
    destruct IHrp7 as [eq_n eq_v].

    exists x'.
    exists (S n1). exists (cons X x n1 v1).
    exists n2. exists v2.
    exists n3. exists v3.

    simpl in *.
    assert (S (n1 + S (n2 + S n3)) = S m) as eq_Sm.

    + rewrite eq_n.
      reflexivity.

    + exists eq_Sm.
      dependent destruction eq_Sm.
      simpl in *.
      reflexivity.  

  - apply appears_in_app_split in a.

    destruct a as [n1' a1].
    destruct a1 as [v1' a2].
    destruct a2 as [n2' a3].
    destruct a3 as [v2' a4].
    destruct a4 as [eq_m eq_v].

    simpl in *.

    exists x.
    exists 0. exists (nil X).
    exists n1'. exists v1'.
    exists n2'. exists v2'.

    simpl in *.
    assert (S (n1' + S n2') = S m) as eq_Sm.

    + rewrite eq_m.
      reflexivity.

    + exists eq_Sm.
      dependent destruction eq_Sm.
      simpl in *.
      reflexivity. 
Defined.

Lemma repeats_comp : forall {X : Type} {n : nat}, forall v : Vector.t X n,
      { x  : X   &
      { n1 : nat & { v1 : Vector.t X n1  &
      { n2 : nat & { v2 : Vector.t X n2  & 
      { n3 : nat & { v3 : Vector.t X n3  &
      { eq : n1 + (S n2 + S n3) = n      &
        v = eq_rect (n1 + (S n2 + S n3)) (Vector.t X) 
         (append v1 (append (cons X x n2 v2) (cons X x n3 v3))) n eq } }} }} }} }
   -> repeats v.
Proof.
  intros X n v ex.

  destruct ex  as [x  ex1].
  destruct ex1 as [n1 ex2].
  destruct ex2 as [v1 ex3].
  destruct ex3 as [n2 ex4].
  destruct ex4 as [v2 ex5].
  destruct ex5 as [n3 ex6].
  destruct ex6 as [v3 ex7].
  destruct ex7 as [eq_n eq_v].

  pose (ai_here x v3) as x_in_v3. 
  assert (appears_in x (append v2 (cons X x n3 v3))) as x_in_v2xv3.
  
  - apply app_appears_in.
    right.
    assumption.
  
  - pose (rp_intr x (append v2 (cons X x n3 v3)) x_in_v2xv3) as rp_xv2xv3.

    rewrite eq_v.
    dependent destruction eq_n.
    simpl in *.
    apply repeats_in_app.
    right.
    assumption.
Defined.


(*Länge von konkatenierten Listen und einem Element ist gleich. 

Lemma length_app_2 : forall X:Type, forall x:X, forall xs ys: list X,
  length (xs ++ x :: ys) = length (x :: xs ++ ys).
Proof.
  induction xs.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

*)

Lemma sum_0 (n1 n2 : nat) : n1 + n2 = 0 -> ((n1 = 0) * (n2 = 0))%type.
Proof.
intro eq_0.
induction n1.
- split.
  + reflexivity.
  + rewrite <- eq_0.
    simpl. reflexivity.
- inversion eq_0.
Defined.

Lemma sum_1 (n1 n2 : nat) : n1 + n2 = 1 -> ((n1 = 0) + (n2 = 0))%type.
Proof.
intro eq_1.
destruct n1.
- left.
  reflexivity.
- dependent destruction eq_1.
  apply sum_0 in x.
  destruct x.
  right. 
  assumption. 
Defined.

Definition adapt_vec {X : Type} (n1 n2 : nat) (v : Vector.t X n1) (eq : n1 = n2) := 
             eq_rect n1 (Vector.t X) v n2 eq.

Lemma map_dec_2 {X Y :Type} {n n1 n2 : nat} : forall (f : X -> Y) 
                         (v : Vector.t X n) (eq : n1 + n2 = n)
                         (v1 : Vector.t Y n1) (v2 : Vector.t Y n2),
                 (map f v = adapt_vec (n1 + n2) n (append v1 v2) eq) 
              -> { v1' : Vector.t X n1 & { v2' : Vector.t X n2 &
                   ( (v = adapt_vec (n1 + n2) n (append v1' v2') eq)  
                   * (map f v1' = v1) * (map f v2' = v2) )%type }}.
Proof.
intros f v. generalize n1 n2.
dependent induction v; intros n1' n2' eq_n v1 v2 map_f_v.
- pose (sum_0 n1' n2' eq_n) as n1_n2_0.
  destruct n1_n2_0 as [n1_0 n2_0].
  + dependent destruction n1_0.
    dependent destruction n2_0.
    exists (nil X).
    exists (nil X).
    dependent destruction eq_n.
    simpl in *.
    dependent destruction v1.
    dependent destruction v2.
    split.
    * split; reflexivity.
    * reflexivity.
- simpl in *.
  dependent destruction v1.
  + dependent destruction v2.
    * inversion eq_n.
    * exists (nil X).
      simpl in *.
      pose (adapt_vec (S n) (S n0) (cons X h n v) (eq_sym eq_n)) as v2'.
      exists v2'.
      dependent destruction eq_n.
      simpl in *.
      split.
      { split. 
        - unfold v2'. 
          reflexivity.
        - reflexivity. 
      }
      { assumption. }
   + assert (n0 + n2' = n) as eq_n0_n2'.
     * dependent destruction eq_n.
       reflexivity.
     * pose (IHv n0 n2' eq_n0_n2' v1 v2).
       assert (map f v = adapt_vec (n0 + n2') n (append v1 v2) eq_n0_n2') as m_f_v'.
       { dependent destruction eq_n.
         dependent destruction eq_n0_n2'.
         dependent destruction map_f_v. 
         simpl in *.
         assumption. }
       { pose (s m_f_v') as IHv1.
         destruct IHv1 as [v1' IHv2].
         destruct IHv2 as [v2' eq_prod].
         destruct eq_prod as [eq_prod1 eq_v2].
         destruct eq_prod1 as [eq_v eq_v1].
         exists (cons X h n0 v1').
         exists v2'.
         split.
         - split.
           + dependent destruction eq_n.
             dependent destruction eq_n0_n2'.
             simpl in *.
             rewrite eq_v.
             reflexivity.
           + dependent destruction eq_n.
             simpl in *.
             rewrite eq_v1.
             dependent destruction map_f_v. 
             reflexivity.
          - assumption.
        }
Defined.


Lemma map_dec_3 {X Y :Type} {n n1 n2 n3 : nat} : forall (f : X -> Y) 
                (v : Vector.t X n) (eq : n1 + (n2 + n3) = n)
                (v1 : Vector.t Y n1) (v2 : Vector.t Y n2) (v3 : Vector.t Y n3),
     (map f v = adapt_vec (n1 + (n2 + n3)) n (append v1 (append v2 v3)) eq) 
  -> { v1' : Vector.t X n1 & { v2' : Vector.t X n2 & { v3' : Vector.t X n3 &
                   ( (v = adapt_vec (n1 + (n2 + n3)) n (append v1' (append v2' v3')) eq)  
                   * (map f v1' = v1) * (map f v2' = v2) * (map f v3' = v3) )%type }}}.
Proof.
intros f v eq v1 v2 v3 eq_map_f_v.
remember eq_map_f_v as eq_map_f_v'.
clear Heqeq_map_f_v'.
apply map_dec_2 in eq_map_f_v'.

destruct eq_map_f_v' as [v1' ex_v2].
destruct ex_v2 as [v2' eq_prod].
destruct eq_prod as [eq_prod1 eq_v2].
destruct eq_prod1 as [eq_v eq_v1].

exists v1'.
assert (append v2 v3 = adapt_vec (n2 + n3) (n2 + n3) (append v2 v3) eq_refl) as eq_v2'.
- simpl.
  reflexivity.
- rewrite eq_v2' in eq_v2.
  apply map_dec_2 in eq_v2. 

  destruct eq_v2 as [v2'' ex_v3].
  destruct ex_v3 as [v3'' eq_prod].
  destruct eq_prod as [eq_prod1 eq_v3''].
  destruct eq_prod1 as [eq_v' eq_v2''].

  exists v2''.
  exists v3''.

  split.
  + split.
    * split.
      { dependent destruction eq.
        simpl in *.
        rewrite <- eq_v'.
        assumption.
      }
      { assumption.
      }
     * assumption.
    + assumption.
Defined.