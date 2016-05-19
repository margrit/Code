Require Import Fin.
Require Import Arith.
Require Import Program.


(* We need some Extensions to the Vectors.Fin library, first of all *)
(* versions of to_nat and of_nat with strong sums *) 

Fixpoint of_nat' (p n : nat) : (t n) + { m : nat & p = n + m }.
induction n.
- right.
  exists p.
  simpl.
  reflexivity.
- induction p.
  + left.
    pose (@F1 n).
    assumption.
  + pose (of_nat' p n).
    destruct s.
    * left.
      pose (FS t).
      assumption.
    * right.
      destruct s.
      exists x.
      rewrite e.
      simpl.
      reflexivity.   
Defined.

Fixpoint of_nat'' (p n : nat) : ((t n) * (p < n)) + { m : nat & p = n + m }.
induction n.
- right.
  exists p.
  simpl.
  reflexivity.
- induction p.
  + left.
    pose (@F1 n).
    split.
    * assumption.
    * apply lt_0_Sn.
  +  pose (of_nat'' p n).
     destruct s.
     destruct p0.
    * left.
      pose (FS t).
      split.
      { assumption. }
      { apply lt_n_S.
        assumption. }
    * right.
      destruct s.
      exists x.
      rewrite e.
      simpl.
      reflexivity.   
Defined.


Fixpoint to_nat' {m : nat} (n : t m) {struct n} : {i : nat & i < m} :=
  match n in (t n0) return {i : nat & i < n0} with
  | @F1 j => existT (fun i : nat => i < S j) 0 (Nat.lt_0_succ j)
  | @FS n0 p =>
      let (i, P) := @to_nat' n0 p in
      existT (fun i0 : nat => i0 < S n0) (S i) (lt_n_S i n0 P)
  end.


Theorem fin_eq_dec {n : nat} (a b : @Fin.t n): (a = b) + ~(a = b).
Proof.
induction n.
- inversion a.
- dependent destruction a;
  dependent destruction b.
 + left.
    reflexivity.
 + right.
    discriminate.
 + right.
    discriminate.
 + destruct (IHn a b).
    * left.
      rewrite e.
      reflexivity.
    * right.
      simplify_eq.
      intro.
      apply FS_inj in H.
      contradict n0.
      assumption.

      (* das geht auch: 
      dependent destruction H.
      destruct n0.
      reflexivity. *)
         
      (* So ginge es weiter mit dem, was wir am Schluss versucht haben, 
         allerdings immer noch mit dependent destruction, 
         d.h. wir haben implizit "Axiom K" benutzt):
          
         contradict H.
         pose (eq_app_dep (@projT2 nat @Fin.t) H).
         compute in e.
         dependent destruction H.
         reflexivity. *)
Defined.


Inductive fin_le : forall {n : nat}, (@Fin.t n) -> (@Fin.t n) -> Type
  := 
  | le_f1 : forall {n : nat} (f' : @Fin.t (S n)),fin_le F1 f'
  | le_fs : forall {n : nat} (f : @Fin.t (S n)) (f' : @Fin.t (S n)), fin_le f f' -> fin_le (FS f) (FS f').

Check le_f1.

Definition fin_lt {n : nat} (i : @Fin.t (S n)) (j : @Fin.t (S (S n)))
  := fin_le (FS i) j.

Lemma dec_fin_lt {n : nat} (i j : @Fin.t (S n)): (fin_le i j) + (fin_le j i) + (i = j).
Proof.
dependent induction n.
- dependent induction i.
  + dependent induction j.
    * right.
      reflexivity.
    * dependent destruction j.
  + dependent destruction i.
- dependent destruction i.
  + dependent destruction j.
    * right.
      reflexivity.
    * left.
      left.
      apply le_f1.
  + dependent destruction j.
    * left.
      right.
      apply le_f1.
    * destruct (IHn i j).
      { destruct s.
        - left.
          left. 
          apply le_fs.
          assumption.
        - left.
          right.
          apply le_fs.
          assumption.
       }
       { right.
         rewrite e. 
         reflexivity.
       }
Defined.


(* Lemmata zur Typanpassung *)

Lemma n_plus_0 : forall n,  (n + 0 = n).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Defined.

Lemma fin_pl0 {n : nat} (p : @Fin.t (n + 0)) : @Fin.t n.
Proof.
  pose (n_plus_0 n).
  rewrite <- e.  
  assumption.
Defined.


Lemma S_plus_1 : forall n,  (S n = n + 1).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Defined.

Lemma fin_S_pl1 {n : nat} (p : @Fin.t (n + 1)) : @Fin.t (S n).
Proof.
  pose (S_plus_1 n).
  rewrite e.  
  assumption.
Defined.

Print eqb.
Print Nat.eqb.
