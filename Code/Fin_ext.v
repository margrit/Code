Require Import Fin.
Require Import Arith.


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
- apply (caseS' a); apply (caseS' b).
  + left.
    reflexivity.
  + right.
    discriminate.
  + right.
    discriminate.
  + intros b' a'.
    destruct (IHn a' b').
    * left.
      rewrite e.
      reflexivity.
    * right.
      unfold not.
      intro eq_a'b'.
      apply FS_inj in eq_a'b'.
      contradict n0.
      assumption.
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

