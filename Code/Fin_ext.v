Require Import Fin.
Require Import Arith.

(** Es werden zuerst noch ein paar Erweiterungen zur Vectors.Fin Bibliothek
 benoetigt. Als erstes eine Version von [to_nat] und [of_nat] mit konstruktiven
 Existenzquantoren bzw. abhaengige Summen. *)

(** Wenn p kleiner als n ist, dann wird das p-te Element von Fin.t n  angegeben,oder
 ein Zeugen, dass p groesser als die Kardinalitaet von Fin.t n ist. *)

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

(** Wenn p kleiner als n ist, dann wird das p-te Element von Fin.t n mit einem Beweis, dass
 p < n angegeben, oder ein Zeuge, dass p groesser als die Kardinalitaet von Fin.t n ist. *)

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
    + pose (of_nat'' p n).
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

(** Das i-te Element von Fin.t n, mit einem Beweis, dass dies kleiner ist als die
 Kardinalitaet von Fin.t n. *)

Fixpoint to_nat' {m : nat} (n : t m) {struct n} : {i : nat & i < m} :=
  match n in (t n0) return {i : nat & i < n0} with
    | @F1 j        => existT (fun i : nat => i < S j) 0 (Nat.lt_0_succ j)
    | @FS n0 p =>
      let (i, P) := @to_nat' n0 p in
      existT (fun i0 : nat => i0 < S n0) (S i) (lt_n_S i n0 P)
  end.

(** Gleichheit der Elemente von Fin.t ist entscheidbar. *)

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

(** Lemmata zur Typanpassung *)

Definition n_plus_0 (n : nat) : (n + 0 = n) := eq_sym (plus_n_O n).
  
Lemma fin_pl0 {n : nat} (p : @Fin.t (n + 0)) : @Fin.t n.
Proof.
  rewrite <- (eq_sym (plus_n_O n)).
  exact p.
Defined.

Lemma S_plus_1 (n : nat) : (S n = n + 1).
Proof.
  rewrite <- plus_n_Sm.
  rewrite n_plus_0.
  reflexivity.
Defined.

Lemma fin_S_pl1 {n : nat} (p : @Fin.t (n + 1)) : @Fin.t (S n).
Proof.
  rewrite <- plus_n_Sm in p.
  rewrite n_plus_0 in p.
  exact p.
Defined.