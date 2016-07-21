
Require Import Fin.
Require Import Program.

Class Finite (X : Type) : Type := {
   card : nat;
   to   : X -> @Fin.t card;
   from : @Fin.t card -> X;
   toFrom : forall i : @Fin.t card, to (from i) = i;
   fromTo : forall x : X, from (to x) = x
}.

Inductive States : Type := P1 | P2 | P3.

Instance statesFinite : Finite States := {
  card := 3;
  to x := match x with
    | P1 => F1
    | P2 => FS (F1)
    | P3 => FS (FS (F1))
  end;
  from i := match i with
    | F1         => P1
    | FS  (F1 )  => P2
    | FS  (FS _) => P3
  end
}.
Proof.
  + intro i.
    dependent destruction i.
    - reflexivity.
    - dependent destruction i.
      * reflexivity.
      * dependent destruction i.
        { reflexivity. }
        { dependent destruction i. }
  + intro x.
    destruct x;reflexivity.
Qed.

Print statesFinite.
