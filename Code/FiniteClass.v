(** Um sicher zu stellen, dass die Zustandsmenge und die Menge des Eingabealphabets endliche
 Typen sind, sind sie Instanzen einer endlichen Klasse.*)

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
  - intro i.
    repeat dependent destruction i; reflexivity.
  - intro x.
    destruct x;reflexivity.
Qed.

Print statesFinite.

Inductive Alphabet : Type := a | b | c.

Instance alphabetFinite : Finite Alphabet := {
  card := 3;
  to x := match x with
    | a => F1
    | b => FS (F1)
    | c => FS (FS (F1))
  end;
  from i := match i with
    | F1         => a
    | FS  (F1 )  => b
    | FS  (FS _) => c
  end
}.
Proof.
  - intro i.
    repeat dependent destruction i; reflexivity.
  - intro x.
    destruct x;reflexivity.
Qed.

Print sigT.

(*Finite_Sets sind endliche Typen für die wir eine Instanz der Klasse Finite definieren können.*)
Definition Finite_Sets := sigT Finite.
Print Finite_Sets.