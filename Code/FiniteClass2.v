Require Import Fin.
Require Import Program.

Class Finite (X : Type) : Type := {
   card : nat;
   to   : X -> @Fin.t card;
   from : @Fin.t card -> X;
   toFrom : forall i : @Fin.t card, to (from i) = i;
   fromTo : forall x : X, from (to x) = x
}.

Print sigT.

(*Finite_Sets sind endliche Typen für die wir eine Instanz der Klasse Finite definieren können.*)
Definition FinSet := sigT Finite.
Print FinSet.

Print option.


Instance optionFin (X : Type) `{xFin : Finite X} : Finite (option X) := {
  card := S card;
  to x := match x with
    | None => F1
    | Some x' => FS (to x')
  end;
  (* funktioniert so leider nicht: *)
  from i := match i with
    | F1    => None
    | FS i' => Some (from i')
  end
}.
Proof. 



  (* das hier funktioniet auch nicht
  from i := match i with
    | @F1 _ => None
    | @FS card i' => Some (from i')
  end
 *)