Require DTS_Prop.
Module DTS_Example <: DTS_Def.DTS_Par.

(** Die Zustaende des Wechselschalters und die Instanziierung. *)

Inductive Q' := on : Q' | off : Q'.
Definition Q := Q'.

(** Das Eingabealphabet des Wechselschalters und die Instanziierung. *)

Inductive Sigma' := press : Sigma'.
Definition Sigma := Sigma'.

(** Definition, welche Uebergaenge moeglich sind. *)

Definition delta (p : Q) (a : Sigma) : Q :=
  match p with
    | on  => off
    | off  => on
  end.

(** Startzustand: *)

Definition q0 := off.

(** Akzeptierende Zustaende: *)

Definition is_accepting (q : Q) : Type :=
  match q with
    | on => True
    | off => False
  end.

End DTS_Example.

Module Ex_Prop := DTS_Def.DTS_Fun DTS_Example.
Import Word_Prop.
Import DTS_Example.
Import Ex_Prop.

(** Durch der oben gegebenen Definition lassen sich zwei Sprachen definieren, die mit
 einer geraden Anzahl an Eingaben [even_press] und die mit einer ungeraden Anzahl
 an Eingaben [odd_press]. *)

Inductive even_press : @Word Sigma -> Type :=
  | eps_even : even_press eps
  | snoc_even {w : @Word Sigma} {a : Sigma} : odd_press w -> even_press (snoc w a)
with odd_press : @Word Sigma -> Type :=
  | snoc_odd {w : @Word Sigma} {a : Sigma} : even_press w -> odd_press (snoc w a).

(** Beweis, dass die Sprache des [DTS_Example] = [odd_press] ist indem die folgenden
 Implikationen gezeigt werden.
 - forall w, Lang_delta w -> odd_press w
 - forall w, odd_press w -> Lang_delta w
 Dazu wird ein typwertiges Prädikat benoetigt, um zu wissen, in welchem Zustand sich
 der Automat nach der Eingabe befindet. *)

Lemma finish_input : forall w,
      ((even_press w * (delta_hat q0 w = off)) +
      (odd_press w * (delta_hat q0 w = on)))%type.
Proof.
  induction w.
  - simpl.
    left.
    split.
    + exact eps_even.
    + reflexivity.
  - simpl.
    destruct IHw as [[peven x] | [podd y]].
    + right.
       split.
       * exact (snoc_odd peven).
       * rewrite x.
         simpl.
         reflexivity.
    + left.
       split.
       * exact (snoc_even podd).
       * rewrite y.
         simpl.
         reflexivity.
Defined.

(** Die Eingabe hat eine gerade oder ungerade Laenge. [even_press] und [odd_press]
 sind disjunkt. *)

Lemma even_odd_disjoint (w : @Word Sigma) :
      even_press w -> odd_press w -> False.
Proof.
  intros even odd.
  induction w.
  - inversion odd.
  - inversion even.
    inversion odd.
    exact (IHw X0 X).
Defined.

(** Jetzt koennen beide Richtungen der Aequivalenz gezeitgt werden.
 - forall w, Lang_delta w -> odd_press w
 - forall w, odd_press w -> Lang_delta w *)

Lemma Lang_odd : forall w, Lang_delta w -> odd_press w.
Proof.
  unfold Lang_delta.
  intros w w_in_L.
  pose (finish_input w) as decide_L.
  destruct decide_L as [[even off] |[odd on]].
  - rewrite off in w_in_L.
    simpl in w_in_L.
    destruct w_in_L.
  - exact odd.
Defined.

Lemma odd_Lang : forall w, odd_press w -> Lang_delta w.
Proof.
  unfold Lang_delta.
  intros w odd.
  pose (finish_input w) as decide_L.
  destruct decide_L as [[even off] |[odd' on]].
  - pose (even_odd_disjoint w even odd) as ff.
    destruct ff.
  - rewrite on.
    simpl.
    exact I.
Defined.

(** Aequivalenz zwischen odd_press und Lang_delta. Die Sprache die von dem 
Toggle Automaten akzeptiert wird besteht genau aus den Woertern, deren Laenge
ungerade ist. *)

Require Import Equivalences.
Module Lang_Toggle : Logical_EQ_type_valued_pred.
Definition  base := @Word Sigma.
Definition P := odd_press.
Definition Q := Lang_delta.
Definition pq := odd_Lang.
Definition qp := Lang_odd.
End Lang_Toggle.

(** Es muss noch gezeigt werden, dass das Eingabealphabet und die Zustandsmenge
 endlich sind. *)

Require Import FiniteClass.
Require Import Fin.
Require Import Program.

Instance Q_Finite : Finite Q := {
  card := 2;
  to x := match x with
    | off => F1
    | on => FS (F1)
  end;
  from i := match i with
    | F1         => off
    | FS  (F1 )  => on
    | FS  (FS _) => off
  end
}.
Proof.
  - intro i.
    repeat dependent destruction i; reflexivity.
  - intro x.
    destruct x;reflexivity.
Qed.

Instance Sigma_Finite : Finite Sigma := {
  card := 1;
  to x := match x with
    | press => F1
  end;
  from i := match i with
    | F1         => press
    | FS  (F1 )  => press
    | FS  (FS _) => press
  end
}.
Proof.
  - intro i.
    repeat dependent destruction i; reflexivity.
  - intro x.
    destruct x;reflexivity.
Qed.
