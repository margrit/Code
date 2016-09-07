Require Import Bool.
Require DTS_Def.
Require Import Program.

(*Require Import Word_Prop. *)

(* Sigma ist nicht in der Umgebung. Da wir sie als Parameter definiert haben. Es geht weder mit 
Load noch Require Import oder Export :( Irgendwie scheint das mit den Modulen nicht ganz hin zu 
hauen. 

Module wirklich nur mit Parametern und Axiomen "füllen"? *)

Module DTS_Prop  (Par : DTS_Def.DTS_Par) <: DTS_Def.DTS_Par.
Import Par.
Print Q.
Definition Q := Q.
Definition Sigma := Sigma.
Definition delta := delta.
Definition is_accepting := is_accepting.
Definition q0 := q0.
Print Q.
Module Fun_Par := DTS_Def.DTS_Fun Par.
Import Fun_Par.
Import Word_Prop.

Print Q.
(*Module DTS_Prop ist abhängig von DTS_Fun wie DTS_Fun von DTS_Par*)


Lemma eq_Q_eq_delta_hat : forall (w : @Word Sigma)(p q : Q)(d : forall q p : Q, (p = q) ),
delta_hat q w = delta_hat p w.
Proof.
intros.
induction w.
- simpl.
  apply d.
- simpl.
  rewrite IHw.
  reflexivity.
Qed.

Lemma delta_hat_eps (q : Q) (w : @Word Sigma) :
delta_hat q eps = q.
Proof.
simpl.
reflexivity.
Defined.

Lemma eq_Q_eq_delta_hat_left : forall (w : @Word Sigma)(p q : Q),
q = p -> delta_hat q w = delta_hat p w.
Proof.
intros.
induction w.
- simpl.
  assumption.
- simpl.
  rewrite IHw.
  reflexivity.
Defined.

Lemma eq_Q_eq_delta_hat_right : forall (p q : Q),
(forall (w : @Word Sigma), delta_hat q w = delta_hat p w) -> q = p.
Proof.
intros.
pose (H eps).
simpl in e.
exact e.
Defined.

(**  *[Lang_delta] und [Lang_Conf] beschreiben die gleichen Sprachen.*)

(** Um zu zeigen, dass [Lang_delta] und [Lang_Conf] die Äquivalent zueinander sind, muss sowohl
[Lang_delta] w -> [Lang_Conf] w als auch [Lang_Conf] w -> [Lang_delta] w gezeigt werden. Dazu
sind eine Reihe von Hilfslemmata norwendig.*)

(** Hilfslemmata für [Lang_delta_Lang_Conf]*)
Lemma delta_hat_Conf_reverse (w : @Word Sigma) : forall (q : Q),
               Conf_rel (q, (word_reverse w)) (delta_hat q (word_reverse w), eps).
Proof.
induction w.
- intro q.
  simpl.
  apply refl.
- intro q.
  simpl.
  rewrite (delta_hat_Lemma q a (word_reverse w)).
  pose (IHw (delta q a)) as step2.
  exact (step _ _ _ (one_step q a (word_reverse w)) step2).
Qed.

Lemma delta_hat_Conf (w : @Word Sigma) : forall (q : Q),
               Conf_rel (q, w)  (delta_hat q w, eps).
Proof.
  rewrite <- (word_reverse_idempotent w).
  exact (delta_hat_Conf_reverse (word_reverse w)).
Qed.

(** Hinrichtung der Äquivalenz: *)
Lemma Lang_delta_Lang_Conf {w: @Word Sigma} :
             Lang_delta w -> Lang_Conf w.
Proof.
intro LDw.
unfold Lang_Conf.
unfold Lang_delta in LDw.
exists (delta_hat q0 w).
split.
  - exact LDw.
  - exact (delta_hat_Conf w q0).
Qed.

(** Hilfslemmata für [Lang_Conf_Lang_delta].*)
(** Die vollständige Abarbeitung eines umgedrehten Wortes.*)
Lemma Conf_delta_hat_reverse (w : @Word Sigma) : forall (q p : Q),
                Conf_rel (q, word_reverse w) (p, eps) ->
                delta_hat q (word_reverse w)= p.
Proof.
induction w.
- simpl.
  intros q p rel.
  dependent destruction rel.
  + reflexivity.
  + dependent destruction c.
    induction w.
    * dependent induction x.
    * dependent induction x.
- simpl.
  intros q p rel.
  rewrite delta_hat_Lemma.
  dependent destruction rel.
  + rewrite <- (word_reverse_snoc w a) in x.
     apply (f_equal word_reverse) in x.
     rewrite (word_reverse_idempotent (snoc w a)) in x.
     simpl in x.
     dependent destruction x.
  + dependent induction c.
     rewrite <- (word_reverse_idempotent w0) in x.
     rewrite <- (word_reverse_snoc (word_reverse w0) a0) in x.
     rewrite <- (word_reverse_snoc w a) in x.
     apply (word_reverse_injective) in x.
     injection x.
     intros a0Eqa revw0Eqw.
     rewrite a0Eqa in rel.
     apply (f_equal word_reverse) in revw0Eqw.
     rewrite (word_reverse_idempotent w0) in revw0Eqw.
     rewrite revw0Eqw in rel.
     exact (IHw (delta q a) p rel).
Defined.

Lemma Conf_delta_hat (w : @Word Sigma) : forall (q p : Q),
                Conf_rel (q, w) (p, eps) ->
                delta_hat q w = p.
Proof.
  rewrite <- (word_reverse_idempotent w).
  exact (Conf_delta_hat_reverse (word_reverse w)).
Qed.

(** Rückrichtung der Äquivalenz: *)
Lemma Lang_Conf_Lang_delta {w: @Word Sigma} :
             Lang_Conf w -> Lang_delta w.
Proof.
intro LCw.
unfold Lang_delta.
unfold Lang_Conf in LCw.
destruct LCw as [p [pacc rel]].
rewrite (Conf_delta_hat w q0 p rel).
exact pacc.
Defined.

End DTS_Prop.

