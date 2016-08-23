Load DFA_Def.

(** Mit dem Table Filling Algorithmus findet man heraus, ob Zustände äquivalent sind. Man unterscheidet
 zuerst Endzustände von allen anderen und geht dann iterativ vor, indem man prüft, ob zwei Zustände mit
 dem gleichen Eingabesymbol in den gleichen Folgezustand abbilden. Es werden so Äquivalenzklassen
 über Zustände aufgebaut.*)

(* Die akzeptierenden Zustände werden durch [is_accepting] beschrieben.*)

(* erreichbare Zustände*)

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

Lemma delta_hat_eps (q : Q) (w : @Word Sigma) :
delta_hat q eps = q.
Proof.
simpl.
reflexivity.
Defined.

Lemma eq_Q_eq_delta_hat_right : forall (p q : Q),
(forall (w : @Word Sigma), delta_hat q w = delta_hat p w) -> q = p.
Proof.
intros.
pose (H eps).
simpl in e.
assumption.
Defined.

(*zwei Wörter haben die gleiche Länge*)
Lemma dec_eq_word {A : Type} (w1 w2: @Word A) : 


(*Äquivalenz zwischen Wörtern *)
Lemma w_eq_v : forall w v : @Word Sigma, forall q : Q,
  delta_hat q w = delta_hat q v -> w = v.
Proof.
intros.



Fixpoint reachable (q : Q) : bool :=
  if q = q0 then true else exists w, Conf_rel_DFA

Definition reachable := [fun x y => [exists a, Conf_DFA_step x a = y]].
Print reachable.

(*Definition Q_reachable := (nil ++ reachable Q).*)

(* Um zu zeigen, dass Zustände gleich sind, müssen sie durch die gleiche Eingabe in den gleichen
 Folgezustand abbilden.*)
Inductive Eq_Q_step : Conf_DFA -> Conf_DFA -> Type :=
  | eq_step : forall (p : Q) (q : Q) (a : Sigma) (w : @Word Sigma) (eq : (delta p a) = (delta q a)),
    Eq_Q_step (p, (snoc w a)) (q, (snoc w a)).

Definition eq_Q (q p : Conf_DFA) :=
  next_Conf p = next_Conf q.

Print eq_Q.

(*Äquivalente Zustände in einer Liste speichern.*)
