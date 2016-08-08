Load DFA_Def.

(** Mit dem Table Filling Algorithmus indet man heraus, ob Zustände äquivalent sind. Man unterscheidet
 zuerst Endzustände von allen anderen und geht dann iterativ vor, indem man prüft, ob zwei Zustände mit
 dem gleichen Eingabesymbol in den gleichen Folgezustand abbilden. Es werden Äquivalenzklassen über
 Zustände aufgebaut.*)

(* Die akzeptierenden Zustände werden durch [is_accepting] beschrieben.*)

(* erreichbare Zustände*)
Definition reachable := [fun x y => [exists a, Conf_DFA_step x a = y]].

Definition Q_reachable := (nil ++ reachable Q).

(* Um zu zeigen, dass Zustände gleich sind, müssen sie durch die gleiche Eingabe in den gleichen
 Folgezustand abbilden.*)
Inductive Eq_Q_step : Conf_DFA -> Conf_DFA -> Type :=
  | eq_step : forall (p : Q) (q : Q) (a : Sigma) (w : @Word Sigma) (eq : (delta p a) = (delta q a)),
    Eq_Q_step (p, (snoc w a)) (q, (snoc w a)).

Definition eq_Q (q p : Conf_DFA) :=
  next_Conf p = next_Conf q.

Print eq_Q.

(*Äquivalente Zustände in einer Liste speichern.*)
