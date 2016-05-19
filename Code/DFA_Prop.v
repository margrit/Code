Require Import Bool.
Load DFA_Def.

(* Erweiterte Überführungsfunktion über *)
Theorem delta_hat_append : forall (xs : list Sigma) (ys : list Sigma) (q : Q),
  delta_hat q (xs ++ ys) = delta_hat (delta_hat q xs) ys.
Proof.
  induction xs.
  - simpl.
    intros ys q.
    reflexivity.
  - simpl.
    intros.
    apply IHxs.
Qed.

(*i*)
(*
Inductive Konf_DFA_step : Konf_DFA -> Konf_DFA -> Type :=
 | one_step : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma) (eq : (delta q a) = p), 
                                    Konf_DFA_step (q, (cons a w)) (p, w).
Inductive Konf_rel_DFA : Konf_DFA -> Konf_DFA -> Type :=
  | refl    : forall (K : Konf_DFA), Konf_rel_DFA K K
  | step  : forall (K L M : Konf_DFA),
                                    Konf_rel_DFA K L ->
                                    Konf_DFA_step L M ->
                                    Konf_rel_DFA K M.
*)

(*ii*)
(*(|--) Konf_DFA -> (Konf_DFA -> Prop)*)
Inductive Konf_DFA_step_bool : Konf_DFA -> (Konf_DFA -> Prop) :=
 | one_step_bool : forall (q : Q) (p : Q) (a : Sigma) (w : list Sigma) (eq : (delta q a) = p),
                                    Konf_DFA_step_bool (q, (cons a w)) (p, w).
(*(|--* ) Konf_DFA -> (Konf_DFA -> Prop)*)
Inductive Konf_rel_DFA_bool : Konf_DFA -> (Konf_DFA -> Prop) :=
  | refl_bool    : forall (K : Konf_DFA), Konf_rel_DFA_bool K K
  | step_bool  : forall (K L M : Konf_DFA),
                                    Konf_rel_DFA_bool K L ->
                                    Konf_DFA_step_bool L M ->
                                    Konf_rel_DFA_bool K M.

(*iii*)
(*dec_Konf_DFA_step : (K1 : Konf_DFA) -> (K2 : Konf_DFA) -> Dec (K1 |-- K2)*)
(*dec_Konf_DFA : (K1 : Konf_DFA) -> (K2 : Konf_DFA) -> Dec (K1 |--* K2)*)

(*(ii) <=> (i) /\ (iii)*)
(*Über die Entscheidbarkeit zeigen, dass Konf_DFA -> Type = Konf_DFA -> Prop*)
Theorem Konf_eq : forall (conf: Konf_DFA), Konf_DFA_step_bool -> Konf_DFA_step.
Proof.
intros.

