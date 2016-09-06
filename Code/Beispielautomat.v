Load DTS_Def.
(*Inductive Sigma := h : Sigma | a : Sigma | l : Sigma | o : Sigma.*)

Inductive Q' := on : Q' | off : Q'.
Inductive Sigma' := press : Sigma'.

Definition Q'_size := 2.
Definition Sigma'_size := 1.

(*Definition, welche Übergänge möglich sind.*)
Fixpoint delta' (p : Q') (a : Sigma') : Q' :=
match p with
  | on  => off
  | off  => on
end.

(*Abbildungen to, from, toFrom und fromTo zu Fin und isFinite *)