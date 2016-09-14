Load Definitions_vector.

(* Automat allgemein angeleht an:
http://stackoverflow.com/questions/22475373/modelisation-of-an-automaton-with-coq *)

Record DAuto: Type :=
  mk_dauto{
  states: Q;
  alphabet: Sigma;
  initial: Q;
  final: list Q;
  transitions: Q -> Sigma -> list Q
  }.

(*Die vom Automaten akzepierte Sprache
L(A)= {w : Sigma | delta_hat (q0, w) : Q_Final} *)
