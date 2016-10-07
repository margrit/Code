(*Reg_Exp1=Reg_Exp2 wenn beide die gleiche Sprache beschreiben*)
Require Import Reg_Exp.

Lemma Reg_plus {A:Type} (e1 : @Reg_Exp A) :
    Plus e1 e1  = e1.
Proof.
destruct Plus.
-



(*Die Gleichheit zwischen regulären Ausdrücken ist entscheidbar.*)

(*Abschlusseigenschaften von regulären/entscheidbaren Sprachen
- Konkatenation
- Hüllenbildung
- Vereinigung
- Schnittmenge
- Komplement
*)