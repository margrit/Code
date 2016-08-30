Load DFA_Def.

Section RegExp.
(*Variable char : Sigma. allerdings nur ein einzelnes Zeichen*)

(** Der Typ eines regulären Ausdrucks induktiv definiert.*)
Inductive Reg_Exp {A: Type} :=
| Void : @Reg_Exp A
| Eps : @Reg_Exp A
| Single : A -> @Reg_Exp A
| Star : @Reg_Exp A -> @Reg_Exp A
| Plus : @Reg_Exp A ->  @Reg_Exp A -> @Reg_Exp A
| Conc : @Reg_Exp A -> @Reg_Exp A -> @Reg_Exp A
| Not : @Reg_Exp A -> @Reg_Exp A.

(** boolsche Funktion auf Wörtern -> Sprache*)

(** Anhängen eines Zeichens an das zweite Teilwort eines aus zwei Teilwörtern bestehenden Wortes.*)
Fixpoint appsec {A : Type} (ps : @Word (@Word A * @Word A)) (x : A) : 
  @Word (@Word A * @Word A) :=
match ps with
 | eps => eps
 | snoc ps' (w1, w2) => snoc (appsec ps' x) (w1, snoc w2 x)
end.

Eval compute in (appsec (snoc eps (eps, eps)) 2).

(** Aufsplitten eines Wortes in zwei Teilwörter. Das erste Teilword wird dabei immer länger und das
 zweite Teilwort dementsprechend kürzer.*)
Fixpoint splits {A : Type} (w : @Word A) : @Word (@Word A * @Word A):=
match w with
| eps => snoc eps (eps, eps)
| snoc w x => snoc (appsec (splits w) x) (snoc w x, eps)
end.

Eval compute in (splits (snoc (snoc (snoc eps 2) 3)4)).

(** Formalisierung des Existenzquantors auf Wörtern analog zu [existsb], das auf Listen arbeitet.*)
Fixpoint existsbw {A : Type} (p : A -> bool) (w : @Word A) : bool :=
match w with
  | eps => false
  | snoc w' x => p x || existsbw p w'
end.

(** Formalisierung des Allquantors auf Wörtern analog zu [forallb], das auf Listen arbeitet.*)
Fixpoint forallbw {A : Type} (p : A -> bool) (w : @Word A) : bool :=
match w with
  | eps => true
  | snoc w' x => p x && forallbw p w'
end.

(** "Kreuzprodukt" zweier Prädikate *)
Fixpoint pair_andb {A B : Type} (p : A -> bool) (q : B -> bool) (c : A * B) : bool :=
match c with
| (a,b) => p a && q b
end.


(** Ein einzelnes Zeichen an ein Wort anhängen.*)
Definition concat_word_single {A : Type} (x : A) (w : @Word(@Word A)) : @Word(@Word A) :=
  snoc w (snoc eps x).

Eval compute in (concat_word_single 2 (snoc eps (snoc eps 3))).

(** Ein Wort über Wörtern in ein Wort umwandeln (Monadenmultiplikation von Word).*)
Fixpoint flatten_word {A : Type} (w : @Word (@Word A)) : @Word A :=
  match w with
    | eps => eps
    | snoc w1 w2 => concat_word (flatten_word w1) w2
  end.

(** bind-Operation der Monade Word*)
Definition concat_map_word {A B : Type} (f : A -> @Word B) (w : @Word A) : @Word B :=
flatten_word(map_word f w).

(** Hilfsfunktion für [split2]*)
Fixpoint last_snoc {A : Type} (x : A) (w : @Word(@Word A)) : @Word(@Word(@Word A)) :=
  match w with
    | eps => eps
    | snoc w1 w2  => snoc eps (snoc w1 (snoc w2 x))
  end.

(** Generierung aller Zerlegungen eines Wortes in alle nichtleeren Teilwörter *)
Fixpoint split2 {A : Type} (w : @Word A) : @Word (@Word (@Word A)) :=
match w with
  | eps => snoc eps eps
  | snoc w' x => concat_word (map_word (concat_word_single x) (split2 w')) 
                                              (concat_map_word (last_snoc x) (split2 w'))
end.

Eval compute in (split2 (snoc (snoc(snoc(snoc eps 1)2)3)4)).
Eval compute in (split2 eps).
Eval compute in (split2 [ 1 ]).
Eval compute in (split2 [ 1 ; 2 ]).
Eval compute in (split2 [ 1 ; 2 ; 3]).


(*7. Definiere eine Funktion, die einem regulären Ausdruck über A die durch diesen
  Ausdruck definierte Sprache zuordnet.
*)
(** Die Sprache, die von einem regulären Ausdruck beschrieben wird. *)
Fixpoint reg_match {A : Type} (e : @Reg_Exp A) (eq: A -> A -> bool) (w : @Word A)  : bool :=
  match e, w with
  | Void  ,_ => false
  | Eps ,eps => true
  | Eps ,_=> false
  | Single x, snoc eps y => eq x y
  | Single _, _ => false
  | Conc e1 e2, w => existsbw (pair_andb (reg_match e1 eq) (reg_match e2 eq))(splits w)
  | Star e1, w' => existsbw (forallbw (reg_match e1 eq)) (split2 w')
  | Plus e1 e2, w' => (reg_match e1 eq w') || (reg_match e2 eq w')
  | Not e1, w' => negb (reg_match e1 eq w')
  end.

Definition testreg : @Reg_Exp nat := Star( Conc (Single 1)(Single 2) ).

Eval compute in (reg_match testreg Nat.eqb eps).
Eval compute in (reg_match testreg Nat.eqb (snoc eps 1)).
Eval compute in (reg_match testreg Nat.eqb (snoc (snoc eps 1)2)).

End RegExp.