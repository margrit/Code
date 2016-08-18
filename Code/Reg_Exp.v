Load DFA_Def.

Section RegExp.
(*Variable char : Sigma. allerdings nur ein einzelnes Zeichen*)

Inductive Reg_Exp {A: Type} :=
| Void : @Reg_Exp A
| Eps : @Reg_Exp A
| Single : A -> @Reg_Exp A
| Star : @Reg_Exp A -> @Reg_Exp A
| Plus : @Reg_Exp A ->  @Reg_Exp A -> @Reg_Exp A
| Conc : @Reg_Exp A -> @Reg_Exp A -> @Reg_Exp A
| Not : @Reg_Exp A -> @Reg_Exp A
| Minus : @Reg_Exp A -> A -> @Reg_Exp A.

(*boolsche Funktion auf Wörtern -> Sprache*)

Fixpoint appsec {A : Type} (ps : @Word (@Word A * @Word A)) (x : A) : 
  @Word (@Word A * @Word A) :=
match ps with
 | eps => eps
 | snoc ps' (w1, w2) => snoc (appsec ps' x) (w1, snoc w2 x)
end.

Eval compute in (appsec (snoc eps (eps, eps)) 2).

Fixpoint splits {A : Type} (w : @Word A) : @Word (@Word A * @Word A):=
match w with
| eps => snoc eps (eps, eps)
| snoc w x => snoc (appsec (splits w) x) (snoc w x, eps)
end.

Eval compute in (splits (snoc (snoc eps 2) 3)).

Fixpoint existsbw {A : Type} (p : A -> bool) (w : @Word A) : bool :=
match w with
  | eps => false
  | snoc w' x => p x || existsbw p w'
end.

Fixpoint forallbw {A : Type} (p : A -> bool) (w : @Word A) : bool :=
match w with
  | eps => true
  | snoc w' x => p x && forallbw p w'
end.

Fixpoint pair_pred {A : Type} (p1 p2 : A -> bool) (a : A * A) : bool :=
match a with
| (a1,a2) => p1 a1 && p2 a2
end.

Fixpoint map_word {A B : Type} (f : A -> B) (w : @Word A) : @Word B :=
 match w with
   | eps => eps
   | snoc w' x => snoc (map_word f w') (f x)
 end.

Definition concat_word_single {A : Type} (x : A) (w : @Word(@Word A)) : @Word(@Word A) :=
  snoc w (snoc eps x).

Eval compute in (concat_word_single 2 (snoc eps (snoc eps 3))).

Fixpoint flatten_word {A : Type} (w : @Word (@Word A)) : @Word A :=
  match w with
    | eps => eps
    | snoc w1 w2 => concat_word (flatten_word w1) w2
  end.

Definition concat_map_word {A B : Type} (f : A -> @Word B) (w : @Word A) : @Word B :=
flatten_word(map_word f w).

Fixpoint last_snoc {A : Type} (x : A) (w : @Word(@Word A)) : @Word(@Word(@Word A)) :=
  match w with
    | eps => eps
    | snoc w1 w2  => snoc eps (snoc w1 (snoc w2 x))
  end.

Fixpoint split2 {A : Type} (w : @Word A) : @Word (@Word (@Word A)) :=
match w with
  | eps => snoc eps eps
  | snoc w' x => concat_word (map_word (concat_word_single x) (split2 w')) 
                                              (concat_map_word (last_snoc x) (split2 w'))
end.

Eval compute in (split2 (snoc (snoc(snoc(snoc eps 1)2)3)4)).
Eval compute in (split2 eps).

(*Die Sprache, die von einem regulären Ausdruck beschrieben wird, wenn auch etwas kompliziert.*)
Fixpoint reg_match {A : Type} (e : @Reg_Exp A) (eq: A -> A -> bool) (w : @Word A)  : bool :=
  match e, w with
  | Void  ,_ => false
  | Eps ,eps => true
  | Eps ,_=> false
  | Single x, snoc eps y => eq x y
  | Single _, _ => false
  | Minus e1 x, w => reg_match e1 eq (snoc w x)
  | Conc e1 e2, w => existsbw (pair_pred (reg_match e1 eq) (reg_match e2 eq))(splits w)
  | Star e1, w' => existsbw (forallbw (reg_match e1 eq)) (split2 w')
  | Plus e1 e2, w' => (reg_match e1 eq w') || (reg_match e2 eq w')
  | Not e1, w' => negb (reg_match e1 eq w')
  end.

Definition testreg : @Reg_Exp nat := Star( Conc (Single 1)(Single 2) ).

Eval compute in (reg_match testreg Nat.eqb eps).
Eval compute in (reg_match testreg Nat.eqb (snoc eps 1)).
Eval compute in (reg_match testreg Nat.eqb (snoc (snoc eps 1)2)).

Lemma eq_Reg_Exp_dec {A : Type} (e1 e2 : @Reg_Exp A) : {e1 = e2} + {e1 <> e2}.
Proof.
induction e2.
induction e1.
- left.
  reflexivity.
- right.
  congruence.
- right.
  congruence.
- right.
  congruence.
- right.
  congruence.
- right.
  congruence.
- right.
  congruence.
- right.
  congruence.
- decide equality.
  + right.
     rewrite negb.

End RegExp.