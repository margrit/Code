Load DFA_Def.

Section RegExp.
Variable char : Sigma. (*allerdings nur ein einzelnes Zeichen*)


(*
Definition compl L : dlang char := predC L.

Definition prod L1 L2 : dlang char := [pred w in L1 | w \in L2].

Definition plus L1 L2 : dlang char := [pred w | (w \in L1) || (w \in L2)].

Lemma plusP r s w :
  reflect (w \in r \/ w \in s) (w \in plus r s).
Proof. rewrite !inE. exact: orP. Qed.

Definition conc (L1 L2: dlang char) : dlang char :=
  fun v => [exists i : 'I_(size v).+1, L1 (take i v) && L2 (drop i v)].
*)
(*Lemma concP {L1 L2 : dlang char} {w : word char} :
  reflect (exists w1 w2, w = w1 ++ w2 /\ w1 \in L1 /\ w2 \in L2) (w \in conc L1 L2).
Proof. apply: (iffP existsP) => [[n] /andP [H1 H2] | [w1] [w2] [e [H1 H2]]].
  - exists (take n w). exists (drop n w). by rewrite cat_take_drop -topredE.
  - have lt_w1: size w1 < (size w).+1 by rewrite e size_cat ltnS leq_addr.
    exists (Ordinal lt_w1); subst.
    rewrite take_size_cat // drop_size_cat //. exact/andP.
Qed.

Lemma conc_cat w1 w2 L1 L2 : w1 \in L1 -> w2 \in L2 -> w1 ++ w2 \in conc L1 L2.
Proof. move => H1 H2. apply/concP. exists w1. by exists w2. Qed.

Lemma conc_eq (l1: dlang char) l2 l3 l4: l1 =i l2 -> l3 =i l4 -> conc l1 l3 =i conc l2 l4.
Proof.
  move => H1 H2 w. apply: eq_existsb => n.
  by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
Qed.
*)

(*
Definition residual x L : dlang char := [pred w | x :: w \in L].

Definition star L : dlang char :=
  fix star v := if v is x :: v' then conc (residual x L) star v' else true.
*)

(*Lemma starP : forall {L v},
  reflect (exists2 vv, all [predD L & eps] vv & v = flatten vv) (v \in star L).
Proof.
move=> L v;
  elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n.
  by left; exists [::].
apply: (iffP concP) => [[u] [v'] [def_v [Lxu starLv']] | [[|[|y u] vv] //=]].
  case/IHn: starLv' => [|vv Lvv def_v'].
    by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl.
  by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v'].
case/andP=> Lyu Lvv [def_x def_v]; exists u. exists (flatten vv).
subst. split => //; split => //. apply/IHn; last by exists vv.
by rewrite -ltnS (leq_trans _ le_v_n) // size_cat !ltnS leq_addl.
Qed.

Lemma star_cat w1 w2 L : w1 \in L -> w2 \in (star L) -> w1 ++ w2 \in star L.
Proof.
  case: w1 => [|a w1] // H1 /starP [vv Ha Hf]. apply/starP.
  by exists ((a::w1) :: vv); rewrite ?Hf //= H1.
Qed.

Lemma starI (L : dlang char) vv :
  (forall v, v \in vv -> v \in L) -> flatten vv \in star L.
Proof. elim: vv => /= [//| v vv IHvv /all1s [H1 H2]]. exact: star_cat _ (IHvv _). Qed.

Lemma star_eq (l1 : dlang char) l2: l1 =i l2 -> star l1 =i star l2.
Proof.
  move => H1 w. apply/starP/starP; move => [] vv H3 H4; exists vv => //;
  erewrite eq_all; try eexact H3; move => x /=; by rewrite ?H1 // -?H1.
Qed.*)

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

(*Die Sprache von einem regulären Ausdruck, wenn auch etwas kompliziert.*)
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

SearchPattern (nat -> nat -> bool).

Eval compute in (reg_match testreg Nat.eqb eps).
Eval compute in (reg_match testreg Nat.eqb (snoc eps 1)).
Eval compute in (reg_match testreg Nat.eqb (snoc (snoc eps 1)2)).

(*Lemma eq_regexp_dec e1 e2 : {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply: eq_comparable. Qed.

Definition regexp_eqMixin := EqMixin (compareP eq_regexp_dec).
Canonical Structure form_eqType := EqType _ regexp_eqMixin.

End RegExp.

Implicit Arguments void [].
Implicit Arguments eps [].

Section ReLang.
Variable char: eqType.*)
(* Entscheidbare Sprache über jeden regulären Ausdruck.*)
Fixpoint mem_Reg_Exp e:=
match e with
  | Void => void char
  | Eps => eps char
  | Atom x => atom x
  | Star e1 => star (mem_Reg_Exp e1)
  | Plus e1 e2 => plus(mem_Reg_Exp e1)(mem_Reg_Exp e2)
  | And e1 e2 => and (mem_Reg_Exp e1)(mem_Reg_Exp e2)
  | Conc e1 e2 => conc (mem_Reg_Exp e1)(mem_Reg_Exp e2)
  | Not e1 => compl (mem_Reg_Exp e1)
end.

Fixpoint standard (e: Reg_Exp char) :=
  match e with
    | Not _ => false
    | And _ _ => false
    | Dot => false
    | _ => true
  end.