(*Quelle: https://gist.github.com/anonymous/e9493ce195219c4c2b18 *)
Require ZArith.
Require Eqdep_dec.
Require Import List.
Import ListNotations.

Scheme le_elim := Induction for le Sort Prop.

Lemma le_irrelev : forall n m (p q: n <= m), 
p = q.
induction p using le_elim;intro q.
replace (le_n n) with
 (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).

 generalize (refl_equal n).
 pattern n at 2 4 6 10, q;case q; [intro | intros m l e].
 rewrite <- (Eqdep_dec.eq_rect_eq_dec Peano_dec.eq_nat_dec);trivial.
 contradiction (Le.le_Sn_n m);rewrite <- e;assumption.
 
 reflexivity.

replace (le_S n m p) with
 (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).

 generalize (refl_equal (S m)).
 pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
 contradiction (Le.le_Sn_n m); rewrite Heq; assumption.
 injection HeqS;intro Heq; generalize l HeqS.
 rewrite <- Heq; intros; 
  rewrite <- (Eqdep_dec.eq_rect_eq_dec Peano_dec.eq_nat_dec).
 rewrite (IHp l0);reflexivity.

 reflexivity.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Inductive repeats {X:Type} : list X -> Prop :=
| rep_base : forall l x, appears_in x l -> repeats (x::l)
| rep_step : forall l x, repeats l -> repeats (x::l).

Inductive member {X:Type} (a:X) : list X -> Type :=
  | HFirst : forall l, member a (a::l)
  | HNext : forall b l, member a l -> member a (b::l).

Definition index_strong {X:Type} n : forall (l:list X), 
 n < length l -> X.
induction n;destruct l; simpl; intros.
 exfalso. eapply Le.le_Sn_0. eassumption.
 assumption.
 exfalso. eapply Le.le_Sn_0. eassumption.
 apply (IHn l). apply le_S_n. assumption.
Defined.

Lemma index_proof_indep : forall (X:Type) n (l:list X) pf1 pf2,
 index_strong n l pf1 = index_strong n l pf2.
Proof. induction n;intros; destruct l; simpl. inversion pf1. reflexivity.
 inversion pf1. apply IHn. Qed.

Lemma listsearch : forall (X:Type) (l1 l2:list X) k 
 (H : forall (n : nat) (pfn : n < length l1),
     {m : nat &
     {pfm : m < length l2 | index_strong m l2 pfm = index_strong n l1 pfn}}),
(sum 
({n : nat & {pfn : n < length l1 |
   projT1 (H n pfn) = k}})
(forall n pfn, projT1 (H n pfn) <> k)
). induction l1 as [|x l1];intros.
 right. intros. inversion pfn.
 assert (Hi : 0 < length (x::l1)). apply Le.le_n_S. apply Le.le_0_n.
 destruct (H 0 Hi) eqn:Hd. destruct s. destruct (Peano_dec.eq_nat_dec x0 k). 
 subst.
  left. exists 0. exists Hi. rewrite Hd. reflexivity.
set (H' := (fun (n0 : nat) (pfn : n0 < length l1) =>
               let pfu := Le.le_n_S (S n0) (length l1) pfn in
               let s2 := H (S n0) pfu in
               let (x2, s3) := s2 in
               let (x3, e0) := s3 in
               existT
                 (fun m : nat =>
                  {pfm : m < length l2 |
                  index_strong m l2 pfm = index_strong n0 l1 pfn}) x2
                 (exist
                    (fun pfm : x2 < length l2 =>
                     index_strong x2 l2 pfm = index_strong n0 l1 pfn) x3
                    (eq_trans e0
                       (index_proof_indep X n0 l1
                          (le_S_n (S n0) (length l1) pfu) pfn))))).
destruct (IHl1 l2 k H').
 destruct s. destruct s. left. exists (S x2). 
exists ((Le.le_n_S (S x2) (length l1) x3)).
rewrite <- e0. unfold H'.
destruct (H (S x2) (Le.le_n_S (S x2) (length l1) x3)).
 simpl. destruct s. reflexivity.
right. intros. intro abs. unfold not in n0.
 destruct n1. rewrite (le_irrelev _ _ pfn Hi) in abs.
 rewrite Hd in abs. simpl in abs. apply n. apply abs.
  specialize (n0 n1). apply n0 with (pfn:= Le.le_S_n _ _ pfn).
 fold (@length X). rewrite <- abs. unfold H'.
rewrite (le_irrelev _ _ 
  (Le.le_n_S (S n1) (length l1) (Le.le_S_n (S n1) (length l1) pfn)) pfn).
 destruct (H (S n1) pfn). destruct s. reflexivity.
Qed.

Theorem index_appear_equiv' : forall (X:Type) (l:list X) x, 
 appears_in x l <-> (exists n, n < length l /\
                      forall pf, index_strong n l pf = x).
Proof. induction l as [|x l];simpl;split;intros.
 inversion H.
 destruct H. destruct H. inversion H.
 inversion H;subst.
  exists 0. split. apply Le.le_n_S. apply Le.le_0_n. reflexivity.
  destruct (IHl x0). destruct (H0 H1) as [witness H3]. destruct H3.
   exists (S witness). split. apply Le.le_n_S. apply H3.
   intros. apply H4.
 destruct H as [witness H]. destruct H. destruct witness.
  specialize (H0 H). simpl in H0. rewrite H0. constructor.
  specialize (H0 H). simpl in H0. constructor. apply IHl.
   exists witness. split. apply  Le.le_S_n. apply H.
   intros. rewrite <- H0. apply index_proof_indep.
Qed.

Theorem index_member_equiv' : forall (X:Type) (l:list X) x, 
  (member x l -> { n:nat | n < length l /\
       forall pf, index_strong n l pf = x}) *
  ({ n:nat | n < length l /\ forall pf, index_strong n l pf = x} -> 
       member x l).
Proof. induction l as [|x l];simpl;split;intros.
 inversion X0.
 destruct H. destruct a. exfalso. inversion H.
 inversion X0;subst.
  exists 0. split. apply Le.le_n_S. apply Le.le_0_n. reflexivity.
  destruct (IHl x0). destruct (s X1). destruct a.
   exists (S x1). split. apply Le.le_n_S. apply H.
   intros. apply H0.
 destruct H. destruct a. destruct x1.
  specialize (H0 H). simpl in H0. rewrite H0. constructor.
  specialize (H0 H). simpl in H0. constructor. apply IHl.
   exists x1. split. apply  Le.le_S_n. apply H.
   intros. rewrite <- H0. apply index_proof_indep.
Qed.

Theorem index_appear_equiv : forall (X:Type) (l:list X) x, 
 appears_in x l <-> (exists n, exists pf, index_strong n l pf = x).
Proof. split;intros. apply index_appear_equiv' in H.
 destruct H as [witness]. exists witness. destruct H. exists H. apply H0.
 destruct H as [witness]. destruct H. apply index_appear_equiv'.
 exists witness. split. assumption. intros.
 rewrite <- H. apply index_proof_indep.
Qed.

Theorem index_member_equiv : forall (X:Type) (l:list X) x, 
  (member x l -> { n:nat & {pf | index_strong n l pf = x}}) *
  ({ n:nat & {pf | index_strong n l pf = x}} -> member x l).
Proof. split;intros. apply index_member_equiv' in X0.
 destruct X0. exists x0. destruct a. exists H. apply H0.
 destruct H. destruct s. apply index_member_equiv'.
 exists x0. split. assumption. intros.
 rewrite <- e. apply index_proof_indep.
Qed.

Lemma split_by_index : forall X (l:list X) n pfn, 
 { ll:list X & { lr:list X & (
 (l = ll ++ ((index_strong n l pfn) :: lr)) *
 (forall n' pfn', n' < n -> { m:nat & { pfm | 
    index_strong m ll pfm = index_strong n' l pfn'}}) *
 (forall n' pfn', n < n' -> { m:nat & { pfm | 
    index_strong m lr pfm = index_strong n' l pfn'}}))%type }}.
Proof. induction l as [|x l];intros. exfalso. inversion pfn.
 destruct n. exists []. exists l. repeat split;intros.
 exfalso. inversion H. destruct n'. exfalso. inversion H.
 exists n'. eexists. simpl. apply index_proof_indep.
 assert (n < length l). apply le_S_n. apply pfn.
 destruct (IHl n H). destruct s. destruct p.
 destruct p. exists (x::x0). exists x1.
 repeat split;intros. simpl. rewrite e at 1. do 3 f_equal. 
 apply index_proof_indep.
 destruct n'. exists 0. eexists. auto.
 edestruct (s0 n'). apply le_S_n. assumption.
 destruct s1. exists (S x2). eexists. simpl.
 rewrite <- e0. apply index_proof_indep. destruct n'.
 exfalso. inversion H0. edestruct (s n'). apply le_S_n. assumption.
 destruct s1. exists x2. exists x3. simpl.
 rewrite e0. apply index_proof_indep.
Grab Existential Variables.
 apply le_S_n. apply pfn'. apply Le.le_n_S. apply x3.
 apply Le.le_n_S. apply Le.le_0_n. apply le_S_n. apply pfn'.
Qed.

Lemma le_lt_eq : forall n m, sum (n < m) 
 (sum (m < n) (n = m)).
Proof. intros. destruct (Compare_dec.le_lt_dec n m).
destruct (Compare_dec.le_lt_eq_dec n m l). auto. auto. auto. Defined.

Theorem index_in_app_left : forall (X:Type) (ll lr:list X) x,
{ m:nat & {pfm | index_strong m ll pfm = x}} ->
{ m:nat & {pfm | index_strong m (ll++lr) pfm = x}}.
Proof. induction ll as [|x ll];intros.
 destruct H. destruct s. exfalso. inversion x1.
 destruct H. destruct s. destruct x1. exists 0. eexists. apply e.
 destruct (IHll lr x0). exists x1. eexists. simpl in e. apply e.
 destruct s. exists (S x3). eexists. simpl. rewrite <- e0.
 apply index_proof_indep.
Grab Existential Variables. 
 apply Le.le_n_S. apply x4.
 apply Le.le_n_S. apply Le.le_0_n.
Qed.

Theorem index_in_app_right : forall (X:Type) (ll lr:list X) x,
{ m:nat & {pfm | index_strong m lr pfm = x}} ->
{ m:nat & {pfm | index_strong m (ll++lr) pfm = x}}.
Proof. induction ll as [|x ll];intros. destruct H. destruct s.
 exists x0. exists x1. apply e.
 destruct H. destruct s. destruct (IHll lr x0).
 exists x1. exists x2. apply e. destruct s.
 exists (S x3). eexists. rewrite <- e0. simpl. apply index_proof_indep.
Grab Existential Variables.
 apply Le.le_n_S. apply x4.
Qed.

Theorem app_length_cons: forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
       length (l1 ++ x :: l2) = n -> S (length (l1 ++ l2)) = n.
Proof. induction l1;intros. apply H. destruct n. inversion H.
 f_equal. eapply IHl1. inversion H. reflexivity. Qed.

Theorem pigeonhole_principle_idx: forall (X:Type) (l1  l2:list X), 
   (forall n pfn, {m:nat & {pfm | 
       index_strong m l2 pfm = index_strong n l1 pfn}}) ->
   length l2 < length l1 -> 
   repeats l1.
Proof. induction l1 as [|x l1];intros. inversion H0.
assert (0 < length (x::l1)). simpl. apply Le.le_n_S. apply Le.le_0_n.
 destruct (H 0 H1). destruct s. simpl in e.
assert (forall (n:nat) (pfn:n < length l1), 
 {m: nat & {pfm | index_strong m l2 pfm = index_strong n l1 pfn}}).
intros. destruct (H (S n) (Le.le_n_S _ _ pfn)). destruct s.
exists x2. exists x3. simpl in e0. eapply eq_trans. apply e0.
apply index_proof_indep.
assert (TT := listsearch _ _ _ x0 H2).
 destruct TT.
  destruct s. destruct s. destruct (H2 x2 x3). simpl in e0.
  destruct s. subst. constructor.
  apply index_appear_equiv. exists x2. exists x3. eapply eq_trans.
  symmetry. apply e1. apply index_proof_indep. apply rep_step.
 destruct (split_by_index X l2 x0 x1) as [l2l [l2r [[Heq Hll] Hlr]]].
apply (IHl1 (l2l++l2r)); intros. 
 destruct (le_lt_eq (projT1 (H2 n0 pfn)) x0).
  destruct (H2 n0 pfn). destruct s. simpl in l. 
  destruct (Hll x2 x3 l). destruct s. apply index_in_app_left.
  exists x4. exists x5. eapply eq_trans;eassumption.
  destruct s. destruct (H2 n0 pfn). destruct s. simpl in l.
  destruct (Hlr x2 x3 l). destruct s. apply index_in_app_right.
  exists x4. exists x5. eapply eq_trans;eassumption.
  specialize (n n0 pfn). contradiction.
 symmetry in Heq. assert ((S (length (l2l ++ l2r))) = (length l2)).
  eapply app_length_cons. f_equal. apply Heq. unfold lt.
  rewrite H3. apply le_S_n. assumption.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
   (forall x, member x l1 -> member x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
 intros. apply pigeonhole_principle_idx with (l2:=l2);intros.
 apply index_member_equiv.
 apply X0.
 apply index_member_equiv.
 exists n. exists pfn.
 reflexivity.
 assumption.
Qed.

Print Assumptions pigeonhole_principle.