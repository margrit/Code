(*Quelle: https://github.com/wjzz/PumpingLemma/blob/master/Dfa.v*)

(* In this file we try to formalize some notions from the 
   formal languages field, precisely 
   Deterministic Finite-State Automata.
 *)

Load Definitions.
Section Transitions.

Fixpoint word_replicate (n : nat) (l : list Sigma) : list Sigma :=
  match n with
  | O    => nil
  | S n' => l ++ word_replicate n' l
  end.

(* Wenn es eine Schleife im Automaten gibt, kann man diese nutzen,
um das Wort aufzublähen an dieser Stelle und bleibt im gleichen Zustand. *)
Theorem ext_loop: forall n : nat, forall q : Q, forall xs : list Sigma,
  ext q xs = q -> ext q (word_replicate n xs) = q.
Proof.
  induction n as [|n'].
  - intros q xs H.
    simpl.
    reflexivity.
  (* n = S n; *)
  - intros q xs H.
    simpl.
    rewrite ext_app.
    rewrite H.
    apply IHn'.
    assumption.
Qed.

Fixpoint inits {X : Type} (l : list X) : list (list X) :=
  match l with
  | nil       => nil :: nil
  | x :: xs => nil :: map (cons x) (inits xs)
  end.

Eval compute in (inits (1 :: 2 :: nil)).
Eval compute in (inits nil : list (list nat)).

Theorem inits_len : forall X : Type, forall l : list X,
  length (inits l) = S (length l).
Proof.
  induction l.
  - simpl.
    reflexivity.
  (* l = cons _ _ *)
  - simpl.
    rewrite map_length.
    congruence.
Qed.

Theorem inits_dec_1 :
  forall X : Type,
  forall l : list X,
  forall y : list X, 
  forall xs ys : list (list X),
   inits l = xs ++ (y :: ys) ->
    exists zs : list X, l = y ++ zs.
Proof.
  intros X l.
  induction l as [|h l'].
  (* l ist nil *)
  - intros y xs ys H.
    (* y muss nil sein *)
    simpl in H.
    assert (xs = nil) as Hxs.
    + destruct xs.
      * { reflexivity. }
      * { destruct xs.
          - simpl in H.
            inversion H.
          - simpl in H.
            inversion H.
        }
    + subst xs.
      simpl in H.
      inversion H.
      exists nil.
      simpl.
      reflexivity.
  (* l ist h :: l' *)
  - intros y xs ys H.
    simpl in H.
    destruct xs.
    + simpl in H.
      inversion H.
      exists (h :: l').
      simpl.
      reflexivity.
    + simpl in H.
      inversion H.
      apply map_dec_2 in H2.
      destruct H2 as [xss].
      destruct H0 as [yss].
      destruct H0.
      destruct H2.
      destruct yss as [|y0 yss].
      * { inversion H3. }
      * { simpl in H3.
          apply IHl' in H0.
          destruct H0 as [zs].
          inversion H3.
          simpl.
          exists zs.
          subst.
          reflexivity.
        }
Qed.

Theorem inits_dec_2 :
  forall X : Type,
  forall l : list X,
  forall y z : list X,
  forall xs ys zs : list (list X),
   inits l = xs ++ (y :: ys) ++ (z :: zs) ->
    exists ds : list X, z = y ++ ds /\ length ds > 0.
Proof.
  intros X l.
  induction l as [|h l'].
  - intros y z xs ys zs H.
  (* Impossible case, inits nil has 1 elem,
     the list on RHO has >= 2 elems *)
    destruct xs.
    + simpl in H.
      inversion H.
      subst y.
      simpl in *.
      inversion H.
      destruct ys.
      * { simpl in *.
          inversion H1.
        }
      * { simpl in *.
          inversion H1.
        }
    + simpl in *.
      inversion H.
      subst l.
      inversion H.
      destruct xs.
      * { simpl in *.
          inversion H2.
        }
      * { simpl in *.
          inversion H1.
        }
  (* l = h :: l' *)
  (* we need more info *)
  - destruct l' as [|h' ls].
    + intros y z xs ys zs H.
      simpl in *.
      destruct xs.
      * { simpl in *.
          inversion H.
          subst y.
          inversion H.
          destruct ys.
          - simpl in *.
            inversion H1.
            exists (h :: nil).
            split.
            + reflexivity.
            + simpl.
               unfold gt.
               unfold lt.
               apply le_n.
          - inversion H1.
            simpl in *.
            clear H2.
            clear H.
            destruct ys.
            * { simpl in *.
                inversion H4.
              }
            * { simpl in *.
                inversion H4.
              } }
      * { inversion H.
          destruct xs.
          - simpl in *.
            inversion H2.
            destruct ys.
            + simpl in *.
              inversion H4.
            + simpl in *.
              inversion H4.
          - inversion H2.
            destruct xs.
            + simpl in H4.
              inversion H4.
            + simpl in H4.
              inversion H4.
        }
    (* l = h :: h' :: ls *)
    (* finally we can use the ind. hyp. *)
    + intros y z xs ys zs H.
      remember (h' :: ls) as l.
      simpl in *.
      destruct xs.
      * { simpl in *.
          inversion H.
          exists z.
          split.
          - simpl.
          reflexivity.
          - apply map_dec_2 in H2.
            destruct H2 as [xss].
            destruct H0 as [yss].
            destruct H0.
            destruct H2.
            destruct yss.
            + simpl in *.
              inversion H3.
            + simpl in *.
              inversion H3.
              simpl.
              unfold gt.
              unfold lt.
              apply le_n_S.
              apply le_0_n.
        }
      * { simpl in *.
          inversion H.
          subst l0. 
          clear H.
          assert (map (cons h) (inits l) = xs ++ (y :: ys) ++ (z :: zs)).
          - simpl.
            assumption.
          - apply map_dec_3 in H.
            destruct H as [xss].
            destruct H as [yss].
            destruct H as [zss].
            destruct H.
            destruct H0.
            destruct H1.
            destruct yss.
            + simpl in *.
              inversion H1.
            + simpl in *.
              inversion H1.
              destruct zss.
              * { simpl in *.
                  inversion H3.
                }
              * { simpl in *.
                  inversion H3.
                  apply IHl' in H.
                  destruct H as [ds].
                  destruct H.
                  exists ds.
                  split.
                  - subst.
                    reflexivity.
                  - assumption.
                } }
Qed.

Theorem inits_dec : 
  forall X : Type, 
  forall l : list X,
  forall b c : list X, 
  forall ass bs cs : list (list X),
  inits l = ass ++ (b :: bs) ++ (c :: cs) ->
  (exists ds : list X, c = b ++ ds /\ length ds > 0) /\
  exists es : list X, l = c ++ es.
Proof.
  intros X l b c ass bs cs H.
  remember H as H2. (* H : inits l = ass ++ (b :: bs) ++ c :: cs *)
  clear HeqH2.
  apply inits_dec_2 in H.
  destruct H as [ds].
  split.
  - exists ds.
    destruct H.
    split.
    + apply H.
    + apply H0.
  - rewrite app_assoc in H2.
  eapply inits_dec_1.
  apply H2. (*Warum das geht ist mir ein wenig schleierhaft - wahrscheinlich weil die 
                  erste Klammer als eine Liste aufgefasst wird.*)
Qed.

Definition prefixes (q : Q) (l : list Sigma) : list Q :=
  map (ext q) (inits l).

Lemma prefixes_len : forall l : list Sigma, forall q : Q,
  length (prefixes q l) = S (length l).
Proof.
  intros.
  unfold prefixes.
  rewrite map_length.
  rewrite inits_len.
  reflexivity.
Qed.

(* Dieses Axiom beschreibt das Pigeohole Principle *)
Axiom states_size: forall l: list Q, length l > Q_size ->
  repeats l.

(* Pumping Lemma: *)
Theorem pumping_lemma : forall w : list Sigma,
  accepted_word w -> Q_size <= length w ->
  exists xs : list Sigma,
  exists ys : list Sigma,
  exists zs : list Sigma,
  length ys > 0 /\
 (* length ys < Q_size -> *)
  w = xs ++ ys ++ zs /\
  forall n : nat,
  accepted_word (xs ++ (word_replicate n ys) ++ zs).
Proof.
  intros w acc len_w.
  (* Let's look at which state the DFA is after reading
  epsilon, w0, w0w1, .. w. *)
  set (pref := prefixes q0 w).
  assert (Hpref : Q_size < length pref).
  - unfold pref.
    rewrite prefixes_len.
    unfold lt.
    apply le_n_S.
    apply len_w.
  - assert (HRep : repeats pref).
    + apply states_size.
      apply Hpref.
    + set (Hx := repeats_decomp Q pref HRep).
      destruct Hx.
      destruct H.
      destruct H.
      destruct H.
      unfold pref in H.
      unfold prefixes in H.
      set (Hx := map_dec_3 (list Sigma) Q (ext q0)
      (inits w) x0 (x :: x1) (x :: x2) H).
      destruct Hx.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      destruct H2.
      (* x4 und x5 können nicht nil sein *)
      destruct x4 as [|y x4].
      * { inversion H2. }
      * { destruct x5 as [|y2 x5].
          - inversion H3.
          - set (Hx := inits_dec _ w y y2 x3 x4 x5 H0).
            destruct Hx.
            destruct H4.
            destruct H5.
            destruct  H4.
            exists y.
            exists x6.
            exists x7.
            split.
            + apply H6.
            + split.
              * { subst y2.
                  rewrite H5.
                  rewrite app_assoc.
                  reflexivity.
                }
              * { unfold accepted_word in *.
                  intros n.
                  assert (ext q0 (y ++ (word_replicate n x6) ++ x7) = ext q0 w).
                  - rewrite ext_app.
                    rewrite ext_app.
                    simpl in H2.
                    inversion H2.
                    simpl in H3.
                    inversion H3.
                    assert (ext (ext q0 y) x6 = ext q0 y).
                    + pattern (ext q0 y) at 2.
                      rewrite H8.
                      rewrite <- H10.
                      rewrite H4.
                      rewrite ext_app.
                      reflexivity.
                    + rewrite ext_loop.
                       rewrite H5.
                       rewrite ext_app.
                       congruence.
                       rewrite H7.
                       reflexivity.
                  - rewrite H7.
                    apply acc.
                } }
Qed.