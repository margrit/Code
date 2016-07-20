Require Import Vector.

(* Beipiel: 
   Eine Version von [insert_at] aus Pigeonhole_vector.v direkt definiert. *)

Fixpoint insert_at' {A : Type} {n : nat}  (v : t A n) (p: @Fin.t (S n))
                                     (a : A) : t A (S n) :=
  match p with
  | @Fin.F1 k        => fun v' => cons A a k v'
  | @Fin.FS 0     p' => fun v' => False_rect (t A (S 0)) (match p' with end)
  | @Fin.FS (S k) p' => fun v' => caseS' v' (fun _ => t A (S (S k)))
                                        (fun h t => 
                                          cons A h (S k) (insert_at' t p' a)) 
  end v.

Print insert_at'.

Eval compute in 
  (insert_at' (cons _ 1 _ (cons _ 2 _ (cons _ 3 _ (nil _)))) (Fin.FS Fin.F1) 5). 