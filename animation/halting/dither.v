
(**************** DITHER Machine ***************)

(*
Implementation: 0 1 -> 1 R
                1 B -> 0 L
                1 1 -> 2 L
*)

Definition Dither: Spec := (0, one, 1, R) :: 
                           (1, B  , 0, L) :: 
                           (1, one, 2, L) :: nil.

(************************ Divergence proof ************************)

Lemma Dither_loops:
      bi Dither (pair Bs (Cons one Bs)) 0.
cofix co_hp; apply biR with 1; auto; simpl.
apply biL with 0; auto.
Qed.

(************************ Convergence proof ************************)

Lemma Dither_stops:
      bf Dither (pair Bs (Cons one (Cons one Bs))) 0
                (pair Bs (Cons one (Cons one Bs))) 2.
apply bfR with 1; auto; simpl.
apply bfL with 2; auto; simpl.
apply bfH; unfold is_value; auto.
Qed.