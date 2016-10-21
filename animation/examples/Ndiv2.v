
(* Function div2(n) = n/2       if n is even
                      undefined otherwise

   Example machine:
      1 1 -> 1 B
      1 B -> 2 R
      2 1 -> 3 R
      3 B -> 3 R
      3 1 -> 4 B
      4 B -> 2 R

Definition div2: Spec := (1, one, W B, 1) :: 
                         (1, B  ,   R, 2) :: 
                         (2, one,   R, 3) :: 
                         (3, B  ,   R, 3) :: 
                         (3, one, W B, 4) :: 
                         (4, B  ,   R, 2) :: nil.
*)

(************************ Convergence proof ************************)

Fixpoint repeat (n:nat): list Sym :=
         match n with
         | 0 => nil
         | (S m) => (cons B (cons one (repeat m)))
         end.

Lemma repeat_comm: forall n l,
      (Cons B (Cons one (app_ls (repeat n) l))) =
      (app_ls (repeat n) (Cons B (Cons one l))).
induction n.
simpl. reflexivity.
simpl. intro. rewrite <- IHn. reflexivity.
Qed. 

(*
cycle from the state 2, if an even number of ones
*)

Lemma div2_stops_2even: forall n l,
      bf div2 (pair l
                    (app_ls (ones (2*n)) Bs)) 2
              (pair (app_ls (repeat n) l)
                    Bs)                       2.
induction n.

simpl. intro. apply bfH.
unfold is_value. auto.

simpl. intro. apply bfR with 3.
auto.
simpl. replace (n + S (n + 0)) with (S (2*n)).
simpl. apply bfW with 4 B.
auto.
simpl. apply bfR with 2.
auto.
simpl. replace (n + (n + 0)) with (2*n).
rewrite repeat_comm. apply IHn.
omega. omega.
Qed.

(*
stop from the starting state 1
*)

Lemma div2_stops: forall n,
      bf div2 (pair Bs
                    (Cons one (app_ls (ones (2*n)) Bs))) 1
              (pair (app_ls (repeat n) (Cons B Bs))
                    Bs)                                  2.
intros. apply bfW with 1 B.
auto.
simpl. apply bfR with 2.
auto.
simpl. replace (n + (n + 0)) with (2*n). apply div2_stops_2even.
omega.
Qed.