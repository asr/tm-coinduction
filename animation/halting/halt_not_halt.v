
(* First half of the proof:
   supposing that Witness halts leads to absurd
*)

Lemma witness_stops_absurd:
      halt witness (gamma witness) -> False.
unfold halt; intro.
elim H; clear H. intro t; intro.

cut (bi witness (pair Bs (app_ls (ones (S (gamma witness))) Bs)) 0).
intro. apply bf_not_bi with
       witness (pair Bs (app_ls (ones (S (gamma witness))) Bs))
       0 t (max_source witness 0 + 1).
assumption. assumption.
unfold witness at 1.

(* First decomposition *)

apply join_loop with 
      (pair Bs (app_ls (ones (S (gamma witness)))
                       (Cons B (app_ls (ones (S (gamma witness))) Bs))))
      7.

(* Copy machine *)

apply Copy_stops.

(* Second decomposition *)

apply join_loop with (pair Bs (Cons one Bs))
                     (max_source HM 0 + 8).

(* HM machine *)

change 7 with (7+0) at 2.
change 8 with (7+1). rewrite (plus_comm 7 1). 
rewrite plus_assoc. rewrite (plus_comm (max_source HM 0 + 1) 7).
apply shift_preserves_stop. apply HM_decides_stop.
unfold halt. exists t. assumption.
clear H t.

(* Dither machine *)

change (max_source HM 0 + 8) with (0 + (max_source HM 0 + 8)) at 2. 
rewrite (plus_comm 0 (max_source HM 0 + 8)). apply shift_preserves_loop.
apply Dither_loops.

(* join condition: 1st check
*)

clear H t; unfold not, Dither. simpl; intros. 

assert (i <= (max_source HM 0)+7).
apply shift_maxsource. assumption.
omega.

(* 2nd check
*)

clear H t; unfold not, Dither. simpl; intros.

assert (i >= 7 \/ In i (proj_target 
       ((max_source HM 0 + 8 + 0, one, max_source HM 0 + 8 + 1, R)
          :: (max_source HM 0 + 8 + 1, B, max_source HM 0 + 8 + 0, L)
             :: (max_source HM 0 + 8 + 1, one, max_source HM 0 + 8 + 2, L)
                :: nil))).
apply app_shift with HM. assumption.
clear H; simpl in H1. omega.
Qed.