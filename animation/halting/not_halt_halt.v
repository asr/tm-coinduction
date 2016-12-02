Require Import Arith List Omega.

Require Import coinduction.
Require Import copy.
Require Import datatypes.
Require Import dither.
Require Import halting_defs.
Require Import join.
Require Import Ndiv2oo.
Require Import shift.
Require Import shift_maxsource.
Require Import streams_vs_lists.
Require Import witness.

(* Second half of the proof:
   supposing that Witness does not halt leads to absurd
*)

Lemma witness_loops_absurd:
      ~halt witness (gamma witness) -> False.
intro. generalize H.
unfold halt; intro.
elim H0; clear H0.
exists (pair Bs (Cons one (Cons one Bs))).
unfold witness at 1.

(* First decomposition *)

apply join_stop with
      (pair Bs (app_ls (ones (S (gamma witness)))
                       (Cons B (app_ls (ones (S (gamma witness))) Bs))))
      7.

(* Copy machine *)

apply Copy_stops.

(* Second decomposition *)

apply join_stop with (pair Bs (Cons one (Cons one Bs)))
                     (max_source HM 0 + 8).

(* HM machine *)

change 7 with (7+0) at 2.
change 8 with (7+1). rewrite (plus_comm 7 1).
rewrite plus_assoc. rewrite (plus_comm (max_source HM 0 + 1) 7).
apply shift_preserves_stop. apply HM_decides_loop.
assumption.
clear H.

(* Dither machine *)

rewrite max_source_HM_witness.
change 9 with (8+1). rewrite plus_assoc.
rewrite <- plus_assoc. change (1+1) with 2.
change (max_source HM 0 + 8) with (0 + (max_source HM 0 + 8)) at 2.
rewrite (plus_comm 0 (max_source HM 0 + 8)).
apply shift_preserves_stop. apply Dither_stops.

(* join condition: 1st check
*)

clear H; unfold not, Dither. simpl; intros.

assert (i <= (max_source HM 0)+7).
apply shift_maxsource. assumption.
omega.

(* 2nd check
*)

clear H; unfold not, Dither. simpl; intros.

assert (i >= 7 \/ In i (proj_target
       ((max_source HM 0 + 8 + 0, one, max_source HM 0 + 8 + 1, R)
          :: (max_source HM 0 + 8 + 1, B, max_source HM 0 + 8 + 0, L)
             :: (max_source HM 0 + 8 + 1, one, max_source HM 0 + 8 + 2, L)
                :: nil))).
apply app_shift with HM. assumption.
clear H; simpl in H1. omega.
Qed.
