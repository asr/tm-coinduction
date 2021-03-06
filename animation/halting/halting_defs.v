
Require Import bigstep.
Require Import coinduction.
Require Import datatypes.
Require Import Ndiv2oo.
Require Import shift_maxsource.
Require Import streams_vs_lists.

(*********** Definition of the HALTING PROBLEM ***********)

Definition halt (T:Spec) (n:nat) := exists t:Tape,
           bf T (pair Bs (app_ls (ones (S n)) Bs)) 0
                t                                  (max_source T 0 + 1).

(*
Assumptions: coding function, halting machine
*)

Parameter gamma: Spec -> nat.

Parameter HM: Spec.

(*
Assumption: H can decide the halting
*)

Parameter HM_decides_stop: forall T:Spec, forall n:nat,
          halt T n ->
          bf HM (pair Bs (app_ls (ones (S (gamma T)))
                                 (Cons B (app_ls (ones (S n)) Bs))))
                0
                (pair Bs (Cons one Bs))
                (max_source HM 0 + 1).

Parameter HM_decides_loop: forall T:Spec, forall n:nat,
          ~halt T n ->
          bf HM (pair Bs (app_ls (ones (S (gamma T)))
                                 (Cons B (app_ls (ones (S n)) Bs))))
                0
                (pair Bs (Cons one (Cons one Bs)))
                (max_source HM 0 + 1).
