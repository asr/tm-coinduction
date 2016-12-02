
Require Import bigstep.
Require Import coinduction.
Require Import datatypes.
Require Import MminusNoo.
Require Import Ndiv2oo.
Require Import streams_vs_lists.
Require Import UndefNoo.

(* Function undef(n) = undefined for any n

   Example machine:
      1 1 -> 1 R
      1 B -> 2 1
      2 1 -> 2 L
      2 B -> 1 1

Definition undef: Spec := (1, one, 1,     R) ::
                          (1, B  , 2, W one) ::
                          (2, one, 2,     L) ::
                          (2, B  , 1, W one) :: nil.
*)

(****************** Unuarded Divergence, via BI *********************)

Lemma undef_loops_unguarded: forall n,
      bi undef (pair Bs (app_ls (ones (S n)) Bs)) 1.
cofix co_hp.
intro.

Lemma undef_scan_right2: forall m l,
      bi undef (pair (app_ls (ones m) l) (Cons one Bs)) 2 ->
      bi undef (pair l (app_ls (ones m) Bs)) 1.
induction m; simpl; intros.

apply biW with 2 one.
auto. simpl. assumption.

apply biR with 1.
auto. simpl.
apply IHm.
rewrite ones_comm. assumption.
Qed.

apply undef_scan_right2.

Lemma undef_scan_left2: forall m r,
      bi undef (pair Bs (app_ls (ones (S (S m))) r)) 1 ->
      bi undef (pair (app_ls (ones m) Bs) (Cons one r)) 2.
induction m; simpl; intros.

apply biL with 2.
auto. simpl.
apply biW with 1 one.
auto. simpl. assumption.

apply biL with 2.
auto. simpl.
apply IHm.
rewrite ones_comm. do 2 rewrite <- ones_step2. assumption.
Qed.

apply undef_scan_left2.
apply co_hp.

(* The proof is not accepted by Coq (try to apply Qed.)
Qed.
*)

Abort.
