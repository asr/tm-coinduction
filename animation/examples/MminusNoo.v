
Require Import List Omega.

Require Import bigstep.
Require Import coinduction.
Require Import datatypes.
Require Import Ndiv2oo.
Require Import streams_vs_lists.

(* Function pminus(m,n) = m-n       if m>=n
                          undefined otherwise

   Example machine: 1 1 -> 1 R
                    1 B -> 2 R
                    2 0 -> 2 R
                    2 1 -> 3 0
                    3 0 -> 3 L
                    3 B -> 4 L
                    4 B -> 4 L
                    4 1 -> 5 B
                    5 B -> 5 R
                    5 0 -> 2 R
*)

Definition pminus: Spec := (1,  one, 1,      R) ::
                           (1,  B  , 2,      R) ::
                           (2, zero, 2,      R) ::
                           (2,  one, 3, W zero) ::
                           (3, zero, 3,      L) ::
                           (3,    B, 4,      L) ::
                           (4,    B, 4,      L) ::
                           (4,  one, 5,    W B) ::
                           (5,    B, 5,      R) ::
                           (5, zero, 2,      R) :: nil.

(************************ Auxiliary objects and properties  ***************)

Lemma ones_comm: forall n l,
      (app_ls (ones n) (Cons one l)) = (Cons one (app_ls (ones n) l)).
induction n; simpl; intros.
reflexivity.
rewrite IHn. reflexivity.
Qed.

Fixpoint blanks (n:nat) {struct n}: list Sym :=
         match n with
         | 0 => nil
         | (S m) => (cons B (blanks m))
         end.

Lemma blanks_step: forall l,
      (Cons B l) = (app_ls (blanks 1) l).
simpl. reflexivity.
Qed.

Fixpoint zeros (n:nat) {struct n}: list Sym :=
         match n with
         | 0 => nil
         | (S m) => (cons zero (zeros m))
         end.

Lemma zeros_step: forall l,
      (Cons zero l) = (app_ls (zeros 1) l).
simpl. reflexivity.
Qed.

Lemma blanks_comm: forall n l,
      (app_ls (blanks n) (Cons B l)) = (app_ls (blanks (S n)) l).
induction n; simpl; intros.
reflexivity.
rewrite IHn. simpl. reflexivity.
Qed.

Lemma zeros_comm: forall n l,
      (app_ls (zeros n) (Cons zero l)) = (app_ls (zeros (S n)) l).
induction n; simpl; intros.
reflexivity.
rewrite IHn. simpl. reflexivity.
Qed.

(************************ Divergence proof ************************)

(*
move to R till to the first "1" of n, going into state 2
*)
Lemma pminus_move_from1: forall m l r,
      bi pminus (pair (Cons B (app_ls (ones (S m)) l)) r) 2 ->
      bi pminus (pair l (app_ls (ones (S m)) (Cons B r))) 1.
induction m; simpl; intros.
apply biR with 1.
auto.
simpl. apply biR with 2.
auto.
simpl. assumption.
apply biR with 1.
auto.
simpl. apply IHm.
rewrite ones_comm. assumption.
Qed.

(*
mandatory transitions from state 2 to 5, to erase a "1" for both m ed n
*)
Lemma pminus_1stcycle_from2: forall l r,
      bi pminus (pair (Cons B (Cons B l)) (Cons zero r)) 5 ->
      bi pminus (pair (Cons B (Cons one l)) (Cons one r)) 2.
intros. apply biW with 3 zero.
auto.
simpl. apply biL with 3.
auto.
simpl. apply biL with 4.
auto.
simpl. apply biW with 5 B.
auto.
simpl. apply biR with 5.
auto.
simpl. apply biR with 5.
auto.
simpl. assumption.
Qed.

(*
loop from the state 4, if Bs on the left and reading a B
*)
Lemma pminus_loops_4_Bs_B: forall r,
      bi pminus (pair Bs (Cons B r)) 4.
cofix co_hp.
intro. apply biL with 4.
auto.
simpl. apply co_hp.
Qed.

Lemma pminus_loops_aux_2to2: forall k l r,
      bi pminus (pair (app_ls (zeros k) l) (Cons one r)) 2 ->
      bi pminus (pair l (app_ls (zeros k) (Cons one r))) 2.
induction k; simpl; intros.
assumption.
apply biR with 2.
auto. simpl. apply IHk.
rewrite zeros_comm. simpl. assumption.
Qed.

Lemma pminus_loops_aux_3to3: forall k l r,
      bi pminus (pair l (Cons zero (app_ls (zeros k) (Cons zero r)))) 3 ->
      bi pminus (pair (app_ls (zeros k) (Cons zero l)) (Cons zero r)) 3.
induction k; simpl; intros.
apply biL with 3.
auto. simpl. assumption.
apply biL with 3.
auto. simpl. apply IHk.
rewrite zeros_comm. simpl. assumption.
Qed.

Lemma pminus_loops_aux_5to3: forall k l r,
      bi pminus (pair l (Cons zero (app_ls (zeros k)
                        (Cons zero r)))) 3 ->
      bi pminus (pair l (Cons zero (app_ls (zeros k)
                        (Cons one r)))) 5.
intros. apply biR with 2.
auto.
simpl.
apply pminus_loops_aux_2to2.
apply biW with 3 zero.
auto. simpl.
apply pminus_loops_aux_3to3. assumption.
Qed.

Lemma pminus_loops_aux_4to4: forall k l r,
      bi pminus (pair l (app_ls (blanks k) (Cons B r))) 4 ->
      bi pminus (pair (app_ls (blanks k) l) (Cons B r)) 4.
induction k; simpl; intros.
assumption.
apply biL with 4.
auto. simpl.
apply IHk.
rewrite blanks_comm. simpl. assumption.
Qed.

Lemma pminus_loops_aux_5to5: forall k l r,
      bi pminus (pair (app_ls (blanks k) l) r) 5 ->
      bi pminus (pair l (app_ls (blanks k) r)) 5.
induction k; simpl; intros.
assumption.
apply biR with 5.
auto. simpl.
apply IHk.
rewrite blanks_comm. simpl. assumption.
Qed.

Lemma pminus_loops_aux_3to5: forall k l r,
      bi pminus (pair (Cons B (Cons B (app_ls (blanks k)
                              (Cons B l))))
                      (Cons zero r)) 5 ->
      bi pminus (pair (Cons B (Cons B (app_ls (blanks k)
                              (Cons one l))))
                      (Cons zero r)) 3.
intros. apply biL with 3.
auto. simpl. apply biL with 4.
auto. simpl.
apply pminus_loops_aux_4to4.
rewrite blanks_comm. simpl.
apply biL with 4.
auto. simpl. apply biW with 5 B.
auto. simpl.
rewrite blanks_comm. simpl.
rewrite blanks_comm in H. simpl in H.
assert (forall l,
       (Cons B (Cons B (Cons B (app_ls (blanks k) l)))) =
       (app_ls (blanks (S (S (S k)))) l)).
simpl. reflexivity.
rewrite (H0 (Cons zero r)). rewrite (H0 l) in H. clear H0.
apply pminus_loops_aux_5to5. assumption.
Qed.

Lemma pminus_loops_5_B_0: forall n m k r,
      m < n ->
      bi pminus (pair (app_ls (blanks (S (S k))) (app_ls (ones m) Bs))
                      (app_ls (zeros (S k)) (app_ls (ones n) r)))
                5.
double induction n m; simpl; intros.

(* m=n=0 *)

omega.

(* m=p+1, n=0 *)

omega.

(* m=0, n=p+1 *)
clear H H0.
apply pminus_loops_aux_5to3.
apply biL with 3.
auto. simpl. apply biL with 4.
auto. simpl.
apply pminus_loops_aux_4to4.
rewrite blanks_comm. simpl. apply pminus_loops_4_Bs_B.

(* m=q+1, n=p+1 *)
clear H. apply pminus_loops_aux_5to3.
apply pminus_loops_aux_3to5.
rewrite blanks_comm. rewrite zeros_comm.
apply H0. omega.
Qed.

Lemma pminus_loops: forall n m,
      m < n ->
      bi pminus (pair Bs (app_ls (ones (S m))
                                 (Cons B (app_ls (ones (S n)) Bs)))) 1.
intros.
apply pminus_move_from1.
simpl.
apply pminus_1stcycle_from2.

(* Here the discrimination between Divergence and Convergence starts *)
rewrite blanks_step, zeros_step. rewrite blanks_comm.

(*
core property: from state 5, in the end you reach state 4 and loop
*)
apply pminus_loops_5_B_0. assumption.
Qed.
