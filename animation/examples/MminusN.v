
Require Import Omega.

Require Import big_vs_small.
Require Import bigstep.
Require Import coinduction.
Require Import datatypes.
Require Import MminusNoo.
Require Import Ndiv2oo.
Require Import smallstep.
Require Import streams_vs_lists.
Require Import UndefNoo.

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
*)

(************************ Auxiliary objects and properties  ***************)

Lemma zeros_comm2: forall n l,
      (app_ls (zeros n) (Cons zero l)) = (Cons zero (app_ls (zeros n) l)).
induction n; simpl; intros.
reflexivity.
rewrite IHn. reflexivity.
Qed.

Lemma blanks_comm2: forall n l,
      (app_ls (blanks n) (Cons B l)) = (Cons B (app_ls (blanks n) l)).
induction n; simpl; intros.
reflexivity.
rewrite IHn. reflexivity.
Qed.

Lemma blanks_step2: forall n l,
      (Cons B (app_ls (blanks n) l)) = (app_ls (blanks (S n)) l).
simpl. reflexivity.
Qed.

Lemma zeros_step2: forall n l,
      (Cons zero (app_ls (zeros n) l)) = (app_ls (zeros (S n)) l).
simpl. reflexivity.
Qed.

(************************ Convergence proof ************************)

Lemma sf_1: forall m l r,
      sf pminus (pair l (app_ls (ones (S m)) (Cons B r))) 1
                (pair (Cons B (app_ls (ones (S m)) l)) r) 2.
induction m; simpl; intros.

apply sfI with 1 (pair (Cons one l) (Cons B r)).
apply s1R. auto.
apply sfI with 2 (pair (Cons B (Cons one l)) r).
apply s1R. auto.
apply sf0.

apply sfI with 1 (pair (Cons one l) (app_ls (ones (S m)) (Cons B r))).
apply s1R. auto.
rewrite <- ones_comm. replace (Cons one (app_ls (ones m) (Cons one l)))
                      with (app_ls (ones (S m)) (Cons one l)).
apply IHm. auto.
Qed.

Lemma pminus_stops_aux_2to2: forall k l,
      bf pminus (pair l (app_ls (zeros k) Bs)) 2
                (pair (app_ls (zeros k) l) Bs) 2.
induction k; simpl; intros.
apply bfH. unfold is_value. auto.
apply bfR with 2.
auto. simpl.
rewrite <- zeros_comm2. apply IHk.
Qed.

Lemma sf_2: forall k l r,
      sf pminus (pair l (app_ls (zeros k) r)) 2
                (pair (app_ls (zeros k) l) r) 2.
induction k; simpl; intros.
apply sf0.
apply sfI with 2 (pair (Cons zero l) (app_ls (zeros k) r)).
apply s1R. auto.
rewrite <- zeros_comm2. apply IHk.
Qed.

Lemma sf_3: forall k l r,
      sf pminus (pair (app_ls (zeros k) l) (Cons zero r)) 3
                (pair l (app_ls (zeros k) (Cons zero r))) 3.
induction k; simpl; intros.

apply sf0.

apply sfI with 3 (pair (app_ls (zeros k) l) (Cons zero (Cons zero r))).
apply s1L. auto.
rewrite <- zeros_comm2. apply IHk.
Qed.

Lemma sf_4: forall k l r,
      sf pminus (pair (app_ls (blanks k) l) (Cons B r)) 4
                (pair l (app_ls (blanks k) (Cons B r))) 4.
induction k; simpl; intros.

apply sf0.

apply sfI with 4 (pair (app_ls (blanks k) l) (Cons B (Cons B r))).
apply s1L. auto.
rewrite <- blanks_comm2. apply IHk.
Qed.

Lemma sf_5: forall k l r,
      sf pminus (pair l (app_ls (blanks k) r)) 5
                (pair (app_ls (blanks k) l) r) 5.
induction k; simpl; intros.

apply sf0.

apply sfI with 5 (pair (Cons B l) (app_ls (blanks k) r)).
apply s1R. auto.
rewrite <- blanks_comm2. apply IHk.
Qed.

(*
core property: from state 5, in the end you reach state 2 and stop
*)
Lemma pminus_stops_5_B_0: forall n m k,
      m >= n ->
      bf pminus (pair (app_ls (blanks (S (S k))) (app_ls (ones m) Bs))
                      (app_ls (zeros (S k)) (app_ls (ones n) Bs)))
                5
                (pair (app_ls (zeros (n+(S k)))
                              (app_ls (blanks (n+(S (S k))))
                              (app_ls (ones (minus m n)) Bs)))
                      Bs)
                2.
double induction n m; simpl; intros.

(* m=n=0 *)

apply bfR with 2.
auto. simpl.
rewrite <- zeros_comm2. apply pminus_stops_aux_2to2.

(* m=p+1, n=0 *)

clear H H0.
apply bfR with 2.
auto. simpl.
rewrite <- zeros_comm2. apply pminus_stops_aux_2to2.

(* m=0, n=p+1 *)

omega.

(* m=q+1, n=p+1 *)

clear H. apply bfR with 2.
auto. simpl.
apply sf_to_bf with
      (pair (app_ls (zeros k) (Cons zero (Cons B (Cons B
                    (app_ls (blanks k) (Cons one (app_ls (ones n0) Bs)))))))
            (Cons one (app_ls (ones n1) Bs))) 2.
apply sf_2.

apply bfW with 3 zero.
auto. simpl.
apply sf_to_bf with
      (pair (Cons zero (Cons B (Cons B (app_ls (blanks k)
                       (Cons one (app_ls (ones n0) Bs))))))
            (app_ls (zeros k) (Cons zero (app_ls (ones n1) Bs)))) 3.

apply sf_3.

rewrite zeros_comm2. apply bfL with 3.
auto. simpl. apply bfL with 3.
auto. simpl. apply bfL with 4.
auto. simpl.

apply sf_to_bf with
      (pair (Cons one (app_ls (ones n0) Bs))
            (app_ls (blanks k) (Cons B (Cons B (Cons zero
                    (Cons zero  (app_ls (zeros k)
                    (app_ls (ones n1) Bs)))))))) 4.

apply sf_4.

rewrite blanks_comm. rewrite blanks_comm. simpl.
apply bfL with 4.
auto. simpl. apply bfW with 5 B.
auto. simpl. apply bfR with 5.
auto. simpl. apply bfR with 5.
auto. simpl. apply bfR with 5.
auto. simpl.

apply sf_to_bf with
      (pair (app_ls (blanks k) (Cons B (Cons B (Cons B
                    (app_ls (ones n0) Bs)))))
            (Cons zero (Cons zero (app_ls (zeros k)
                   (app_ls (ones n1) Bs))))) 5.

apply sf_5.

do 3 rewrite blanks_comm. simpl.  rewrite blanks_step2.
rewrite zeros_step2. rewrite (zeros_step2 (n1 + S k)).
assert (S (n1 + S k) = (n1 + S (S k))). omega. rewrite H; clear H.
rewrite (blanks_step2 (n1 + S (S k))).
assert (S (n1 + S (S k)) = (n1 + S (S (S k)))). omega. rewrite H; clear H.
apply H0. omega.
Qed.

Lemma pminus_stops: forall n m,
      m >= n ->
      bf pminus (pair Bs (app_ls (ones (S m))
                                 (Cons B (app_ls (ones (S n)) Bs)))) 1
                (pair (app_ls (zeros (n+1)) (app_ls (blanks (n+2))
                      (app_ls (ones (m-n)) Bs))) Bs) 2.

(*
move from the starting state 1 after the B that separates m and n
*)
intros.
apply sf_to_bf with (pair (Cons B (app_ls (ones (S m)) Bs))
                          (app_ls (ones (S n)) Bs)) 2.
apply sf_1.

(*
mandatory transitions from state 2 to 5, to erase a "1" for both m ed n
*)
simpl. apply bfW with 3 zero.
auto. simpl. apply bfL with 3.
auto. simpl. apply bfL with 4.
auto. simpl. apply bfW with 5 B.
auto. simpl. apply bfR with 5.
auto. simpl. apply bfR with 5.
auto. simpl.

rewrite blanks_step. rewrite blanks_comm.
rewrite zeros_step.
apply pminus_stops_5_B_0. assumption.
Qed.
