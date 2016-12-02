
(**************** COPY Machine ***************)

Definition Copy: Spec := (0, one , 0, W zero) ::
                         (0, zero, 1,      R) ::
                         (1, one , 1,      R) ::
                         (1, B   , 2,      R) ::
                         (2, one , 2,      R) ::
                         (2, B   , 3,  W one) ::
                         (3, one , 3,      L) ::
                         (3, B   , 4,      L) ::
                         (4, one , 5,      L) ::
                         (4, zero, 6,  W one) ::
                         (5, one , 5,      L) ::
                         (5, zero, 0,      R) ::
                         (6, one , 6,      L) ::
                         (6, zero, 6,  W one) ::
                         (6, B   , 7,      R) :: nil.

(**************** LOOP part *********************************************)

Lemma Copy_loop_5L_sf: forall n l r,
      sf Copy (pair ((app_ls (ones n) (Cons zero l)))
                    (Cons one r))
              4
              (pair l
                    (Cons zero (app_ls (ones (S n)) r)))
              5.
destruct n; intros.

simpl. apply sfI with 5 (pair l (Cons zero (Cons one r))).
apply s1L. auto. apply sf0.

apply sfI with 5 (pair (app_ls (ones n) (Cons zero l))
                       (Cons one (Cons one r))).
apply s1L. auto.

generalize n l r; clear n l r.
induction n; intros.

simpl. apply sfI with 5 (pair l (Cons zero (Cons one (Cons one r)))).
apply s1L. auto. apply sf0.

apply sfI with 5 (pair (app_ls (ones n) (Cons zero l))
                       (Cons one (Cons one (Cons one r)))).
apply s1L. auto.
assert (app_ls (ones (S (S (S n)))) r =
       (app_ls (ones (S (S n))) (Cons one r))).
simpl. rewrite ones_comm. reflexivity.
rewrite H; clear H. apply IHn.
Qed.

Lemma Copy_loop_1and2R_sf: forall n l r p,
      p = 1 \/ p = 2 ->
      sf Copy (pair l (app_ls (ones n) r)) p
              (pair (app_ls (ones n) l) r) p.
induction n; intros; simpl.

apply sf0.

inversion_clear H.

rewrite H0; clear H0.
apply sfI with 1 (pair (Cons one l) (app_ls (ones n) r)).
apply s1R. auto.
rewrite <- ones_comm. apply IHn. tauto.

rewrite H0; clear H0.
apply sfI with 2 (pair (Cons one l) (app_ls (ones n) r)).
apply s1R. auto.
rewrite <- ones_comm. apply IHn. tauto.
Qed.

Lemma Copy_loop_3L_sf: forall n l r,
      sf Copy (pair (app_ls (ones n) l) (Cons one r)) 3
              (pair l (app_ls (ones n) (Cons one r))) 3.
induction n; intros; simpl.

apply sf0.

apply sfI with 3 (pair (app_ls (ones n) l)
                       (Cons one (Cons one r))).
apply s1L. auto.
rewrite <- ones_comm. apply IHn.
Qed.

Lemma Copy_loop_generalized_sf: forall j k n,
      n = j+k ->
      sf Copy (pair (app_ls (ones j) (app_ls (zeros (S k)) Bs))
                    (Cons B (app_ls (ones (S k)) Bs)))
               3
              (pair (app_ls (zeros (S n)) Bs)
                    (Cons B (app_ls (ones (S n)) Bs)))
               3.
induction j; intros.

simpl in H |-*. rewrite H. apply sf0.

apply sfI with 4 (pair (app_ls (ones j) (app_ls (zeros (S k)) Bs))
                       (Cons one (Cons B (app_ls (ones (S k)) Bs)))).
apply s1L. auto.

apply sf_trans with (pair (app_ls (zeros k) Bs)
                          (Cons zero (app_ls (ones (S j))
                                   (Cons B (app_ls (ones (S k)) Bs)))))
                    5.
apply Copy_loop_5L_sf.

apply sfI with 0 (pair (Cons zero (app_ls (zeros k) Bs))
                       (app_ls (ones (S j))
                               (Cons B (app_ls (ones (S k)) Bs)))).
apply s1R. auto.

apply sfI with 0 (pair (Cons zero (app_ls (zeros k) Bs))
                       (Cons zero (app_ls (ones j)
                                  (Cons B (app_ls (ones (S k)) Bs))))).
apply s1W. auto.

apply sfI with 1 (pair (Cons zero (Cons zero (app_ls (zeros k) Bs)))
                       (app_ls (ones j)
                               (Cons B (app_ls (ones (S k)) Bs)))).
apply s1R. auto.

apply sf_trans with (pair (app_ls (ones j) (Cons zero
                                  (Cons zero (app_ls (zeros k) Bs))))
                           (Cons B (app_ls (ones (S k)) Bs)))
                    1.
apply Copy_loop_1and2R_sf. tauto.

apply sfI with 2 (pair (Cons B (app_ls (ones j) (Cons zero (Cons zero
                                                (app_ls (zeros k) Bs)))))
                       (app_ls (ones (S k)) Bs)).
apply s1R. auto.

apply sfI with 2 (pair (Cons one (Cons B (app_ls (ones j) (Cons zero (Cons zero
                                                 (app_ls (zeros k) Bs))))))
                       (app_ls (ones k) Bs)).
apply s1R. auto.

apply sf_trans with (pair (app_ls (ones k) (Cons one (Cons B (app_ls
                                  (ones j) (Cons zero (Cons zero
                                           (app_ls (zeros k) Bs)))))))
                          Bs)
                    2.
apply Copy_loop_1and2R_sf. tauto.

apply sfI with 3 (pair (app_ls (ones k) (Cons one (Cons B (app_ls
                               (ones j) (Cons zero (Cons zero
                                        (app_ls (zeros k) Bs)))))))
                       (Cons one Bs)).
apply s1W. auto.

rewrite ones_comm.
apply sfI with 3 (pair (app_ls (ones k) (Cons B (app_ls (ones j)
                               (Cons zero (Cons zero (app_ls (zeros k) Bs))))))
                       (Cons one (Cons one Bs))).
apply s1L. auto.

apply sf_trans with (pair (Cons B (app_ls (ones j) (Cons zero
                                  (Cons zero (app_ls (zeros k) Bs)))))
                          (app_ls (ones k) (Cons one (Cons one Bs))))
                    3.
apply Copy_loop_3L_sf.

rewrite ones_comm.
apply sfI with 3 (pair (app_ls (ones j) (Cons zero (Cons zero
                                        (app_ls (zeros k) Bs))))
                       (Cons B ((Cons one (app_ls (ones k)
                                                  (Cons one Bs)))))).
apply s1L. auto.

do 2 rewrite zeros_step2. rewrite ones_comm. do 2 rewrite ones_step2.
apply IHj. omega.
Qed.

Lemma Copy_loop_sf: forall n,
      sf Copy (pair (app_ls (ones n) (Cons zero Bs))
                    (Cons B (Cons one Bs)))
               3
              (pair (app_ls (zeros (S n)) Bs)
                    (Cons B (app_ls (ones (S n)) Bs)))
               3.
rewrite zeros_step. change (Cons one Bs) with (app_ls (ones 1) Bs).
intro. apply Copy_loop_generalized_sf. omega.
Qed.

(*************** BEGIN part *****************************************)

Lemma Copy_begin_sf: forall n,
      sf Copy (pair Bs
                    (app_ls (ones (S n)) Bs))
               0
              (pair (app_ls (ones n) (Cons zero Bs))
                    (Cons B (Cons one Bs)))
               3.
intro. simpl.

apply sfI with 0 (pair Bs (Cons zero (app_ls (ones n) Bs))).
apply s1W. auto.

apply sfI with 1 (pair (Cons zero Bs) (app_ls (ones n) Bs)).
apply s1R. auto.

apply sf_trans with (pair (app_ls (ones n) (Cons zero Bs)) Bs)
                    1.
apply Copy_loop_1and2R_sf. tauto.

apply sfI with 2 (pair (Cons B (app_ls (ones n) (Cons zero Bs))) Bs).
apply s1R. auto.

apply sfI with 3 (pair (Cons B (app_ls (ones n) (Cons zero Bs)))
                       (Cons one Bs)).
apply s1W. auto.

apply sfI with 3 (pair (app_ls (ones n) (Cons zero Bs))
                       (Cons B (Cons one Bs))).
apply s1L. auto.

apply sf0.
Qed.

(*************** END part *******************************************)

Lemma Copy_end_6W_sf: forall n r,
      sf Copy (pair (app_ls (zeros n) Bs) (Cons one r)) 6
              (pair Bs (app_ls (ones n) (Cons one r))) 6.
induction n; intros; simpl.

apply sf0.

apply sfI with 6 (pair (app_ls (zeros n) Bs) (Cons zero (Cons one r))).
apply s1L. auto.

apply sfI with 6 (pair (app_ls (zeros n) Bs) (Cons one (Cons one r))).
apply s1W. auto.

rewrite <- ones_comm. apply IHn.
Qed.

Lemma Copy_end: forall n,
      bf Copy (pair (app_ls (zeros n) (Cons zero Bs))
                    (Cons B (Cons one (app_ls (ones n) Bs))))
              3
              (pair Bs
                    (Cons one (app_ls (ones n)
                                      (Cons B (Cons one
                                              (app_ls (ones n) Bs))))))
              7.
destruct n; intros; simpl.

apply bfL with 4; simpl; auto.
apply bfW with 6 one; simpl; auto.
apply bfL with 6; simpl; auto.
apply bfR with 7; simpl; auto.
rewrite <- unfold_Bs. apply bfH.
unfold is_value; auto.

apply bfL with 4; simpl; auto.
apply bfW with 6 one; simpl; auto.

rewrite zeros_comm2. apply bfL with 6; simpl; auto.
apply bfW with 6 one; simpl; auto.

apply sf_to_bf with (pair Bs
                          (app_ls (ones n) (Cons one (Cons one (Cons B
                                           (Cons one (Cons one (app_ls
                                           (ones n) Bs))))))))
                    6.

apply Copy_end_6W_sf.

do 2 rewrite ones_comm. apply bfL with 6; simpl; auto.
apply bfR with 7; simpl; auto.
rewrite <- unfold_Bs. apply bfH.
unfold is_value. auto.
Qed.

(****************** Main proof ******************************)

Theorem Copy_stops: forall n,
        bf Copy (pair Bs (app_ls (ones (S n)) Bs))
                0
                (pair Bs (app_ls (ones (S n))
                                 (Cons B (app_ls (ones (S n)) Bs))))
                7.
intro.

(* Decompositions via small-step + Begin, Loop, End *)

apply sf_to_bf with (pair (app_ls (ones n) (Cons zero Bs))
                          (Cons B (Cons one Bs)))
                    3.
apply Copy_begin_sf.

apply sf_to_bf with (pair (app_ls (zeros n) (Cons zero Bs))
                          (Cons B (Cons one (app_ls (ones n) Bs))))
                    3.
rewrite zeros_comm. rewrite ones_step2. apply Copy_loop_sf.

simpl. apply Copy_end.
Qed.
