
Fixpoint shift (T:Spec) (n:nat) {struct T}: Spec :=
         match T with | nil => nil
                      | (cons A T') =>
         match A with (p, a, r, x) =>
                      (cons (n+p, a, n+r, x) (shift T' n))
         end end.

Lemma app_shift: forall M i n L,
      In i (proj_target (app (shift M n) L)) ->
      i >= n \/ In i (proj_target L).
induction M; intros.

simpl in H. tauto.

destruct a. destruct p. destruct p.
simpl in H. inversion_clear H.
rewrite <- H0. left. omega.
apply IHM. assumption.
Qed.

Lemma shift_stop: forall T s p,
      is_value T s p ->
      forall n, is_value (shift T n) s (n+p).
induction T; intros.

unfold is_value. simpl. reflexivity.

destruct a. destruct p0. destruct p0. simpl.
unfold is_value in IHT, H |-*. simpl in H |-*.
elim (eq_nat_dec p s2); intro.
elim (eq_sym_dec (read s) s3); intro.

rewrite a, a0 in H.
rewrite eq_state in H. rewrite eq_sym in H. inversion H.

rewrite a in H |- *.
rewrite eq_state in H |- *. rewrite neq_sym in H |- *.
apply IHT. assumption. auto. auto.

rewrite neq_state in H |- *.
apply IHT. assumption. assumption.
unfold not; intro. unfold not in b; apply b.
apply plus_reg_l with n. assumption.
Qed.

Lemma shift_move: forall T s p i x,
      tr T p s = Some (i, x) ->
      forall n, tr (shift T n) (n+p) s = Some (n+i, x).
induction T; intros.

simpl in H. inversion H.

destruct a. destruct p0. destruct p0.
simpl in H |-*.
elim (eq_nat_dec p s2); intro.
elim (eq_sym_dec s s3); intro.

rewrite a, a0 in H |-*.
rewrite eq_state in H |-*. rewrite eq_sym in H |-*.
inversion_clear H. reflexivity.

rewrite a in H |- *.
rewrite eq_state in H |- *. rewrite neq_sym in H |- *.
apply IHT. assumption. auto. auto.

rewrite neq_state in H |- *.
apply IHT. assumption. assumption.
unfold not; intro. unfold not in b; apply b.
apply plus_reg_l with n. assumption.
Qed.

(*************** Convergence ***************)

Lemma shift_preserves_stop: forall T s p t q,
      bf T s p t q ->
      forall n, bf (shift T n) s (n+p) t (n+q).
induction 1; intros.

apply bfH.
apply shift_stop. assumption.

apply bfR with (n+i).
apply shift_move. assumption.
apply IHbf.

apply bfL with (n+i).
apply shift_move. assumption.
apply IHbf.

apply bfW with (n+i) a.
apply shift_move. assumption.
apply IHbf.
Qed.

(*************** Divergence ***************)

Lemma shift_preserves_loop: forall T s p,
      bi T s p ->
      forall n, bi (shift T n) s (n+p).
cofix co_hp; intros.
inversion_clear H.

apply biR with (n+q).
apply shift_move. assumption.
apply co_hp. assumption.

apply biL with (n+q).
apply shift_move. assumption.
apply co_hp. assumption.

apply biW with (n+q) a.
apply shift_move. assumption.
apply co_hp. assumption.
Qed.
