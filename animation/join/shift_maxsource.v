
Fixpoint gtstate (q p:State) {struct q}: bool := 
         match q with | 0 => false
                      | (S u) => match p with | 0 => true
                                              | (S v) => (gtstate u v)
         end end.

Fixpoint max_source (T:Spec) (n:nat) {struct T}: nat :=
         match T with | nil => n
                      | (cons A T') =>
         match A with (p, a, r, x) => if (gtstate p n)
                                      then (max_source T' p)
                                      else (max_source T' n)
         end end.

Lemma gt_true: forall a b, a>b -> (gtstate a b)=true.
double induction a b; intros; auto.
omega. omega. simpl. apply H0. omega. 
Qed.

Lemma gt_false: forall a b, a<=b -> (gtstate a b)=false.
double induction a b; intros; auto.
omega. simpl. apply H0. omega.
Qed. 

Lemma max_source_mono: forall M m n,
      m <= n -> max_source M m <= max_source M n.
induction M; intros.

simpl. assumption.

destruct a. destruct p. destruct p. simpl.
elim (le_gt_dec s0 m); intros.

rewrite (gt_false s0 m). rewrite (gt_false s0 n).
apply IHM. assumption. omega. assumption.

rewrite gt_true. elim (le_gt_dec s0 n); intros.
rewrite gt_false. apply IHM. assumption. assumption.
rewrite gt_true. reflexivity. assumption. assumption.
Qed.

Lemma max_source_ge: forall M n,
      n <= max_source M n.
induction M; intros.

simpl. omega.

destruct a. destruct p. destruct p. simpl.
elim (le_gt_dec s0 n); intros.
rewrite gt_false. apply IHM. assumption.
rewrite gt_true.
assert (n <= max_source M n). apply IHM.
assert (max_source M n <= max_source M s0). 
apply max_source_mono. omega.
omega. assumption.
Qed.

Lemma shift_maxsource: forall M i n,
      In i (proj_source (shift M n)) ->
      i <= (max_source M 0)+n.
induction M; intros.

simpl in H. contradiction H.

destruct a. destruct p. destruct p.
simpl in H. simpl. elim (le_gt_dec s0 0); intros.

inversion_clear H.

rewrite <- H0; clear H0.
rewrite gt_false. rewrite plus_comm. apply plus_le_compat_r.
omega. assumption.

rewrite gt_false. apply IHM. assumption. assumption.

inversion_clear H.

rewrite <- H0; clear H0.
rewrite gt_true. rewrite plus_comm. apply plus_le_compat_r.
apply max_source_ge. assumption.

rewrite gt_true. assert (i <= max_source M 0 + n).
apply IHM. assumption.
assert (max_source M 0 + n <= max_source M s0 + n).
apply plus_le_compat_r. apply max_source_mono. omega.
omega. assumption.
Qed.