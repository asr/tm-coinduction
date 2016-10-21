
(**************** WITNESS Machine ***************)

Definition witness := 
  (app Copy
  (app (shift HM     7)
       (shift Dither (max_source HM 0 + 8)))).

(*** Auxiliary properties for the 2nd path of Undecidability ***)

Lemma max_source_shift: forall M m n k,
      m <= n ->
      max_source (shift M m) (max_source M k + n) =
      max_source M k + n.
induction M; intros.

simpl. reflexivity.

destruct a. destruct p. destruct p.
simpl. elim (le_gt_dec s0 k); intros.
rewrite (gt_false s0 k).
rewrite plus_comm at 1.
rewrite gt_false. apply IHM. assumption.

apply plus_le_compat.
assert (k <= max_source M k). apply max_source_ge. omega.
assumption. assumption.

rewrite (gt_true s0 k).
rewrite plus_comm at 1.
rewrite gt_false. apply IHM. assumption.
apply plus_le_compat. apply max_source_ge. assumption. assumption.
Qed.

Lemma maxsource_swap: forall M n a b,
      max_source (cons a (cons b M)) n = 
      max_source (cons b (cons a M)) n.
intros. 
destruct a. destruct p. destruct p.
destruct b. destruct p. destruct p. simpl.

elim (le_gt_dec s0 n); intros.

rewrite gt_false.
elim (le_gt_dec s4 n); intros.

rewrite gt_false. reflexivity. assumption.

rewrite gt_true. rewrite gt_false. reflexivity. omega.
assumption. assumption.

rewrite gt_true.
elim (le_gt_dec s4 n); intros.

rewrite gt_false. rewrite gt_false. reflexivity. assumption. omega.

elim (le_gt_dec s4 s0); intros.

rewrite gt_false. rewrite gt_true.
assert (s4 < s0 \/ s4 = s0). apply le_lt_or_eq. assumption.
elim H; clear H a; intro.

rewrite gt_true. reflexivity. assumption.
rewrite H. rewrite gt_false. reflexivity.
omega. assumption. assumption. 

rewrite gt_true. rewrite gt_true. rewrite gt_false. reflexivity.
omega. assumption. assumption. assumption. 
Qed.

Lemma max_source_1step: forall p a x q b M n,
      max_source ((p, a, x, q) :: b :: M) n =
      if gtstate p n then max_source (b :: M) p
                     else max_source (b :: M) n.
auto.
Qed.

Lemma maxsource_app_comm_item: forall M n a,
      max_source (app M (cons a nil)) n = max_source (cons a M) n.
induction M; intros.

simpl. reflexivity.

rewrite maxsource_swap.
destruct a. destruct p. destruct p.

rewrite max_source_1step. simpl (max_source (((s0, s2, s, h) :: M) ++ a0 :: nil) n). 
elim (le_gt_dec s0 n); intros.

rewrite gt_false. apply IHM. assumption.

rewrite gt_true. apply IHM. assumption.
Qed. 

Lemma maxsource_app_comm: forall M N n,
      max_source (app M N) n = max_source (app N M) n.
induction M; intros.

simpl. rewrite <- app_nil_end. reflexivity.

assert (N ++ a :: M = app (app N (cons a nil)) M).
rewrite <- ass_app. rewrite <- app_comm_cons. auto.
rewrite H; clear H. rewrite <- IHM.

rewrite <- app_comm_cons. rewrite ass_app.
rewrite <- maxsource_app_comm_item. reflexivity.
Qed.

Lemma max_source_HM_witness:
      max_source witness 0 = max_source HM 0 + 9.
simpl.
rewrite maxsource_app_comm.
simpl. rewrite (gt_true (max_source HM 0 + 8 + 0) 6).
rewrite (gt_true (max_source HM 0 + 8 + 1) (max_source HM 0 + 8 + 0)).
rewrite (gt_false (max_source HM 0 + 8 + 1) (max_source HM 0 + 8 + 1)).

rewrite <- plus_assoc. change (8+1) with 9.

apply max_source_shift. omega.

omega. omega. omega. 
Qed.