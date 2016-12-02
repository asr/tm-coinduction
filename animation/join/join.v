
(**************** Preliminary definitions and proofs ***************)

Fixpoint proj_source (T:Spec) {struct T}: (list State) :=
         match T with | nil => nil
                      | (cons A T') =>
         match A with (p, a, r, x) => (cons p (proj_source T'))
         end end.

Fixpoint proj_target (T:Spec) {struct T}: (list State) :=
         match T with | nil => nil
                      | (cons A T') =>
         match A with (p, a, r, x) => (cons r (proj_target T'))
         end end.

Lemma eq_sym: forall a, (eqsym a a)=true.
induction a.
auto. auto. auto.
Qed.

Lemma neq_sym: forall a b, a<>b -> (eqsym a b)=false.
double induction a b; auto; intros.
contradiction H; auto. contradiction H; auto. contradiction H; auto.
Qed.

Lemma eq_sym_dec: forall a b:Sym, {a=b} + {a<>b}.
destruct a; destruct b; auto.
right; discriminate. right; discriminate.
right; discriminate. right; discriminate.
right; discriminate. right; discriminate.
Qed.

Lemma eq_state: forall p, (eqstate p p)=true.
induction p.
auto. simpl. assumption.
Qed.

Lemma neq_state: forall p q, p<>q -> (eqstate p q)=false.
double induction p q; auto; intros.
contradiction H; auto.
simpl. apply H0. auto.
Qed.

(**************** Join properties about CONVERGENCE ***************)

(* Auxiliary lemma 1: if M stops with the current configuration C,
                      then M::N makes the same first step as N with C
*)

Lemma move_preserves_halt_app: forall M p a,
      tr M p a = None ->
      forall N,
      tr N p a = tr (app M N) p a.
induction M; intros. 

simpl. reflexivity.

destruct a. destruct p0. destruct p0. simpl in H |- *.
elim (eq_nat_dec p s0); intro.
elim (eq_sym_dec a0 s2); intro.

rewrite a, a1 in H.
rewrite eq_state in H. rewrite eq_sym in H.
inversion H.

rewrite <- a in H |- *. 
rewrite eq_state in H |- *. rewrite neq_sym in H |- *.
apply IHM. assumption. auto. auto.

rewrite neq_state in H |- *.
apply IHM. assumption. assumption. assumption.
Qed.

(* Auxiliary lemma 2: if M does not stop with the current C,
                      then M::N the same first step as M with C
*)

Lemma move_preserves_app: forall M p a,
      tr M p a <> None ->
      forall N,
      tr M p a = tr (app M N) p a.
induction M; intros.

simpl in H. contradiction H. reflexivity.

destruct a. destruct p0. destruct p0. simpl in H |-*. 
elim (eq_nat_dec p s0); intro.
elim (eq_sym_dec a0 s2); intro.

rewrite a, a1.
rewrite eq_state. rewrite eq_sym. reflexivity.

rewrite a in H |- *.
rewrite eq_state in H |- *. rewrite neq_sym in H |- *.
apply IHM. assumption. auto. auto.

rewrite neq_state in H |- *.
apply IHM. assumption. assumption. assumption.
Qed.

(* Auxiliary lemma 3: if M stops with the current configuration C
                      and its source states are not reachable from C,
                      then M::N makes the same computation as N with C
*)

Lemma derive_not_source: forall M i a,
      ~ In i (proj_source M) -> tr M i a=None.
induction M; intros. 

simpl. reflexivity.

destruct a. destruct p. destruct p. simpl in H |- *.
assert (~s0=i /\ ~In i (proj_source M)). tauto.
inversion_clear H0; clear H.
elim (eq_nat_dec i s0); intro.

contradiction H1. auto.

rewrite neq_state.
apply IHM. assumption. assumption.
Qed.

Lemma derive_target: forall M p a i x,
      tr M p a=(Some (i, x)) -> In i (proj_target M).
induction M; intros. 

simpl in H. inversion H.

destruct a. destruct p0. destruct p0. simpl in H |- *.
elim (eq_nat_dec p s0); intro.
elim (eq_sym_dec a0 s2); intro.

rewrite a, a1 in H.
rewrite eq_state in H. rewrite eq_sym in H.
inversion_clear H. tauto.

rewrite a in H.
rewrite eq_state in H. rewrite neq_sym in H.
right. apply IHM with s0 a0 x. assumption. auto.

rewrite neq_state in H.
right. apply IHM with p a0 x. assumption. assumption.
Qed.

Lemma bf_preserves_halt_app: forall M p s N,
      tr M p (read s) = None ->
      (forall i, In i (proj_target N) ->
                 ~In i (proj_source M)) ->
      forall t q,
      bf N s p t q -> bf (app M N) s p t q.
induction 3; intros.

(* halt *)

apply bfH. 
unfold is_value. rewrite <- move_preserves_halt_app.
assumption. assumption.

(* move R *)

apply bfR with i. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply IHbf; clear IHbf.

assert (In i (proj_target T)).
apply derive_target with p (read (pair l r)) R. assumption.
assert (~ In i (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.

(* move L *)

apply bfL with i. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply IHbf; clear IHbf.

assert (In i (proj_target T)).
apply derive_target with p (read (pair l r)) L. assumption.
assert (~ In i (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.

(* write *)

apply bfW with i a. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply IHbf; clear IHbf.

assert (In i (proj_target T)).
apply derive_target with p (read (pair l r)) (W a). assumption.
assert (~ In i (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.
Qed.

(***************************************************)

(* Main result: M and N may be joined
                provided M's source states cannot be reached from N
                once M has stopped
*)

Theorem join_stop: forall M p s t q N u r,
      bf M p s t q -> bf N t q u r ->
      (forall i, In i (proj_target N) ->
                 ~In i (proj_source M)) ->
      bf (app M N) p s u r.
induction 1; intros.

(*************** stop ***************)

apply bf_preserves_halt_app. 
assumption. assumption. assumption.

(************* move R ***************)

apply bfR with i.

(* tr *)

rewrite <- move_preserves_app.
assumption.
rewrite H. discriminate.

(* induction *) 

apply IHbf; assumption.

(************* move L ***************)

apply bfL with i.

(* tr *)

rewrite <- move_preserves_app.
assumption.
rewrite H. discriminate.

(* induction *) 

apply IHbf; assumption.

(************* write ***************)

apply bfW with i a.

(* transition *)

rewrite <- move_preserves_app.
assumption.
rewrite H. discriminate.

(* induction *) 

apply IHbf; assumption.
Qed.

(**************** Join properties about DIVERGENCE ***************)

(* Auxiliary lemma: similar to the convergence case
*)

Lemma bi_preserves_halt_app: forall M p s N,
      tr M p (read s) = None ->
      (forall i, In i (proj_target N) ->
                 ~In i (proj_source M)) ->
      bi N s p -> bi (app M N) s p.
cofix co_hp; intros.
inversion_clear H1 in H.

(* move R *)

apply biR with q. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply co_hp; clear co_hp.

assert (In q (proj_target N)).
apply derive_target with p (read (pair l r)) R. assumption.
assert (~ In q (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.
assumption.

(* move L *)

apply biL with q. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply co_hp; clear co_hp.

assert (In q (proj_target N)).
apply derive_target with p (read (pair l r)) L. assumption.
assert (~ In q (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.
assumption.

(* write *)

apply biW with q a. 

rewrite <- move_preserves_halt_app.
assumption. assumption. 

apply co_hp; clear co_hp.

assert (In q (proj_target N)).
apply derive_target with p (read (pair l r)) (W a). assumption.
assert (~ In q (proj_source M)). apply H0. assumption.
apply derive_not_source. assumption.
assumption.
assumption.
Qed.

(***************************************************)

(* Main result: M and N may be joined
                provided M's source states cannot be reached from N
                once M has stopped
*)

Theorem join_loop: forall M p s t q N,
      bf M p s t q -> bi N t q ->
      (forall i, In i (proj_target N) ->
                 ~In i (proj_source M)) ->
      bi (app M N) p s.
cofix co_hp; intros.
inversion_clear H in H0.

(*************** stop ***************)

apply bi_preserves_halt_app. 
assumption. assumption. assumption.

(************* move R ***************)

apply biR with i.

(* transition *)

rewrite <- move_preserves_app.
assumption.
rewrite H2. discriminate.

(* coinduction *) 

apply co_hp with t q; assumption.

(************* move L ***************)

apply biL with i.

(* transition *)

rewrite <- move_preserves_app.
assumption.
rewrite H2. discriminate.

(* coinduction *) 

apply co_hp with t q; assumption.

(************* write ***************)

apply biW with i a.

(* transition *)

rewrite <- move_preserves_app.
assumption.
rewrite H2. discriminate.

(* coinduction *) 

apply co_hp with t q; assumption.
Qed.