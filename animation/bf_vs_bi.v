
(*** Convergence and divergence are mutually exclusive ***)

Lemma bf_not_bi: forall T s p t q,
      bf T s p t q -> ~bi T s p.
induction 1; intro.

(* stop *)
unfold is_value in H; inversion_clear H0 in H.
rewrite H in H1; inversion H1.
rewrite H in H1; inversion H1.
rewrite H in H1; inversion H1.

(* right *)
inversion_clear H1; clear H0.
rewrite H in H2; apply IHbf; inversion_clear H2; assumption.
rewrite H in H2; inversion H2.
rewrite H in H2; inversion H2.

(* left *)
inversion_clear H1; clear H0.
rewrite H in H2; inversion H2.
rewrite H in H2; apply IHbf; inversion_clear H2; assumption.
rewrite H in H2; inversion H2.

(* write *)
inversion_clear H1; clear H0.
rewrite H in H2; inversion H2.
rewrite H in H2; inversion H2.
rewrite H in H2; apply IHbf; inversion_clear H2; assumption.
Qed.

Lemma bi_not_bf: forall T s p t q,
      bi T s p -> ~bf T s p t q.
unfold not; intros.
generalize H; clear H; change (~bi T s p).
apply bf_not_bi with t q; assumption.
Qed.