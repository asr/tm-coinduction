
Require Import List.

Require Import bigstep.
Require Import datatypes.
Require Import smallstep.

(****************** Big -> Small *********************)

Lemma if_bf_then_sf: forall T s p t q,
                     bf T s p t q ->
                     sf T s p t q /\ is_value T t q.
induction 1.

split; auto. apply sf0; assumption.

split.
apply sfI with i (pair (Cons (hd r) l) (tl r)). apply s1R; assumption.
tauto. tauto.

split.
apply sfI with i (pair (tl l) (Cons (hd l) r)). apply s1L; assumption.
tauto. tauto.

split.
apply sfI with i (pair l (Cons a (tl r))). apply s1W; assumption.
tauto. tauto.
Qed.

(****************** Small -> Big *********************)

Lemma s1_to_bf: forall T s p t q u i,
                s1 T s p u i -> bf T u i t q ->
                bf T s p t q.
intros. inversion_clear H in H0.

apply bfR with i; assumption; assumption.
apply bfL with i; assumption; assumption.
apply bfW with i a; assumption; assumption.
Qed.

Lemma if_sf_then_bf: forall T s p t q,
                     sf T s p t q -> is_value T t q ->
                     bf T s p t q.
induction 1; intros.

apply bfH; assumption.

assert (bf T u i t q).
apply IHsf; assumption. clear H0 H1 IHsf.
apply s1_to_bf with u i; assumption; assumption.
Qed.

(****************** Big_oo -> Small_oo *********************)

Lemma if_bi_then_si: forall T s p,
                     bi T s p -> si T s p.
cofix cohp. intros.
inversion_clear H.

apply siC with q (pair (Cons (hd r) l) (tl r)).
apply s1R; assumption.
apply cohp; assumption.

apply siC with q (pair (tl l) (Cons (hd l) r)).
apply s1L; assumption.
apply cohp; assumption.

apply siC with q (pair l (Cons a (tl r))).
apply s1W; assumption.
apply cohp; assumption.
Qed.

(****************** Small_oo -> Big_oo *********************)

Lemma if_si_then_bi: forall T s p,
                     si T s p -> bi T s p.
cofix cohp. intros.
inversion_clear H. inversion_clear H0 in H1.

apply biR with q.
assumption.
apply cohp; assumption.

apply biL with q.
assumption.
apply cohp; assumption.

apply biW with q a.
assumption.
apply cohp; assumption.
Qed.

(****************** Extra tools (for later use) *************)

Lemma sf_to_bf: forall T s p t q u i,
                sf T s p u i -> bf T u i t q ->
                bf T s p t q.
induction 1; intros.

assumption.

assert (bf T u i t q). apply IHsf; assumption.
apply s1_to_bf with u i; assumption; assumption.
Qed.

Lemma sf_trans: forall T s p t q u i,
                sf T s p u i -> sf T u i t q ->
                sf T s p t q.
induction 1; intros.

assumption.

assert (sf T u i t q). apply IHsf; assumption.
apply sfI with i u; assumption; assumption.
Qed.
