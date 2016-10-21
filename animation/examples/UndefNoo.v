
(* Function undef(n) = undefined for any n

   Example machine:
      1 1 -> 1 R
      1 B -> 2 1
      2 1 -> 2 L
      2 B -> 1 1
*)

Definition undef: Spec := (1, one, 1,     R) :: 
                          (1, B  , 2, W one) :: 
                          (2, one, 2,     L) :: 
                          (2, B  , 1, W one) :: nil.

(****************** Split Divergence, via SF1 *********************)

Inductive sf1: Spec -> Tape -> State -> Tape -> State -> Prop :=

(* one move *)

 | sf1A: forall T:Spec, forall p q:State, forall s t:Tape,
         (s1 T s p t q) -> (sf1 T s p t q)

(* inductive moves *)

 | sf1I: forall T:Spec, forall p q i:State, forall s t u:Tape,
         (s1 T s p u i) -> (sf1 T u i t q) ->
         (sf1 T s p t q).

CoInductive gsi: Spec -> Tape -> State -> Prop :=

|  gsiC: forall T:Spec, forall p q:State, forall s t:Tape,
         sf1 T s p t q -> gsi T t q -> gsi T s p.

(****************** Subsumed by BI ****************************)

Lemma if_bi_then_guarded: forall T s p,
      bi T s p -> gsi T s p.
cofix cohp.
intros. inversion_clear H.

apply gsiC with q (pair (Cons (hd r) l) (tl r)).
apply sf1A. apply s1R. assumption. 
apply cohp. assumption. 

apply gsiC with q (pair (tl l) (Cons (hd l) r)).
apply sf1A. apply s1L. assumption.
apply cohp. assumption.

apply gsiC with q (pair l (Cons a (tl r))).
apply sf1A. apply s1W. assumption.
apply cohp. assumption.
Qed.

(****************** Subsumes SI ****************************)

Lemma if_guarded_then_si: forall T s p,
      gsi T s p -> si T s p.
cofix cohp.
intros. inversion_clear H. inversion_clear H0.

apply siC with q t.
assumption.
apply cohp. assumption.

apply siC with i u.
assumption.
apply cohp. apply gsiC with q t. assumption. assumption.
Qed.

(****************** Subsumed by SI ****************************)

Lemma if_si_then_guarded: forall T s p,
      si T s p -> gsi T s p.
cofix cohp.
intros. inversion_clear H.

apply gsiC with q t.
apply sf1A. assumption.

apply cohp. assumption.
Qed.

(******************************** Subsumes BI **********************)

Lemma if_guarded_then_bi: forall T s p,
      gsi T s p -> bi T s p.
intros.
apply if_si_then_bi. apply if_guarded_then_si. assumption.
Qed.

(****************** Transitivity of SF1 ****************************)

Lemma sf1_trans: forall T s p t q u i,
                 sf1 T s p u i -> sf1 T u i t q ->
                 sf1 T s p t q.
induction 1; intros.

apply sf1I with q0 t0. assumption. assumption.

assert (sf1 T u i t q). apply IHsf1. assumption.
clear H0 IHsf1 H1.
apply sf1I with i u. assumption. assumption.
Qed.

(********** Divergence proof with Split Divergence ************************)

Lemma ones_step2: forall n l,
      (Cons one (app_ls (ones n) l)) = (app_ls (ones (S n)) l).
simpl. reflexivity.
Qed.

Lemma undef_loops: forall n,
      gsi undef (pair Bs (app_ls (ones (S n)) Bs)) 1.
cofix co_hp.
intro. apply gsiC with 1 (pair Bs (app_ls (ones (S (S (S n)))) Bs)).

apply sf1_trans with (pair (app_ls (ones (S n)) Bs) (Cons one Bs)) 2.

Lemma undef_scan_right: forall m l,
      sf1 undef (pair l (app_ls (ones m) Bs)) 1
                (pair (app_ls (ones m) l) (Cons one Bs)) 2.
induction m; simpl; intros.

apply sf1A. apply s1W. auto.

apply sf1I with 1 (pair (Cons one l) (app_ls (ones m) Bs)).
apply s1R. auto.
rewrite <- ones_comm. apply IHm. 
Qed.

apply undef_scan_right.

Lemma undef_scan_left: forall m r,
      sf1 undef (pair (app_ls (ones m) Bs) (Cons one r)) 2
                (pair Bs (app_ls (ones (S (S m))) r)) 1.
induction m; simpl; intros.

apply sf1I with 2 (pair Bs (Cons B (Cons one r))).
apply s1L. auto.
apply sf1A. apply s1W.
auto.

apply sf1I with 2 (pair (app_ls (ones m) Bs)
                        (Cons one (Cons one r))).
apply s1L. auto.
rewrite <- ones_comm. apply IHm.
Qed.

apply undef_scan_left.

apply co_hp.
Qed.