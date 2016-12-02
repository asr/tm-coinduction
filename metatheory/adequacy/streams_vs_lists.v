
(*
CoFixpoint Bs := (Cons B Bs).

Lemma unfold_HTape: forall h:HTape,
                    h = (match h with (Cons a k) => (Cons a k) end).
destruct h. reflexivity.
Qed.
*)

Lemma unfold_Bs: Bs = (Cons B Bs).
apply (unfold_HTape Bs).
Qed.

Fixpoint app_ls (l:HTape2) (s:HTape) {struct l}: HTape :=
         match l with
         | nil => s
         | (cons b l') => (Cons b (app_ls l' s))
         end.

(****************** Lists -> Streams *********************)

Lemma lists_streams: forall T s p s' q,
                     bf2 T s p s' q ->
                     forall l r l' r', s=(pair2 l r) ->
                                       s'=(pair2 l' r') ->
                     bf T (pair (app_ls l Bs)
                                (app_ls r Bs))
                          p
                          (pair (app_ls l' Bs)
                                (app_ls r' Bs))
                          q.
induction 1; intros.

(* halt *)

rewrite H0 in H. rewrite H1 in H0; clear H1. inversion_clear H0.
apply bfH.
unfold is_value2 in H. unfold is_value. destruct r.
simpl in H. rewrite unfold_Bs. simpl. assumption.
simpl in H. simpl. assumption.

(* move R, right list is not nil *)

inversion H1. rewrite <- H4; clear H1 H4 H5.
apply bfR with i.
simpl. simpl in H. assumption.
simpl. assert ((Cons b (app_ls l Bs) =
               (app_ls (cons b l) Bs))).
simpl. reflexivity. rewrite H1; clear H1.
apply IHbf2. reflexivity. assumption.

(* move R, right list is nil *)

inversion H1. rewrite <- H4; clear H1.
apply bfR with i.
simpl. simpl in H. assumption.
simpl.
assert ((Cons B (app_ls l Bs) =
        (app_ls (cons B l) Bs))).
simpl. reflexivity. rewrite H1; clear H1.
assert (Bs = app_ls nil Bs).
simpl. reflexivity. rewrite H1 at 2; clear H1.
apply IHbf2. reflexivity. assumption.

(* move L, left list is not nil *)

inversion H1. rewrite <- H5; clear H1.
apply bfL with i.
destruct r.
simpl. simpl in H. assumption.
simpl. simpl in H. assumption.
simpl. assert ((Cons b (app_ls r Bs) =
               (app_ls (cons b r) Bs))).
simpl. reflexivity. rewrite H1; clear H1.
apply IHbf2. reflexivity. assumption.

(* move L, left list is nil*)

inversion H1. rewrite <- H5; clear H1.
apply bfL with i.
destruct r.
simpl. simpl in H. assumption.
simpl. simpl in H. assumption.
simpl.
assert ((Cons B (app_ls r Bs) =
        (app_ls (cons B r) Bs))).
simpl. reflexivity. rewrite H1; clear H1.
assert (Bs = app_ls nil Bs).
simpl. reflexivity. rewrite H1 at 1; clear H1.
apply IHbf2. reflexivity. assumption.

(* write, right list is not nil *)

inversion H1. rewrite <- H4; clear H1.
apply bfW with i a.
simpl. simpl in H. assumption.
simpl. assert ((Cons a (app_ls r Bs) =
               (app_ls (cons a r) Bs))).
simpl. reflexivity. rewrite H1; clear H1.
apply IHbf2. reflexivity. assumption.

(* write, right list is nil *)

inversion H1. rewrite <- H4; clear H1.
apply bfW with i a.
simpl. simpl in H. assumption.
simpl.
assert ((Cons a Bs) =
        (app_ls (cons a nil) Bs)).
simpl. reflexivity. rewrite H1; clear H1.
apply IHbf2. reflexivity. assumption.
Qed.

(****************** Lists_oo -> Streams_oo *********************)

Lemma lists_streams_oo: forall T s p,
                     bi2 T s p ->
                     forall l r, s=(pair2 l r) ->
                     bi T (pair (app_ls l Bs)
                                (app_ls r Bs)) p.
cofix cohp; intros.
inversion_clear H in H0.

(* move-R not nil *)

inversion H0. rewrite <- H3; clear H0.
apply biR with q.
simpl. simpl in H1. assumption.
simpl. assert ((Cons b (app_ls l0 Bs) =
               (app_ls (cons b l0) Bs))).
simpl. reflexivity. rewrite H; clear H.
apply cohp with (pair2 (b :: l0) r0). assumption. reflexivity.

(* move-R nil *)

inversion H0. rewrite <- H3; clear H0.
apply biR with q.
simpl. simpl in H1. assumption.

assert ((hd (app_ls nil Bs)) = B).
simpl. reflexivity.
rewrite H; clear H.

assert ((Cons B (app_ls l0 Bs) =
        (app_ls (cons B l0) Bs))).
simpl. reflexivity.
rewrite H; clear H.

assert ((tl (app_ls nil Bs) =
        (app_ls nil Bs))).
simpl. reflexivity.
rewrite H; clear H.

apply cohp with (pair2 (B :: l0) nil). assumption. reflexivity.

(* move-L not nil *)

inversion H0. rewrite <- H4; clear H0.
apply biL with q.
destruct r0.
simpl. simpl in H1. assumption.
simpl. simpl in H1. assumption.
simpl. assert ((Cons b (app_ls r0 Bs) =
               (app_ls (cons b r0) Bs))).
simpl. reflexivity. rewrite H; clear H.
apply cohp with (pair2 l0 (b :: r0)). assumption. reflexivity.

(* move-L nil *)

inversion H0. rewrite <- H4; clear H0.
apply biL with q.
destruct r0.
simpl. simpl in H1. assumption.
simpl. simpl in H1. assumption.
assert ((hd (app_ls nil Bs)) = B).
simpl. reflexivity.
rewrite H; clear H.
assert ((Cons B (app_ls r0 Bs) =
        (app_ls (cons B r0) Bs))).
simpl. reflexivity.
rewrite H; clear H.

assert ((tl (app_ls nil Bs) =
        (app_ls nil Bs))).
simpl. reflexivity.
rewrite H; clear H.

apply cohp with (pair2 nil (B :: r0)). assumption. reflexivity.

(* write not nil *)

inversion H0. rewrite <- H3; clear H0.
apply biW with q a.
simpl. simpl in H1. assumption.
simpl. assert ((Cons a (app_ls r0 Bs) =
               (app_ls (cons a r0) Bs))).
simpl. reflexivity. rewrite H; clear H.
apply cohp with (pair2 l0 (a :: r0)). assumption. reflexivity.

(* write nil *)

inversion H0. rewrite <- H3; clear H0.
apply biW with q a.
simpl. simpl in H1. assumption.

assert (Cons a (tl (app_ls nil Bs)) =
        (app_ls (cons a nil) Bs)).
simpl. reflexivity.
rewrite H; clear H.

apply cohp with (pair2 l0 (a :: nil)). assumption. reflexivity.
Qed.

(****************** Streams_oo -> Lists_oo *********************)

Fixpoint trunc_Str (n:nat) (s:HTape) {struct n}: HTape2 :=
         match s with (Cons a t) =>
         match n with 0 => nil
                    | (S m) => (cons a (trunc_Str m t))
         end end.

Lemma trunc_0: forall s,
               trunc_Str 0 s = nil.
destruct s. simpl. reflexivity.
Qed.

Lemma trunc_step: forall n a s,
                  trunc_Str (S n) (Cons a s) =
                  cons a (trunc_Str n s).
simpl. reflexivity.
Qed.

Lemma trunc_list: forall l l0 s,
      l0 = app_ls l s ->
      exists n, l = trunc_Str n l0.
induction l; intros.

destruct l0. exists 0. simpl. reflexivity.

destruct l0. simpl in H. inversion H. clear H H1.
assert (exists n : nat, l = trunc_Str n l0). apply IHl with s. assumption.
elim H; clear H. intro n; intros.
exists (S n). simpl. rewrite <- H2; clear H2.
rewrite H. reflexivity.
Qed.

Lemma trunc_trunc: forall n s t,
      trunc_Str n (app_ls (trunc_Str n s) t) =
      trunc_Str n s.
induction n; intros.

do 2 rewrite trunc_0. reflexivity.

destruct s. simpl. rewrite IHn. reflexivity.
Qed.

Lemma streams_lists_oo: forall T s p,
                     bi T s p ->
                     forall l r,
                     s=(pair (app_ls l Bs)
                             (app_ls r Bs)) ->
                     bi2 T (pair2 l r) p.
cofix cohp; intros.
inversion_clear H in H0.

(*** move R ***)

inversion H0; clear H0.

assert (exists n, r = trunc_Str n r0).
apply trunc_list with Bs. assumption.
assert (exists n, l = trunc_Str n l0).
apply trunc_list with Bs. assumption.

elim H; clear H. intro n; intros. rewrite H.
elim H0; clear H0. intro m; intros. rewrite H0.
destruct r0. destruct l0. destruct n. destruct m.

(* r=nil, l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biRn with q.
simpl. simpl in H1. assumption.

apply cohp with (pair Bs Bs).
simpl in H2. rewrite unfold_Bs at 1. assumption.
simpl. rewrite unfold_Bs at 1. reflexivity.

(* r=nil, l=a:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biRn with q.
simpl. simpl in H1. assumption.

apply cohp with (pair (Cons B (Cons s1
                      (app_ls (trunc_Str m l0) Bs)))
                      Bs).
simpl in H2. assumption.
simpl. rewrite trunc_trunc. reflexivity.

destruct m.

(* r=a:r', l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biRc with q.
simpl. simpl in H1. assumption.

rewrite trunc_trunc.
apply cohp with (pair (Cons s0 Bs)
                      (app_ls (trunc_Str n r0) Bs)).
simpl in H2. assumption.
simpl. reflexivity.

(* r=a:r', l=b:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biRc with q.
simpl. simpl in H1. assumption.

do 2 rewrite trunc_trunc.
apply cohp with (pair (Cons s0 (Cons s1
                               (app_ls (trunc_Str m l0) Bs)))
                      (app_ls (trunc_Str n r0) Bs)).
simpl in H2. assumption.
simpl. reflexivity.

(*** move L ***)

inversion H0; clear H0.

assert (exists n, r = trunc_Str n r0).
apply trunc_list with Bs. assumption.
assert (exists n, l = trunc_Str n l0).
apply trunc_list with Bs. assumption.

elim H; clear H. intro n; intros. rewrite H.
elim H0; clear H0. intro m; intros. rewrite H0.
destruct r0. destruct l0. destruct n. destruct m.

(* r=nil, l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biLn with q.
simpl. simpl in H1. assumption.

apply cohp with (pair Bs Bs).
simpl in H2. rewrite unfold_Bs at 2. assumption.
simpl. rewrite unfold_Bs at 2. reflexivity.

(* r=nil, l=a:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. rewrite trunc_trunc. apply biLc with q.
simpl. simpl in H1. assumption.

apply cohp with (pair (app_ls (trunc_Str m l0) Bs)
                      (app_ls  (cons s1 nil) Bs)).
simpl in H2. assumption.
reflexivity.

destruct m.

(* r=a:r', l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. rewrite trunc_trunc. apply biLn with q.
simpl. simpl in H1. assumption.

apply cohp with (pair Bs
                      (app_ls (cons B (cons s0 (trunc_Str n r0))) Bs)).
simpl in H2. assumption.
simpl. reflexivity.

(* r=a:r', l=b:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. do 2 rewrite trunc_trunc. apply biLc with q.
simpl. simpl in H1. assumption.

apply cohp with (pair (app_ls (trunc_Str m l0) Bs)
                      (app_ls (cons s1 (cons s0 (trunc_Str n r0))) Bs)).
simpl in H2. assumption.
reflexivity.

(*** write ***)

inversion H0; clear H0.

assert (exists n, r = trunc_Str n r0).
apply trunc_list with Bs. assumption.
assert (exists n, l = trunc_Str n l0).
apply trunc_list with Bs. assumption.

elim H; clear H. intro n; intros. rewrite H.
elim H0; clear H0. intro m; intros. rewrite H0.
destruct r0. destruct l0. destruct n. destruct m.

(* r=nil, l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biWn with q a.
simpl. simpl in H1. assumption.

apply cohp with (pair Bs (Cons a Bs)).
simpl in H2. assumption.
simpl. reflexivity.

(* r=nil, l=a:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biWn with q a.
simpl. simpl in H1. assumption.

rewrite trunc_trunc.
apply cohp with (pair (app_ls (cons s1 (trunc_Str m l0)) Bs)
                      (app_ls (cons a nil) Bs)).
simpl. simpl in H2. assumption.
reflexivity.

destruct m.

(* r=a:r', l=nil *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. rewrite trunc_trunc. apply biWc with q a.
simpl. simpl in H1. assumption.

apply cohp with (pair Bs
                      (app_ls (cons a (trunc_Str n r0)) Bs)).
simpl. simpl in H2. assumption.
simpl. reflexivity.

(* r=a:r', l=b:l' *)

simpl in H, H0. rewrite H in H4; clear H. rewrite H0 in H3; clear H0.
simpl in H4, H3. rewrite H4, H3.
rewrite H4 in H1, H2; clear H4. rewrite H3 in H1, H2; clear H3.

simpl. apply biWc with q a.
simpl. simpl in H1. assumption.

do 2 rewrite trunc_trunc.
apply cohp with (pair (app_ls (cons s1 (trunc_Str m l0)) Bs)
                      (app_ls (cons a (trunc_Str n r0)) Bs)).
simpl. simpl in H2. assumption.
reflexivity.
Qed.
