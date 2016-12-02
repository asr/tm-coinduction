
(*** Section 4 of the paper ***)

CoFixpoint Bs := Cons B Bs.

CoFixpoint same (a:Sym) := Cons a (same a).

CoFixpoint blink (a b:Sym) := Cons a (Cons b (blink a b)).

CoFixpoint merge (h k:HTape) := 
           match h with | Cons a h' => 
           match k with | Cons b k' => Cons a (Cons b (merge h' k'))
           end end.

CoInductive EqH: HTape -> HTape -> Prop :=
            eqh: forall a:Sym, forall h k:HTape,
                 EqH h k -> EqH (Cons a h) (Cons a k).

Lemma unfold_HTape: forall h:HTape, 
                    h = match h with | Cons a k => Cons a k end.
destruct h. auto.
Qed.

Lemma unfold_same: forall a:Sym, same a = (Cons a (same a)).
intro. apply (unfold_HTape (same a)).
Qed.

Lemma unfold_blink: forall a b:Sym, blink a b = (Cons a (Cons b (blink a b))).
intros. apply (unfold_HTape (blink a b)).
Qed.

Lemma unfold_merge: forall a b:Sym, forall h k:HTape,
      merge (Cons a h) (Cons b k) = (Cons a (Cons b (merge h k))).
intros. apply (unfold_HTape (merge (Cons a h) (Cons b k))).
Qed.

Lemma example: forall a b:Sym,
               EqH (merge (same a) (same b))
                   (blink a b).
cofix co_hp. intros.
rewrite unfold_same. rewrite (unfold_same b). rewrite unfold_merge.
rewrite (unfold_blink a b).
do 2 apply eqh. apply co_hp.
Qed.