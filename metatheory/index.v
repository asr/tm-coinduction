
Load datatypes.

Load bigstep.
Load bf_vs_bi.

Parameter B: Sym.

Load "adequacy/bigstep_lists".

CoFixpoint Bs := Cons B Bs.

Lemma unfold_HTape: forall h:HTape,
                    h = match h with | Cons a k => Cons a k end.
destruct h. auto.
Qed.

Load "adequacy/streams_vs_lists".

Load "adequacy/smallstep".
Load "adequacy/big_vs_small".
