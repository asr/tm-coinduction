
Definition read (t:Tape): Sym := 
           match t with (pair l r) => (hd r)
           end.

Definition is_value (T:Spec) (t:Tape) (q:State) := 
           tr T q (read t) = None.

(****************** INDUCTIVE Semantics *********************)

Inductive bf: Spec -> Tape -> State -> Tape -> State -> Prop :=

(* HALT move *)

   bfH: forall T:Spec, forall q:State,
        forall t:Tape,
        (is_value T t q) -> 
        (bf T t q t q)

(* RIGHT move *)

 | bfR: forall T:Spec, forall p q i:State,
        forall l r:HTape, forall t:Tape,
        (tr T p (read (pair l r))) = (Some (i, R)) ->
        (bf T (pair (Cons (hd r) l) (tl r)) i t q) ->
        (bf T (pair l r) p t q)

(* LEFT move *)

 | bfL: forall T:Spec, forall p q i:State,
        forall l r:HTape, forall t:Tape,
        (tr T p (read (pair l r))) = (Some (i, L)) ->
        (bf T (pair (tl l) (Cons (hd l) r)) i t q) ->
        (bf T (pair l r) p t q)

(* WRITE move *)

 | bfW: forall T:Spec, forall p q i:State,
        forall l r:HTape, forall t:Tape, forall a:Sym,
        (tr T p (read (pair l r))) = (Some (i, (W a))) ->
        (bf T (pair l (Cons a (tl r))) i t q) ->
        (bf T (pair l r) p t q).

(****************** COINDUCTIVE Semantics *********************)

CoInductive bi: Spec -> Tape -> State -> Prop :=

(* RIGHT move *)

   biR: forall T:Spec, forall p q:State,
        forall l r:HTape,
        (tr T p (read (pair l r))) = (Some (q, R)) ->
        (bi T (pair (Cons (hd r) l) (tl r)) q) ->
        (bi T (pair l r) p)

(* LEFT move *)

 | biL: forall T:Spec, forall p q:State,
        forall l r:HTape,
        (tr T p (read (pair l r))) = (Some (q, L)) ->
        (bi T (pair (tl l) (Cons (hd l) r)) q) ->
        (bi T (pair l r) p)

(* WRITE move *)

 | biW: forall T:Spec, forall p q:State,
        forall l r:HTape, forall a:Sym,
        (tr T p (read (pair l r))) = (Some (q, (W a))) ->
        (bi T (pair l (Cons a (tl r))) q) ->
        (bi T (pair l r) p).