
(****************** One-step Reduction **************)

Inductive s1: Spec -> Tape -> State -> Tape -> State -> Prop :=

(* RIGHT move *)

 | s1R: forall T:Spec, forall p q:State,
        forall l r:HTape,
        (tr T p (read (pair l r))) = (Some (q, R)) ->
        (s1 T (pair l r) p
              (pair (Cons (hd r) l) (tl r)) q)

(* LEFT move *)

 | s1L: forall T:Spec, forall p q:State,
        forall l r:HTape,
        (tr T p (read (pair l r))) = (Some (q, L)) ->
        (s1 T (pair l r) p
              (pair (tl l) (Cons (hd l) r)) q)

(* WRITE move *)

 | s1W: forall T:Spec, forall p q:State,
        forall l r:HTape, forall a:Sym,
        (tr T p (read (pair l r))) = (Some (q, (W a))) ->
        (s1 T (pair l r) p
              (pair l (Cons a (tl r))) q).

(****************** Finite Reduction *********************)

Inductive sf: Spec -> Tape -> State -> Tape -> State -> Prop :=

(* HALT move *)

   sf0: forall T:Spec, forall q:State, forall t:Tape,
        (sf T t q t q)

(* inductive moves *)

 | sfI: forall T:Spec, forall p q i:State, forall s t u:Tape,
        (s1 T s p u i) -> (sf T u i t q) ->
        (sf T s p t q).

(****************** Infinite Reduction *********************)

CoInductive si: Spec -> Tape -> State -> Prop :=

(* coinductive moves *)

 | siC: forall T:Spec, forall p q:State, forall s t:Tape,
        (s1 T s p t q) -> (si T t q) ->
        (si T s p).