
Require Import datatypes.

(************* Syntax of Turing machines with lists ***************)

Definition HTape2: Set := list Sym.

Inductive Tape2: Set := pair2: HTape2 -> HTape2 -> Tape2.

Definition read2 (t:Tape2): Sym :=
           match t with (pair2 l r) =>
           match r with nil => B
                      | cons b r' => b
           end end.

Definition is_value2 (T:Spec) (t:Tape2) (q:State) :=
           tr T q (read2 t) = None.

(****************** INDUCTIVE Semantics *********************)

Inductive bf2: Spec -> Tape2 -> State -> Tape2 -> State -> Prop :=

(* HALT move *)

   bfH2: forall T:Spec, forall q:State,
        forall t:Tape2,
        (is_value2 T t q) ->
        (bf2 T t q t q)

(* RIGHT moves *)

 | bfRc: forall T:Spec, forall p q i:State,
        forall l r:HTape2, forall t:Tape2, forall b:Sym,
        (tr T p (read2 (pair2 l (cons b r)))) = (Some (i, R)) ->
        (bf2 T (pair2 (cons b l) r) i t q) ->
        (bf2 T (pair2 l (cons b r)) p t q)

 | bfRn: forall T:Spec, forall p q i:State,
        forall l:HTape2, forall t:Tape2,
        (tr T p (read2 (pair2 l nil))) = (Some (i, R)) ->
        (bf2 T (pair2 (cons B l) nil) i t q) ->
        (bf2 T (pair2 l nil) p t q)

(* LEFT moves *)

 | bfLc: forall T:Spec, forall p q i:State,
        forall l r:HTape2, forall t:Tape2, forall b:Sym,
        (tr T p (read2 (pair2 (cons b l) r))) = (Some (i, L)) ->
        (bf2 T (pair2 l (cons b r)) i t q) ->
        (bf2 T (pair2 (cons b l) r) p t q)

 | bfLn: forall T:Spec, forall p q i:State,
        forall r:HTape2, forall t:Tape2,
        (tr T p (read2 (pair2 nil r))) = (Some (i, L)) ->
        (bf2 T (pair2 nil (cons B r)) i t q) ->
        (bf2 T (pair2 nil r) p t q)

(* WRITE moves *)

 | bfWc: forall T:Spec, forall p q i:State,
        forall l r:HTape2, forall t:Tape2, forall a b:Sym,
        (tr T p (read2 (pair2 l (cons b r)))) = (Some (i, (W a))) ->
        (bf2 T (pair2 l (cons a r)) i t q) ->
        (bf2 T (pair2 l (cons b r)) p t q)

 | bfWn: forall T:Spec, forall p q i:State,
        forall l:HTape2, forall t:Tape2, forall a:Sym,
        (tr T p (read2 (pair2 l nil))) = (Some (i, (W a))) ->
        (bf2 T (pair2 l (cons a nil)) i t q) ->
        (bf2 T (pair2 l nil) p t q).

(****************** COINDUCTIVE Semantics *********************)

CoInductive bi2: Spec -> Tape2 -> State -> Prop :=

(* RIGHT moves *)

   biRc: forall T:Spec, forall p q:State,
        forall l r:HTape2, forall b:Sym,
        (tr T p (read2 (pair2 l (cons b r)))) = (Some (q, R)) ->
        (bi2 T (pair2 (cons b l) r) q) ->
        (bi2 T (pair2 l (cons b r)) p)

 | biRn: forall T:Spec, forall p q:State,
        forall l:HTape2,
        (tr T p (read2 (pair2 l nil))) = (Some (q, R)) ->
        (bi2 T (pair2 (cons B l) nil) q) ->
        (bi2 T (pair2 l nil) p)

(* LEFT moves *)

 | biLc: forall T:Spec, forall p q:State,
        forall l r:HTape2, forall b:Sym,
        (tr T p (read2 (pair2 (cons b l) r))) = (Some (q, L)) ->
        (bi2 T (pair2 l (cons b r)) q) ->
        (bi2 T (pair2 (cons b l) r) p)

 | biLn: forall T:Spec, forall p q:State,
        forall r:HTape2,
        (tr T p (read2 (pair2 nil r))) = (Some (q, L)) ->
        (bi2 T (pair2 nil (cons B r)) q) ->
        (bi2 T (pair2 nil r) p)

(* WRITE moves *)

 | biWc: forall T:Spec, forall p q:State,
        forall l r:HTape2, forall a b:Sym,
        (tr T p (read2 (pair2 l (cons b r)))) = (Some (q, (W a))) ->
        (bi2 T (pair2 l (cons a r)) q) ->
        (bi2 T (pair2 l (cons b r)) p)

 | biWn: forall T:Spec, forall p q:State,
        forall l:HTape2, forall a:Sym,
        (tr T p (read2 (pair2 l nil))) = (Some (q, (W a))) ->
        (bi2 T (pair2 l (cons a nil)) q) ->
        (bi2 T (pair2 l nil) p).
