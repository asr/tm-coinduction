
Require Import List EqNat Arith Omega.

(************* Syntax of Turing machines ***************)

(*** Specification ***)

Parameter State: Set.

(*
Definition State := nat.
*)

Parameter Sym: Set. 

(*
Inductive Sym: Set := blank: Sym
                    | one: Sym
                    | zero: Sym. 
*)

Inductive Head: Set := R: Head
                     | L: Head
                     | W: Sym -> Head. 

Definition Spec: Set := (list (State * Sym * State * Head)).

(*** Tape ***)

CoInductive HTape: Set := Cons: Sym -> HTape -> HTape.

Definition hd (h:HTape) := match h with | Cons a k => a end.

Definition tl (h:HTape) := match h with | Cons a k => k end.

Inductive Tape: Set := pair: HTape -> HTape -> Tape.

(*** Transition Function ***)

Parameter tr: Spec -> State -> Sym -> option (State * Head).

(*
Fixpoint eqsym (a b:Sym) {struct a}: bool := 
         match a, b with B, B => true
                    |    one, one => true
                    |    zero, zero => true
                    |    _ , _ => false
         end.

Fixpoint eqstate (q p:State) {struct q}: bool := 
         match q, p with 0, 0 => true
                    |    (S u), (S v) => (eqstate u v)
                    |    _, _ => false
         end.

Fixpoint tr (T:Spec) (q:State) (a:Sym) {struct T}: option (State * Head) :=
         match T with | nil => None
                      | (cons A T') =>
         match A with (p, b, r, x) => 
                      if (eqstate q p)
                      then if (eqsym b a)
                           then (Some (r, x))
                           else (tr T' q a)
                      else (tr T' q a)
         end end.
*)