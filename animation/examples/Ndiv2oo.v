
Require Import List Omega.

Require Import bigstep.
Require Import coinduction.
Require Import datatypes.
Require Import streams_vs_lists.

(* Function div2(n) = n/2       if n is even
                      undefined otherwise

   Example machine:
      1 1 -> 1 B
      1 B -> 2 R
      2 1 -> 3 R
      3 B -> 3 R
      3 1 -> 4 B
      4 B -> 2 R
*)

Definition div2: Spec := (1, one, 1, W B) ::
                         (1, B  , 2,   R) ::
                         (2, one, 3,   R) ::
                         (3, B  , 3,   R) ::
                         (3, one, 4, W B) ::
                         (4, B  , 2,   R) :: nil.

(************************ Divergence proof ************************)

Fixpoint ones (n:nat) {struct n}: list Sym :=
         match n with
         | 0 => nil
         | (S m) => (cons one (ones m))
         end.

(*
loop from state 3, if Bs on the right
*)

Lemma div2_loops_3B: forall l,
      bi div2 (pair l Bs) 3.
cofix co_hp.
intro. apply biR with 3.
auto.
simpl. apply co_hp.
Qed.

(*
loop from state 2, if an odd number of "1"
*)

Lemma div2_loops_2odd: forall n l,
      bi div2 (pair l (app_ls (ones (2*n + 1)) Bs)) 2.
induction n; intro.

simpl. apply biR with 3.
auto.
simpl. apply div2_loops_3B.

replace (2*S n + 1) with (S (S (2*n + 1))).
simpl. apply biR with 3.
auto.
simpl. apply biW with 4 B.
auto.
simpl. apply biR with 2.
auto.
simpl. replace (n + (n + 0) + 1) with (2*n + 1). apply IHn.
omega. omega.
Qed.

(*
loop from the initial state 1
*)

Lemma div2_loops: forall n,
      bi div2 (pair Bs (Cons one (app_ls (ones (2*n + 1)) Bs))) 1.
intros. apply biW with 1 B.
auto.
simpl. apply biR with 2.
auto.
simpl. replace (n + (n + 0) + 1) with (2*n + 1). apply div2_loops_2odd.
omega.
Qed.
