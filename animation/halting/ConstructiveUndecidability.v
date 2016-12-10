
Require Import Unicode.Utf8.

Require Import halting_defs.
Require Import halt_not_halt.
Require Import not_halt_halt.
Require Import witness.

(* Principle of non-contradiction *)
Theorem pnc {A : Prop} : A → ¬ A → False.
  auto.
Qed.

Lemma HM_cannot_exist: False.
  apply (pnc witness_stops_absurd witness_loops_absurd).
Qed.
