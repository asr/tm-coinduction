
Require Import Classical_Prop.

Require Import halting_defs.
Require Import halt_not_halt.
Require Import not_halt_halt.
Require Import witness.

Lemma HM_cannot_exist: False.
elim (classic (halt witness (gamma witness))).
apply witness_stops_absurd. apply witness_loops_absurd.
Qed.
