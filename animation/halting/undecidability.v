
Require Import Classical_Prop.

Lemma HM_cannot_exist: False.
elim (classic (halt witness (gamma witness))).
apply witness_stops_absurd. apply witness_loops_absurd.
Qed.