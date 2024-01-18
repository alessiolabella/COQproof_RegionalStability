Require Import Reals.
Require Import Interval.Tactic.

Open Scope R_scope.

Goal
  forall a, -1 <= a <= 1 ->
   (a-a/(1+Rabs(a)))*(0.52*a -(a-a/(1+Rabs(a))) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a,  1 <= a <= 5 ->
   (1-a/(1+Rabs(a)))*(0.52*a -(1-a/(1+Rabs(a))) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a,  -5 <= a <= -1 ->
   (-1-a/(1+Rabs(a)))*(0.52*a -(-1-a/(1+Rabs(a))) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

