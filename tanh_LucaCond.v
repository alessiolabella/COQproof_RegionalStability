Require Import Reals.
Require Import Interval.Tactic.

Open Scope R_scope.

Goal
  forall a, -1 <= a <= 1 ->
   (a-tanh(a))*(0.23841*a -(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a,  1 <= a <= 5 ->
   (1-tanh(a))*(0.23841*a -(1-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a,  -5 <= a <= -1 ->
   (-1-tanh(a))*(0.23841*a -(-1-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.
