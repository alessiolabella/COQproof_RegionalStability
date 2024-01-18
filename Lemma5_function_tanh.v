Require Import Reals.
Require Import Interval.Tactic.

Open Scope R_scope.

Goal
  forall a, 0 <= a <= 2.9847 ->
   (a-tanh(a))*(tanh(a) -0.5*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a, -2.9847 <= a <= 0 ->
   (a-tanh(a))*(tanh(a) -0.5*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.


Goal
  forall a, 0 <= a <= 1.915 ->
   (a-tanh(a))*(tanh(a) -1*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a, -1.915 <= a <= 0 ->
   (a-tanh(a))*(tanh(a) -1*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a, 0 <= a <= 1.2878 ->
   (a-tanh(a))*(tanh(a) -2*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.

Goal
  forall a, -1.2878 <= a <= 0 ->
   (a-tanh(a))*(tanh(a) -2*(a-tanh(a)) ) >= -0.000000000001.
Proof.
  intros.
  interval with (i_bisect a, i_taylor a, i_degree 1).
Qed.
