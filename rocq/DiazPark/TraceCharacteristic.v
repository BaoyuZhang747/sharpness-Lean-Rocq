From mathcomp Require Import all_boot all_algebra.

(** Finite trace regrouping and characteristic cancellation.

    The coefficient additive group is arbitrary: no finite carrier, basis,
    dimension, or finite-generation hypothesis occurs.  Only index types
    are finite.  The first section is independent of any scalar ring. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteTrace.

Variable V : zmodType.

(** Regroup a genuine finite sum along a map of finite index types.
    The multiplicity is the cardinality of the actual fiber. *)
Lemma trace_fiber_regroup (I J : finType) (q : I -> J)
    (f : I -> V) (g : J -> V) :
    (forall i, f i = g (q i)) ->
    \sum_(i : I) f i =
      \sum_(j : J) g j *+ #|[pred i : I | q i == j]|.
Proof.
move=> hf.
rewrite (partition_big q predT) //=.
apply: eq_bigr => j _.
rewrite (eq_bigr (fun _ => g j)).
- exact: sumr_const.
- by move=> i /eqP hij; rewrite hf hij.
Qed.

(** The equal-fiber form used by the normalizer quotient trace. *)
Lemma trace_uniform_fiber_regroup (I J : finType) (q : I -> J)
    (f : I -> V) (g : J -> V) (d : nat) :
    (forall i, f i = g (q i)) ->
    (forall j, #|[pred i : I | q i == j]| = d) ->
    \sum_(i : I) f i = (\sum_(j : J) g j) *+ d.
Proof.
move=> hf hcard.
rewrite (trace_fiber_regroup hf) -sumrMnl.
by apply: eq_bigr => j _; rewrite hcard.
Qed.

Variable p : nat.
Hypothesis p_torsion : forall v : V, v *+ p = 0.

(** Divisibility cancellation for the underlying additive group. *)
Lemma trace_dvdn_mul_zero n (v : V) : (p %| n)%N -> v *+ n = 0.
Proof.
by move/dvdnP=> [m ->]; rewrite mulrnA p_torsion.
Qed.

Lemma trace_constant_sum_zero (I : finType) (A : pred I) (v : V) :
    (p %| #|A|)%N -> \sum_(i in A) v = 0.
Proof.
by move=> hA; rewrite sumr_const (trace_dvdn_mul_zero v hA).
Qed.

(** Every term is an explicitly specified function of the fiber label.
    No trace-vanishing assumption appears in the hypotheses. *)
Lemma trace_fiber_sum_zero (I J : finType) (q : I -> J)
    (f : I -> V) (g : J -> V) :
    (forall i, f i = g (q i)) ->
    (forall j, (p %| #|[pred i : I | q i == j]|)%N) ->
    \sum_(i : I) f i = 0.
Proof.
move=> hf hcard.
rewrite (trace_fiber_regroup hf).
apply: big1 => j _.
exact: trace_dvdn_mul_zero (hcard j).
Qed.

End FiniteTrace.

Section ScalarCharacteristic.

Variable R : pzRingType.
Variable V : lmodType R.
Variable p : nat.
Hypothesis p_scalar_zero : p%:R = (0 : R).

(** The scalar characteristic assumption implies additive p-torsion for
    every element, without any restriction on the module's dimension. *)
Lemma trace_char_mul_zero (v : V) : v *+ p = 0.
Proof.
by rewrite -scaler_nat p_scalar_zero scale0r.
Qed.

Lemma trace_char_dvdn_mul_zero n (v : V) :
    (p %| n)%N -> v *+ n = 0.
Proof.
exact (@trace_dvdn_mul_zero _ p trace_char_mul_zero n v).
Qed.

Lemma trace_char_fiber_sum_zero (I J : finType) (q : I -> J)
    (f : I -> V) (g : J -> V) :
    (forall i, f i = g (q i)) ->
    (forall j, (p %| #|[pred i : I | q i == j]|)%N) ->
    \sum_(i : I) f i = 0.
Proof.
exact (@trace_fiber_sum_zero _ p trace_char_mul_zero I J q f g).
Qed.

End ScalarCharacteristic.

Print Assumptions trace_fiber_regroup.
Print Assumptions trace_fiber_sum_zero.
Print Assumptions trace_char_mul_zero.
Print Assumptions trace_char_fiber_sum_zero.
