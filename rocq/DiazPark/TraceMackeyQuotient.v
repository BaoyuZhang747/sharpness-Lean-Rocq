From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape MackeyStructures MackeyPair MackeyFusionBridge
  TraceNormalizerCosets TraceMackeySurvivors TraceNormalizerAction.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyTrace DPNormalizerAction.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Section QuotientTrace.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Variable H T : {group S}.
Hypothesis minimal : forall A : {group S}, (#|A| < #|H|)%N ->
  forall x : pair_value M A, x = 0.
Hypothesis hHT : H \subset T.
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.

Theorem self_trace_quotient (x : pair_value M H) :
    pair_pull M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT))
      (pair_push M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT)) x) =
    \sum_(q in (trace_normalizer H T / H)%g) @quotient_action S F R M H x q.
Proof.
rewrite (@self_trace_survivors S F R M H minimal T hHT hM x).
rewrite (reindex (@trace_quotient_to_survivor S H T)
  (onW_bij _ (trace_quotient_survivor_bijective H T))).
rewrite [RHS]big_sub; apply: eq_bigr=> q _.
have hv : val q = coset H
    (double_coset_representative (val (trace_quotient_to_survivor q))).
  rewrite -(trace_survivor_quotient_value (trace_quotient_to_survivor q)).
  by rewrite trace_quotient_survivor_cancel.
rewrite /quotient_action hv (quotient_class_coset F (valP (trace_quotient_to_survivor q))).
reflexivity.
Qed.

End QuotientTrace.

Print Assumptions self_trace_quotient.
