(** v2.9 Lemma 2.9: the manuscript's filtered-colimit and
    composition-factor route, with arbitrary coefficient module values. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionSystems FusionSaturation FusionOrbit FusionMackeyShape
  MackeyStructures MackeySubquotients MackeyPair MackeyPairDiagrams
  MackeyFusionBridge MackeyBarReduction MackeyFiniteLength.
From DiazParkV16b Require Import MackeyFixedDegreeClosure MackeyNoncentricSimpleReduction.
From DiazParkV29 Require Import CompositionSeries CompositionExact CompositionReduction
  CompositionFilteredMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPCompositionReduction.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29MackeyReduction.
Section ArbitraryValues.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].

Theorem noncentric_simple_to_arbitrary_higher_limits
    (h : forall T : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple T -> DPMackeyNoncentricReduction.minimal_subgroups_noncentric T ->
      positive_centric_limits_zero T)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    positive_centric_limits_zero M.
Proof.
move=> n.
apply: DPFilteredLimitsMackey.centric_subfunctor_higher_limit_closure => N hN.
exact (@finite_from_noncentric_simple_hypothesis S F K p pS sat charp h
  (subfunctor_mackey N) hN n).
Qed.

Theorem simple_to_arbitrary_higher_limits
    (h : forall T : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple T -> positive_centric_limits_zero T)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    positive_centric_limits_zero M.
Proof.
apply: noncentric_simple_to_arbitrary_higher_limits => T hT _; exact: h hT.
Qed.

Theorem inclusion_noncentric_simple_to_arbitrary_higher_limits
    (h : forall T : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple T -> DPMackeyNoncentricReduction.minimal_subgroups_noncentric T ->
      positive_centric_limits_zero T)
    (M : mackey_pair K (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@noncentric_simple_to_arbitrary_higher_limits h
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

End ArbitraryValues.

Theorem prime_field_noncentric_simple_reduction
    (S : finGroupType) (F : DPFusionSystem.system S) (p : nat) (hp : prime p)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (h : forall T : mackey_module [the comPzRingType of 'F_p]
        (DPFusionMackey.fusion_mackey_shape F),
      mackey_simple T -> DPMackeyNoncentricReduction.minimal_subgroups_noncentric T ->
      forall n (q : derived_limit [the pzRingType of 'F_p]
        (mackey_codiagram (centric_inclusion F) T) n.+1), q = 0)
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
exact (@inclusion_noncentric_simple_to_arbitrary_higher_limits
  S F p pS sat [the fieldType of 'F_p] (pchar_Fp hp) h M hM).
Qed.
End DPV29MackeyReduction.

Print Assumptions DPV29MackeyReduction.noncentric_simple_to_arbitrary_higher_limits.
Print Assumptions DPV29MackeyReduction.prime_field_noncentric_simple_reduction.


