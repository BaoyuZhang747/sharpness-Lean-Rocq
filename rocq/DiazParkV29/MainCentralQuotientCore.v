(** v2.9 central-quotient step.  The missing-centre branch uses the new
    trace-image decomposition and zero summand.  The containing-centre
    branch reuses the proved actual quotient Mackey construction. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  CategoryDerivedZero CategoryAtomicDeletionTheorem
  FusionSystems FusionOrbit FusionSaturation FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientCollection FusionMackeyQuotientCoefficients FusionMackeyQuotientVanishing
  FusionCollectionRestrictionAdapter FusionSharpnessStatement FusionCentralQuotientSharpness
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyDiagramIdentities MackeyFusionMinimal FusionMackeyFullBridge.
From DiazParkV29 Require Import SimpleFunctor SimpleManuscript
  CompositionReduction.
Import GRing.Theory DPFusionOrbit DPCompositionReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29CentralQuotientCore.
Section Descent.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].
Hypothesis quotient_sharp : DPFusionSharpness.sharpness K (DPFusionQuotientConstruction.system cZ).
Let pZ : p.-group Z := pgroupS (subsetT Z) pS.
Variable M : mackey_pair K (orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.

Lemma minimalQ : DPMackeyMinimal.subgroup_minimal full Q.
Proof.
split; first exact: leastQ.1.
move=> U hU x; apply: leastQ.2; exact: proper_card hU.
Qed.

Lemma missing_centre_value_zero (missingZ : ~~ (Z \subset Q)) (P : {group S})
    (centricP : DPFusionSystem.centric F P) (x : pair_value M P) : x = 0.
Proof.
apply: (@DPSimpleFunctor.simple_functor_restriction_detection
  S F K full simple Q minimalQ P x) => L hLP hQL.
exact (@DPSimpleManuscript.simple_functor_centralizer_restriction_zero
  S F K full simple Q minimalQ L P hLP hQL p (pcharf0 charp)
  (pgroupS (subsetT P) pS)
  (@DPFusionMackeyQuotientVanishing.minimal_centralizer_noncontained
    S F Z cZ Q missingZ P L centricP hLP hQL) x).
Qed.

Theorem paired_simple_central_quotient_sharpness :
    derived_positive_zero (pair_codiagram (pair_restrict M (centric_inclusion F))).
Proof.
case: (boolP (Z \subset Q)) => [sZQ|missingZ].
- apply (proj2 (DPFusionCollectionAdapter.literal_collection_acyclic_iff cZ pS pZ sat _)).
  rewrite DPFusionCentralQuotientSharpness.literal_pair_restriction.
  exact (@DPFusionCentralQuotientSharpness.containing_simple_collection_zero
    S F Z cZ p pS sat K charp quotient_sharp M hM simple Q leastQ sZQ).
- move=> n; apply: pointwise_zero_derived_limits => P x.
  exact (@missing_centre_value_zero missingZ (val P) (valP P) x).
Qed.

End Descent.

End DPV29CentralQuotientCore.

Print Assumptions DPV29CentralQuotientCore.missing_centre_value_zero.
Print Assumptions DPV29CentralQuotientCore.paired_simple_central_quotient_sharpness.

