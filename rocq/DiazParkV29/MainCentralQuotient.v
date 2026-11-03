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
From DiazParkV29 Require Import SimpleTraceDecomposition SimpleCentralizerSummands
  CompositionReduction ReductionManuscript.
Import GRing.Theory DPFusionOrbit DPCompositionReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

From DiazParkV29 Require Import MainCentralQuotientCore.
Import DPV29CentralQuotientCore.

Module DPV29CentralQuotientSharpness.
Theorem central_quotient_sharpness (S : finGroupType) (F : DPFusionSystem.system S)
    (Z : {group S}) (cZ : DPFusionQuotient.central F Z) (p : nat)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K])
    (quotient_sharp : DPFusionSharpness.sharpness K (DPFusionQuotientConstruction.system cZ)) :
    DPFusionSharpness.sharpness K F.
Proof.
move=> M.
apply (@DPV29MackeyReduction.simple_to_arbitrary_higher_limits S F p pS sat K charp)
  => N simpleN.
have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists simpleN.1.
have simpleP : mackey_simple (DPMackeyFusion.full_mackey_of_inclusions
    (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)).
  by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
have leastP : mackey_least_nonzero (DPMackeyFusion.full_mackey_of_inclusions
    (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)) (fun A : {group S} => #|A|) Q.
  by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
rewrite /positive_centric_limits_zero native_pair_codiagram.
exact (@paired_simple_central_quotient_sharpness S F Z cZ p pS sat K charp quotient_sharp
  (pair_of_mackey N) (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N) simpleP Q leastP).
Qed.
End DPV29CentralQuotientSharpness.


Print Assumptions DPV29CentralQuotientSharpness.central_quotient_sharpness.
