(** The exact canonical inclusion-Mackey formula for native ordinary cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape FusionMackeyRepresentatives MackeyStructures MackeyPair MackeyFusionBridge.
From DiazParkV16b Require Import GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyHomogeneousRestriction GroupCohomologyHomogeneousConjugation
  GroupCohomologyTransferNative GroupCohomologyTransferDoubleCoset
  GroupCohomologyCosetSumsDoubleCosets GroupCohomologyMackeyPushBase
  GroupCohomologyMackeyInclusions GroupCohomologyMackeyPair
  GroupCohomologyMackeyDoubleCosetIndices GroupCohomologyMackeyDoubleCosetGeometry
  GroupCohomologyMackeyDoubleCosetTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyPullback DPGroupCohomologyOrbitCoefficient
  DPGroupCohomologyHomogeneousRestriction DPGroupCohomologyHomogeneousConjugation
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferDoubleCoset
  DPGroupCohomologyCosetSumsDoubleCosets DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyInclusions DPGroupCohomologyMackeyPair
  DPGroupCohomologyMackeyDoubleCosetIndices DPGroupCohomologyMackeyDoubleCosetGeometry
  DPGroupCohomologyMackeyDoubleCosetTerms.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologyMackeyDoubleCosetShape.
Section Shape.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation M := (native_cohomology_pair F A n).

Theorem native_inclusion_mackey_formula : DPMackeyFusion.inclusion_mackey_formula M.
Proof.
move=> P Q T hP hQ z.
rewrite native_pair_pull_class native_pair_push_class raw_push_inclusion raw_pull_inclusion.
change (module_hom_fun (pull A (subgroup_nested_hom hQ) n)
    (module_hom_fun (transfer A hP n) z) =
  \sum_(i : DPFusionMackey.double_coset_index P Q T)
    @DPMackeyRepresentatives.inclusion_summand S F R M P Q
      (DPFusionMackey.double_coset_representative i) z).
rewrite transfer_double_coset [LHS]big_sub.
rewrite [RHS](reindex (to_canonical hP hQ)); last exact: onW_bij (to_canonical_bijective hP hQ).
apply: eq_bigr=> D _.
change (module_hom_fun (transfer A (intersection_sub_Q P Q (double_coset_repr P (val D))) n)
  (module_hom_fun (pull A
    (@subgroup_conjugation_hom S (intersection P Q (double_coset_repr P (val D))) P
      (double_coset_repr P (val D)) (intersection_sub_conjugate P Q (double_coset_repr P (val D)))) n) z) =
  @DPMackeyRepresentatives.inclusion_summand S F R M P Q
    (DPFusionMackey.double_coset_representative (to_canonical hP hQ D)) z).
rewrite -(@canonical_summand_native S F R A n P Q (double_coset_repr P (val D)) z).
refine (@DPMackeyRepresentatives.same_double_coset_summand S F R M P Q
  (double_coset_repr P (val D))
  (DPFusionMackey.double_coset_representative (to_canonical hP hQ D)) _ z).
rewrite (native_representative_set hP hQ D).
exact: esym (DPFusionMackey.double_coset_representative_set _).
Qed.

End Shape.
End DPGroupCohomologyMackeyDoubleCosetShape.
