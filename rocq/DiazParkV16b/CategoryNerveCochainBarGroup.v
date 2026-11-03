(** The actual nerve/bar equivalence specializes to the native group cohomology complex and its maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialCochains SimplicialCochainMaps CategoryNerve
  CategoryNerveCochainBar CategoryNerveCochainBarNaturality GroupCohomologyBase
  GroupCohomologyFunctor GroupCohomologyPullback GroupCohomologyCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPSimplicialCochains DPSimplicialCochainMaps DPCategoryNerve
  DPCategoryNerveCochainBar DPCategoryNerveCochainBarNaturality
  DPGroupCohomology DPGroupCohomologyFunctor.

Module DPCategoryNerveCochainBarGroup.
Section Groups.
Variable R : comPzRingType.
Variable A : lmodType R.
Definition group_nerve_cochain_map (G : finGroupType) :
    cochain_map (DPSimplicialCochains.complex (nerve (group_category G)) A)
      (DPGroupCohomology.complex R G A) := nerve_bar_cochain_map (group_category G) A.
Definition group_nerve_cochain_inverse (G : finGroupType) :
    cochain_map (DPGroupCohomology.complex R G A)
      (DPSimplicialCochains.complex (nerve (group_category G)) A) :=
  bar_nerve_cochain_map (group_category G) A.
Definition group_nerve_cohomology_iso (G : finGroupType) n :
    @isomorphism (module_category R)
      [the lmodType R of cohomology (DPSimplicialCochains.complex (nerve (group_category G)) A) n]
      (value R G A n) := nerve_bar_cohomology_iso (group_category G) A n.
Theorem group_nerve_pull_cochain (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n a :
  cochain_map_at (group_nerve_cochain_map G) n
    (cochain_map_at (DPSimplicialCochainMaps.pull (nerve_map (group_functor f)) A) n a) =
  cochain_map_at (DPGroupCohomologyPullback.pull_cochain A f) n
    (cochain_map_at (group_nerve_cochain_map H) n a).
Proof. exact: nerve_bar_functor_naturality. Qed.
Theorem group_nerve_pull_cohomology (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n a :
  cohomology_map (group_nerve_cochain_map G) n
    (cohomology_map (DPSimplicialCochainMaps.pull (nerve_map (group_functor f)) A) n a) =
  DPGroupCohomologyPullback.pull A f n (cohomology_map (group_nerve_cochain_map H) n a).
Proof. exact: nerve_bar_functor_cohomology. Qed.
End Groups.
Section Coefficients.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables A B : lmodType R.
Variable u : module_hom A B.
Theorem group_nerve_coefficient_cochain n a :
  cochain_map_at (group_nerve_cochain_map B G) n
    (cochain_map_at (coefficient (nerve (group_category G)) (module_hom_to_linear u)) n a) =
  cochain_map_at (DPGroupCohomologyCoefficients.coefficient_cochain_map G u) n
    (cochain_map_at (group_nerve_cochain_map A G) n a).
Proof. exact: nerve_bar_coefficient_naturality. Qed.
Theorem group_nerve_coefficient_cohomology n a :
  cohomology_map (group_nerve_cochain_map B G) n
    (cohomology_map (coefficient (nerve (group_category G)) (module_hom_to_linear u)) n a) =
  DPGroupCohomologyCoefficients.coefficient_map G u n
    (cohomology_map (group_nerve_cochain_map A G) n a).
Proof. exact: nerve_bar_coefficient_cohomology. Qed.
End Coefficients.
End DPCategoryNerveCochainBarGroup.
