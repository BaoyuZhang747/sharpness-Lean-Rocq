(** Actual singular-to-category-bar cohomology comparison and its literal functorial pullback. The unit-chain comparison is explicitly supplied here. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryComplexIso HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialCochains SimplicialCochainMaps CategoryNerve CategoryConstantCohomology CategoryBarPullbackConstant CategoryNerveCochainBar CategoryNerveCochainBarNaturality
 SingularCohomology TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps ChainQuasiIsomorphism RealizationUnitChains RealizationUnitCochainComparison.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
 DPSimplicialSet DPCategoryNerve DPCategoryBarConstant DPCategoryNerveCochainBar DPCategoryNerveCochainBarNaturality
 DPSingularCohomology DPTopological DPGeometricRealization DPGeometricRealizationMaps DPChainQuasiIsomorphism DPRealizationUnitChains DPRealizationUnitCochainComparison.
Module DPRealizationNerveCohomology.
Section Comparison.
Variable Real:realType.
Variable R:comPzRingType.
Variable A:lmodType R.
Definition classifying_space (C:category) := realization_space Real (nerve C).
Definition comparison_cochain (C:category) : cochain_map (singular_cochains Real (classifying_space C) A) (constant_bar R C A) :=
 cochain_composition (unit_pull Real A (nerve C)) (nerve_bar_cochain_map C A).
Lemma comparison_cochain_natural (C D:category) (F:functor C D) n x :
 cochain_map_at (comparison_cochain C) n (cochain_map_at (singular_pullback Real (realization_map Real (nerve_map F)) A) n x)=
 cochain_map_at (constant_bar_pullback A F) n (cochain_map_at (comparison_cochain D) n x).
Proof.
change (cochain_map_at (nerve_bar_cochain_map C A) n
 (cochain_map_at (unit_pull Real A (nerve C)) n (cochain_map_at (singular_pullback Real (realization_map Real (nerve_map F)) A) n x))=
 cochain_map_at (constant_bar_pullback A F) n (cochain_map_at (nerve_bar_cochain_map D A) n (cochain_map_at (unit_pull Real A (nerve D)) n x))).
rewrite unit_pull_natural; exact: nerve_bar_functor_naturality.
Qed.
Lemma comparison_cohomology_natural (C D:category) (F:functor C D) n x :
 cohomology_map (comparison_cochain C) n (singular_cohomology_map Real (realization_map Real (nerve_map F)) A n x)=
 module_hom_fun (DPCategoryConstantCohomology.pull A F n) (cohomology_map (comparison_cochain D) n x).
Proof.
exact (@cohomology_map_square R _ _ _ _ (singular_pullback Real (realization_map Real (nerve_map F)) A) (constant_bar_pullback A F)
 (comparison_cochain D) (comparison_cochain C) (@comparison_cochain_natural C D F) n x).
Qed.
Variable C:category.
Variable hC:quasi_isomorphism (realization_unit_chains Real R (nerve C)).
Definition comparison_iso n : @isomorphism (module_category R)
 [the lmodType R of singular_cohomology Real (classifying_space C) A n] (DPCategoryConstantCohomology.value R A C n) :=
 module_iso_comp (@unit_cohomology_iso Real R A (nerve C) hC n) (nerve_bar_cohomology_iso C A n).
Lemma comparison_iso_forward n x : module_hom_fun (iso_hom (comparison_iso n)) x=cohomology_map (comparison_cochain C) n x.
Proof.
change (cohomology_map (nerve_bar_cochain_map C A) n
 (module_hom_fun (iso_hom (@unit_cohomology_iso Real R A (nerve C) hC n)) x)=cohomology_map (comparison_cochain C) n x).
rewrite unit_cohomology_iso_forward; symmetry; exact: cohomology_map_composition.
Qed.
End Comparison.
End DPRealizationNerveCohomology.
