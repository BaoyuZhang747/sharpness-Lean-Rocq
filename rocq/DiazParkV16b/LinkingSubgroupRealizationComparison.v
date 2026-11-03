(** Actual subgroup diagram, singular replacement augmentation, and geometric coefficient comparison. Uniform unit comparison is explicit until its separate construction is applied. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryNaturalIso CategoryModules CategoryDerivedLimits HomologicalComplex HomologicalCohomologyMaps HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory LinkingCommaCohomology LinkingCommaCohomologyDiagram LinkingCommaCohomologyNatIso GroupCohomologyOrbitCoefficient
 SimplicialSet SimplicialSetYoneda CategoryNerve CategoryCostructuredDiagram CategoryCostructuredRowAugmentation CategoryCostructuredAugmentationPoly
 ChainQuasiIsomorphism SimplicialChainsMaps SingularCohomology TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
 RealizationUnitChains RealizationReplacementUnit RealizationUnitCohomologyDiagram RealizationNerveCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomologyMaps DiazParkHomologicalModuleIso
 DPCentricLinking DPLinkingOrbit DPLinkingComma DPSimplicialSet DPSimplicialYoneda DPCategoryNerve
 DPCategoryCostructuredDiagram DPCategoryCostructuredRowAugmentation DPCategoryCostructuredAugmentationPoly
 DPChainQuasiIsomorphism DPSimplicialChainMaps DPSingularCohomology DPTopological DPGeometricRealization DPGeometricRealizationMaps DPRealizationUnitChains
 DPRealizationReplacementUnit DPRealizationUnitCohomologyDiagram DPRealizationNerveCohomology.
Module DPLinkingSubgroupRealizationComparison.
Section Diagram.
Variable Real:realType.
Variable S:finGroupType.
Variable F:DPFusionSystem.system S.
Variable L:DPCentricLinking.system F.
Local Notation O := (DPFusionOrbit.centric_orbit_category F).
Definition subgroup_nerve_diagram : functor O simplicial_category := costructured_nerve_diagram (orbit_projection L).
Definition subgroup_space_diagram : functor O topological_category := functor_comp subgroup_nerve_diagram (realization_functor Real).
Definition subgroup_singular_augmentation := singular_diagonal_augmentation Real (projection_cocone (orbit_projection L)).
Lemma actual_reindex (P Q:O) (f:hom O P Q) : reindex (orbit_projection L) f=subgroup_comma_map L f.
Proof.
apply (@functor_extensionality _ _ (reindex (orbit_projection L) f) (subgroup_comma_map L f) Logic.eq_refl); reflexivity.
Qed.

Variable R:comPzRingType.
Variable hunit:forall X:simplicial_set, quasi_isomorphism (realization_unit_chains Real R X).
Theorem subgroup_singular_augmentation_quasi_isomorphism : quasi_isomorphism (chain_map_of R subgroup_singular_augmentation).
Proof.
apply (@singular_augmentation_quasi_isomorphism Real R O subgroup_nerve_diagram
 (fun P=>hunit (fobj subgroup_nerve_diagram P)) (nerve (linking_category L)) (projection_cocone (orbit_projection L))
 (hunit (nerve (linking_category L)))).
exact: diagonal_augmentation_quasi_isomorphism.
Qed.

Variable A:lmodType R.
Variable n:nat.
Definition subgroup_singular_coefficient := realized_cohomology_diagram Real A subgroup_nerve_diagram n.
Local Notation CC := (DPLinkingCommaCohomologyDiagram.coefficient L A n).
Definition subgroup_comma_cohomology_iso (P:O) := @comparison_iso Real R A (subgroup_comma L P) (hunit (nerve (subgroup_comma L P))) n.
Lemma subgroup_comma_cohomology_natural (P Q:O) (f:hom O P Q) :
 module_hom_comp (@fmap _ _ subgroup_singular_coefficient Q P f) (iso_hom (subgroup_comma_cohomology_iso P))=
 module_hom_comp (iso_hom (subgroup_comma_cohomology_iso Q)) (@fmap _ _ CC Q P f).
Proof.
apply module_hom_ext=>x.
change (module_hom_fun (iso_hom (subgroup_comma_cohomology_iso P))
 (singular_cohomology_map Real (realization_map Real (nerve_map (reindex (orbit_projection L) f))) A n x)=
 module_hom_fun (DPLinkingCommaCohomology.pull A L f n) (module_hom_fun (iso_hom (subgroup_comma_cohomology_iso Q)) x)).
rewrite /subgroup_comma_cohomology_iso !comparison_iso_forward actual_reindex.
exact: comparison_cohomology_natural.
Qed.
Definition subgroup_comma_cohomology_nat_iso : @isomorphism (functor_category (opposite O) (module_category R)) subgroup_singular_coefficient CC :=
 @nat_iso_of_components (opposite O) (module_category R) subgroup_singular_coefficient CC subgroup_comma_cohomology_iso
 (fun P Q f=>@subgroup_comma_cohomology_natural Q P f).
Definition subgroup_native_higher_limit_iso j : @isomorphism (module_category R)
 (derived_limit R subgroup_singular_coefficient j)
 (derived_limit R (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j) :=
 module_iso_comp (functor_iso (derived_limit_functor R (opposite O) j) subgroup_comma_cohomology_nat_iso)
 (@DPLinkingCommaCohomologyNatIso.higher_limit_iso R A S F L n j).
End Diagram.
End DPLinkingSubgroupRealizationComparison.
