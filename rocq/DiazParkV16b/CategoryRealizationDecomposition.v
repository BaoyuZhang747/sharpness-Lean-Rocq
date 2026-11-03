(** Actual classifying-space decomposition for every functor, with no assumed realization comparison. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SimplicialSet CategoryNerve
 ChainQuasiIsomorphism SimplicialChainsMaps SimplicialReplacementConstants SimplicialReplacementAugmentation
 CategoryCostructuredDiagram CategoryCostructuredRowAugmentation CategoryCostructuredAugmentationPoly
 GeometricRealizationCarrier GeometricRealizationMaps RealizationTopologicalCocone RealizationTopologicalAugmentation
 SingularCochainReplacementEdge SingularReplacementGeometricComparison SingularReplacementGeometricEdge SingularReplacementGeometricConvergence.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSimplicialSet DPCategoryNerve DPChainQuasiIsomorphism DPSimplicialChainMaps
 DPSimplicialReplacementConstants DPSimplicialReplacementAugmentation DPCategoryCostructuredDiagram DPCategoryCostructuredRowAugmentation DPCategoryCostructuredAugmentationPoly
 DPGeometricRealization DPGeometricRealizationMaps DPRealizationTopologicalCocone DPRealizationTopologicalAugmentation
 DPSingularReplacementEdge DPSingularReplacementGeometricComparison DPSingularReplacementGeometricEdge DPSingularReplacementGeometricConvergence.
Module DPCategoryRealizationDecomposition.
Section Decomposition.
Variable Real:realType.
Variables C D:category.
Variable T:functor C D.
Definition space_diagram : functor D topological_category := functor_comp (costructured_nerve_diagram T) (realization_functor Real).
Definition space_cocone := realized_cocone Real (projection_cocone T).
Definition singular_augmentation := singular_geometric_augmentation Real space_cocone.
Theorem singular_augmentation_quasi_isomorphism (R:pzRingType) : quasi_isomorphism (chain_map_of R singular_augmentation).
Proof.
apply (@realized_cocone_augmentation_quasi_isomorphism Real R D (costructured_nerve_diagram T)
 (nerve C) (projection_cocone T)).
exact: diagonal_augmentation_quasi_isomorphism.
Qed.
Variable R:comPzRingType.
Variable A:lmodType R.
Definition total_cohomology_iso n :=
 @singular_geometric_cohomology_iso Real R A D space_diagram (realization_space Real (nerve C))
 space_cocone (singular_augmentation_quasi_isomorphism R) n.
Definition finite_convergence_iso p n :=
 @singular_geometric_finite_convergence_iso Real R A D space_diagram (realization_space Real (nerve C))
 space_cocone (singular_augmentation_quasi_isomorphism R) p n.
Variable h : singular_positive_limits_vanish Real A space_diagram.
Definition limit_iso n :=
 @singular_geometric_limit_iso Real R A D space_diagram (realization_space Real (nerve C))
 space_cocone (singular_augmentation_quasi_isomorphism R) h n.
Theorem limit_iso_component n z d :
 module_limit_val (module_hom_fun (iso_hom (limit_iso n)) z) d =
 singular_cohomology_map Real (component space_cocone d) A n z.
Proof. exact: singular_geometric_limit_iso_component. Qed.
End Decomposition.
End DPCategoryRealizationDecomposition.
