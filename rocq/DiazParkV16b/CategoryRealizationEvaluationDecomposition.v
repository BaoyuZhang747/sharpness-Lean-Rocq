(** Costructured realization decomposition followed by an actual nerve equivalence.
    Every geometric map is the realization of the literal projection/evaluation composite. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryModules CategoryModuleLimits CategoryComma.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve
 ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialChainsMaps
 SimplicialReplacementConstants SimplicialReplacementAugmentation CategoryCostructuredDiagram CategoryCostructuredRowAugmentation CategoryCostructuredAugmentationPoly
 TopologicalCategory SingularCohomology GeometricRealizationCarrier GeometricRealizationMaps RealizationTopologicalCocone RealizationTopologicalAugmentation
 SingularCochainReplacementEdge SingularReplacementGeometricComparison SingularReplacementGeometricEdge SingularReplacementGeometricConvergence.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialChainMaps
 DPSimplicialReplacementConstants DPSimplicialReplacementAugmentation DPCategoryCostructuredDiagram DPCategoryCostructuredRowAugmentation DPCategoryCostructuredAugmentationPoly
 DPTopological DPSingularCohomology DPGeometricRealization DPGeometricRealizationMaps DPRealizationTopologicalCocone DPRealizationTopologicalAugmentation
 DPSingularReplacementEdge DPSingularReplacementGeometricComparison DPSingularReplacementGeometricEdge DPSingularReplacementGeometricConvergence.
Module DPCategoryRealizationEvaluationDecomposition.
Section Decomposition.
Variable Real:realType.
Variables C D B:category.
Variable T:functor C D.
Variable E:functor C B.
Definition evaluation_nerve_cocone : nat_trans (costructured_nerve_diagram T) (@constant_diagram D simplicial_category (nerve B)).
Proof.
refine (@Build_nat_trans D simplicial_category (costructured_nerve_diagram T) (@constant_diagram D simplicial_category (nerve B))
 (fun d=>nat_comp (costructured_projection_nerve T d) (nerve_map E)) _).
move=>d e f; apply nat_trans_ext=>n; apply type_morphism_ext=>s.
change (component (nerve_map E) n (component (costructured_projection_nerve T e) n (component (fmap (costructured_nerve_diagram T) f) n s))=
 component (nerve_map E) n (component (costructured_projection_nerve T d) n s)).
by rewrite projection_nerve_natural.
Defined.
Definition space_diagram : functor D topological_category := functor_comp (costructured_nerve_diagram T) (realization_functor Real).
Definition space_cocone := realized_cocone Real evaluation_nerve_cocone.
Theorem space_cocone_component d : component space_cocone d =
 realization_map Real (nerve_map (functor_comp (costructured_projection T d) E)).
Proof.
change (realization_map Real (nat_comp (costructured_projection_nerve T d) (nerve_map E))=
 realization_map Real (nerve_map (functor_comp (costructured_projection T d) E))).
apply f_equal; apply nat_trans_ext=>n; apply type_morphism_ext=>s.
change (functor_comp (functor_comp s (costructured_projection T d)) E=functor_comp s (functor_comp (costructured_projection T d) E)).
exact: functor_comp_assoc.
Qed.
Variable R:comPzRingType.
Variable hE:quasi_isomorphism (chain_map_of R (nerve_map E)).
Theorem evaluation_augmentation_quasi_isomorphism :
 quasi_isomorphism (chain_map_of R (diagonal_coefficient_augmentation evaluation_nerve_cocone)).
Proof.
apply (@quasi_isomorphism_ext R _ _
 (chain_composition (chain_map_of R (diagonal_augmentation T)) (chain_map_of R (nerve_map E)))
 (chain_map_of R (diagonal_coefficient_augmentation evaluation_nerve_cocone))).
- move=>n x; change (map_at R (nerve_map E) n (map_at R (diagonal_augmentation T) n x)=map_at R (diagonal_coefficient_augmentation evaluation_nerve_cocone) n x).
  rewrite -map_composition.
  have he:nat_comp (diagonal_augmentation T) (nerve_map E)=diagonal_coefficient_augmentation evaluation_nerve_cocone.
    apply nat_trans_ext=>k; apply type_morphism_ext=>[[s y]]; reflexivity.
  by rewrite he.
- apply quasi_isomorphism_composition; [exact: diagonal_augmentation_quasi_isomorphism | exact hE].
Qed.
Theorem singular_augmentation_quasi_isomorphism :
 quasi_isomorphism (chain_map_of R (singular_geometric_augmentation Real space_cocone)).
Proof. apply realized_cocone_augmentation_quasi_isomorphism; exact: evaluation_augmentation_quasi_isomorphism. Qed.
Variable A:lmodType R.
Definition total_cohomology_iso n :=
 @singular_geometric_cohomology_iso Real R A D space_diagram (realization_space Real (nerve B)) space_cocone singular_augmentation_quasi_isomorphism n.
Definition finite_convergence_iso p n :=
 @singular_geometric_finite_convergence_iso Real R A D space_diagram (realization_space Real (nerve B)) space_cocone singular_augmentation_quasi_isomorphism p n.
Variable h:singular_positive_limits_vanish Real A space_diagram.
Definition limit_iso n :=
 @singular_geometric_limit_iso Real R A D space_diagram (realization_space Real (nerve B)) space_cocone singular_augmentation_quasi_isomorphism h n.
Theorem limit_iso_component n z d :
 module_limit_val (module_hom_fun (iso_hom (limit_iso n)) z) d=
 singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (costructured_projection T d) E))) A n z.
Proof. rewrite -space_cocone_component; exact: singular_geometric_limit_iso_component. Qed.
End Decomposition.
End DPCategoryRealizationEvaluationDecomposition.
