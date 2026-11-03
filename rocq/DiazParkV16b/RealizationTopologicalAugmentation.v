(** The actual topological realization cocone has a singular augmentation quasi-isomorphism whenever its actual nerve augmentation does. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve
 ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialChains SimplicialChainsMaps
 BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyNaturality
 SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementMaps SimplicialReplacementConstants SimplicialReplacementAugmentation SimplicialReplacementComparisonPoly
 SingularSet TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSingularAdjunction
 RealizationUnitChains RealizationUnitComparison RealizationTopologicalCocone SingularReplacementGeometricComparison.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialChains DPSimplicialChainMaps
 DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyNaturality DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementMaps DPSimplicialReplacementConstants DPSimplicialReplacementAugmentation DPSimplicialReplacementComparisonPoly
 DPSingularSet DPTopological DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction DPRealizationUnitChains DPRealizationUnitComparison DPRealizationTopologicalCocone DPSingularReplacementGeometricComparison.
Module DPRealizationTopologicalAugmentation.
Section Augmentation.
Variable Real:realType.
Variable R:pzRingType.
Variable C:category.
Variable F:functor C simplicial_category.
Local Notation SF := (functor_comp (functor_comp F (realization_functor Real)) (singular_functor Real)).
Definition topological_diagram_unit : nat_trans F SF.
Proof.
refine (@Build_nat_trans C simplicial_category F SF (fun c=>realization_unit_map Real (fobj F c)) _).
move=>c d f; exact: realization_unit_natural.
Defined.
Definition topological_replacement_unit := diagonal_map (replacement_map topological_diagram_unit).
Theorem topological_replacement_unit_quasi_isomorphism : quasi_isomorphism (chain_map_of R topological_replacement_unit).
Proof.
apply (@replacement_diagonal_quasi_isomorphism R C F SF topological_diagram_unit).
move=>c; exact: realization_unit_quasi_isomorphism.
Qed.
Variable X:simplicial_set.
Variable a:nat_trans F (@constant_diagram C simplicial_category X).
Lemma topological_augmentation_unit_square :
 nat_comp topological_replacement_unit (singular_geometric_augmentation Real (realized_cocone Real a))=
 nat_comp (diagonal_coefficient_augmentation a) (realization_unit_map Real X).
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[s x]].
exact (Logic.eq_sym (f_equal (fun z:simplicial_map (fobj F (initial_object s)) (singular_set Real (realization_space Real X))=>component z n x)
 (realization_unit_natural Real (component a (initial_object s))))).
Qed.
Theorem realized_cocone_augmentation_quasi_isomorphism
 (ha:quasi_isomorphism (chain_map_of R (diagonal_coefficient_augmentation a))) :
 quasi_isomorphism (chain_map_of R (singular_geometric_augmentation Real (realized_cocone Real a))).
Proof.
apply (@quasi_isomorphism_cancel_first R _ _ _ (chain_map_of R topological_replacement_unit)
 (chain_map_of R (singular_geometric_augmentation Real (realized_cocone Real a)))); first exact: topological_replacement_unit_quasi_isomorphism.
apply (@quasi_isomorphism_ext R _ _
 (chain_composition (chain_map_of R (diagonal_coefficient_augmentation a)) (realization_unit_chains Real R X))
 (chain_composition (chain_map_of R topological_replacement_unit) (chain_map_of R (singular_geometric_augmentation Real (realized_cocone Real a))))).
- move=>n x; change (map_at R (realization_unit_map Real X) n (map_at R (diagonal_coefficient_augmentation a) n x)=
 map_at R (singular_geometric_augmentation Real (realized_cocone Real a)) n (map_at R topological_replacement_unit n x)).
  by rewrite -!map_composition topological_augmentation_unit_square.
- apply quasi_isomorphism_composition; [exact ha | exact: realization_unit_quasi_isomorphism].
Qed.
End Augmentation.
End DPRealizationTopologicalAugmentation.
