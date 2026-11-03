(** Actual diagonal-to-total augmentation comparison using the polymorphic AW equivalence. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  SimplicialSet SimplicialSetYoneda SimplicialChains SimplicialChainsMaps BisimplicialChains
  BisimplicialAlexanderWhitneyChain BisimplicialAlexanderWhitneyEquivalencePoly
  SimplicialReplacementConstants SimplicialReplacement SimplicialReplacementAugmentation
  SimplicialReplacementCoconeTotal SimplicialReplacementCoconeDual ChainDualCochain
  CategoryCochainReplacementSimplicialEvaluation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPBisimplicialChains
  DPAlexanderWhitneyChain DPAlexanderWhitneyEquivalencePoly DPSimplicialReplacementConstants
  DPSimplicialReplacement DPSimplicialReplacementAugmentation DPSimplicialReplacementCoconeTotal
  DPSimplicialReplacementCoconeDual DPChainDualCochain DPCategoryCochainReplacementSimplicialEvaluation
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Module DPSimplicialReplacementCoconeQuasiIso.
Section Chains.
Variable R : pzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable X : simplicial_set.
Variable a : nat_trans F (@constant_diagram C simplicial_category X).
Theorem cocone_total_augmentation_quasi_isomorphism
  (ha : quasi_isomorphism (chain_map_of R (diagonal_coefficient_augmentation a))) :
  quasi_isomorphism (cocone_total_augmentation R a).
Proof.
apply (@quasi_isomorphism_cancel_first R _ _ _
  (alexander_whitney R (replacement F)) (cocone_total_augmentation R a)).
- exact (@alexander_whitney_quasi_isomorphism R (replacement F)).
- apply (@quasi_isomorphism_ext R _ _ (chain_map_of R (diagonal_coefficient_augmentation a))
    (chain_composition (alexander_whitney R (replacement F)) (cocone_total_augmentation R a))).
  + move=> n z; symmetry; exact: cocone_total_augmentation_triangle.
  + exact ha.
Qed.
End Chains.

Section Cochains.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable X : simplicial_set.
Variable a : nat_trans F (@constant_diagram C simplicial_category X).
Variable A : lmodType R.
Variable ha : quasi_isomorphism (chain_map_of R (diagonal_coefficient_augmentation a)).
Definition cocone_dual_iso_of_diagonal n :=
  cocone_dual_cohomology_iso A (cocone_total_augmentation_quasi_isomorphism ha) n.
Theorem cocone_dual_iso_of_diagonal_hom n (z : cohomology (@dual_complex R A (chains R X)) n) :
  module_hom_fun (iso_hom (cocone_dual_iso_of_diagonal n)) z =
  cohomology_map (cocone_dual_comparison a A) n z.
Proof. exact: cocone_dual_cohomology_iso_hom. Qed.
Theorem cocone_dual_iso_of_diagonal_restriction n (z : cohomology (@dual_complex R A (chains R X)) n) c :
  cohomology_map (dual_replacement_projection F A c) n
    (module_hom_fun (iso_hom (cocone_dual_iso_of_diagonal n)) z) =
  cohomology_map (dual_map A (chain_map_of R (component a c))) n z.
Proof. exact: cocone_dual_cohomology_iso_restriction. Qed.
End Cochains.
End DPSimplicialReplacementCoconeQuasiIso.
