(** The actual geometric infinite-stage passage. Only the finite-skeleton
    homology comparison remains as an explicit induction input here. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialSkeleton SingularSet
  TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
  GeometricRealizationSkeletonSeparation GeometricRealizationSkeletonCompact
  ChainQuasiIsomorphism RealizationUnitChains RealizationUnitExhaustive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPRealizationUnitSkeletonPassage.
Import DPSimplicialSet DPSimplicialSkeleton DPSingularSet DPTopological
  DPGeometricRealization DPGeometricRealizationMaps DPRealizationSkeletonSeparation
  DPRealizationSkeletonCompact DPChainQuasiIsomorphism DPRealizationUnitChains
  DPRealizationUnitExhaustive.

Theorem actual_realization_unit_quasi_iso_of_skeleta (Real : realType) (R : pzRingType)
  (X : simplicial_set)
  (hstage : forall k, quasi_isomorphism (realization_unit_chains Real R (skeleton_set X k))) :
  quasi_isomorphism (realization_unit_chains Real R X).
Proof.
apply (@realization_unit_quasi_iso_of_skeleta Real R X).
- exact: actual_skeleton_inclusion_injective.
- move=> d s.
  have [k [t ht]] := @continuous_simplex_factors_skeleton Real X d s.
  exists k,t; apply: topological_hom_ext => a; exact: ht.
- exact hstage.
Qed.
End DPRealizationUnitSkeletonPassage.
