(** The unconditional comparison for the actual characteristic-simplex unit,
    arbitrary simplicial sets and arbitrary coefficient rings. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazParkV16b Require Import SimplicialSet ChainQuasiIsomorphism
  RealizationUnitChains RealizationUnitFiniteSkeleton RealizationUnitSkeletonPassage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPRealizationUnitComparison.
Import DPSimplicialSet DPChainQuasiIsomorphism DPRealizationUnitChains
  DPRealizationUnitFiniteSkeleton DPRealizationUnitSkeletonPassage.

Theorem realization_unit_quasi_isomorphism (Real : realType) (R : pzRingType)
  (X : simplicial_set) : quasi_isomorphism (realization_unit_chains Real R X).
Proof.
apply (@actual_realization_unit_quasi_iso_of_skeleta Real R X).
intro n; exact (@skeleton_unit_quasi_isomorphism Real R X n).
Qed.
End DPRealizationUnitComparison.
