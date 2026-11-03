(** Simultaneous induction on the actual skeletal dimension. The boundary of
    an n-simplex is already its strict n-skeleton, including dimension zero. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialBoundary SimplicialSubcomplex
  SimplicialSkeleton SimplicialSkeletonAttachmentStages SimplicialSkeletonAttachmentCover
  SimplicialBoundarySkeleton ChainQuasiIsomorphism RealizationUnitChains
  RealizationUnitEmpty RealizationUnitIsomorphism RealizationUnitStageSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPRealizationUnitFiniteSkeleton.
Import DPSimplicialSet DPSimplicialBoundary DPSimplicialSubcomplex DPSimplicialSkeleton
  DPSimplicialAttachmentStages DPSimplicialAttachmentCover DPSimplicialBoundarySkeleton
  DPChainQuasiIsomorphism DPRealizationUnitChains DPRealizationUnitEmpty
  DPRealizationUnitIsomorphism DPRealizationUnitStageSuccessor.
Section Induction.
Variable Real : realType.
Variable R : pzRingType.

Theorem stage_unit_quasi_isomorphism n (X : simplicial_set) :
  quasi_isomorphism (realization_unit_chains Real R (stage_set X n)).
Proof.
elim: n => [|n ih] in X *.
- exact (@stage_zero_unit_quasi_isomorphism Real R X).
- apply (@stage_successor_unit_quasi_isomorphism Real R X n).
  + exact (@realization_unit_isomorphism Real R _ _ (boundary_skeletal_isomorphism n)
      (ih (boundary_set n))).
  + exact (ih X).
Qed.

Theorem skeleton_unit_quasi_isomorphism (X : simplicial_set) n :
  quasi_isomorphism (realization_unit_chains Real R (skeleton_set X n)).
Proof.
exact (@stage_unit_quasi_isomorphism n.+1 X).
Qed.
End Induction.
End DPRealizationUnitFiniteSkeleton.
