(** Actual homological Quillen A for literal functor-induced nerve/string maps.
    Every comma premise concerns the actual augmented chain complex; the
    comparison theorem is constructed using the checked replacement and prism. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryComma CategoryLeftKan.
From DiazParkV16b Require Import ChainComplex.
From DiazParkV16b Require Import ChainHomology.
From DiazParkV16b Require Import ChainHomologyMaps.
From DiazParkV16b Require Import ChainQuasiIsomorphism.
From DiazParkV16b Require Import SimplicialSet.
From DiazParkV16b Require Import SimplicialChains.
From DiazParkV16b Require Import SimplicialChainsMaps.
From DiazParkV16b Require Import CategoryNerve.
From DiazParkV16b Require Import CategoryStringChains.
From DiazParkV16b Require Import CategoryStringChainsMaps.
From DiazParkV16b Require Import CategoryInducedBarCofinality.
From DiazParkV16b Require Import ConstantSimplicialPointChains.
From DiazParkV16b Require Import CategoryNerveAugmentedExact.
From DiazParkV16b Require Import SimplicialReplacementAugmentation.
From DiazParkV16b Require Import CategoryCostructuredDiagram.
From DiazParkV16b Require Import CategoryCostructuredAugmentationPoly.
From DiazParkV16b Require Import CategoryQuillenABase.
From DiazParkV16b Require Import CategoryQuillenANerveString.
From DiazParkV16b Require Import CategoryQuillenATrianglePoly.
From DiazParkV16b Require Import CategoryStringOppositeExact.
From DiazParkV16b Require Import CategoryStringOppositeQuasiIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve
  DPConstantSimplicialPointChains DPCategoryNerveAugmentedExact
  DPSimplicialReplacementAugmentation DPCategoryCostructuredDiagram
  DPCategoryCostructuredAugmentationPoly DPCategoryQuillenABase DPCategoryQuillenANerveString
  DPCategoryQuillenATrianglePoly DPCategoryStringOppositeExact DPCategoryStringOppositeQuasiIso.

Module DPCategoryQuillenA.
Section Criterion.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor C D.

Theorem costructured_nerve_quasi_isomorphism
  (h : forall d, category_string_augmented_exact R (costructured_category T d)) :
  quasi_isomorphism (chain_map_of R (nerve_map T)).
Proof.
have hbase : quasi_isomorphism
    (chain_map_of R (diagonal_base_projection (costructured_nerve_diagram T))).
  apply base_projection_quasi_isomorphism=> d.
  exact (@nerve_to_point_quasi_isomorphism R (costructured_category T d) (h d)).
have haug := @diagonal_augmentation_quasi_isomorphism R C D T.
move=> n; split.
- move=> x y hxy.
  have [a ha] := proj2 (haug n) x.
  have [b hb] := proj2 (haug n) y.
  have he : homology_map (chain_map_of R
      (diagonal_base_projection (costructured_nerve_diagram T))) n a =
    homology_map (chain_map_of R
      (diagonal_base_projection (costructured_nerve_diagram T))) n b.
    by rewrite -(@homology_triangle R C D T n a) -(@homology_triangle R C D T n b) ha hb.
  have hab := proj1 (hbase n) _ _ he.
  by rewrite -ha -hb hab.
- move=> y.
  have [a ha] := proj2 (hbase n) y.
  exists (homology_map (chain_map_of R (diagonal_augmentation T)) n a).
  by rewrite homology_triangle.
Qed.

Theorem costructured_chain_quasi_isomorphism
  (h : forall d, category_string_augmented_exact R (costructured_category T d)) :
  quasi_isomorphism (category_string_chain_map R T).
Proof.
apply string_quasi_isomorphism_of_nerve.
exact: costructured_nerve_quasi_isomorphism.
Qed.
End Criterion.

Section Structured.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor C D.

Theorem structured_chain_quasi_isomorphism
  (h : forall d, category_string_augmented_exact R (structured_category T d)) :
  quasi_isomorphism (category_string_chain_map R T).
Proof.
apply functor_map_unopposite_quasi_isomorphism.
apply costructured_chain_quasi_isomorphism=> d.
apply augmented_exact_unopposite.
exact: h.
Qed.

Theorem structured_nerve_quasi_isomorphism
  (h : forall d, category_string_augmented_exact R (structured_category T d)) :
  quasi_isomorphism (chain_map_of R (nerve_map T)).
Proof.
apply nerve_quasi_isomorphism_of_string.
exact: structured_chain_quasi_isomorphism.
Qed.
End Structured.
End DPCategoryQuillenA.
