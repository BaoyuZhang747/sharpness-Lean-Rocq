(** Actual augmented category-string exactness implies that the literal
    simplicial projection of the nerve to one point is a native quasi-isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness MackeyModuleCarriers
  MackeyModuleQuotient HomologicalModuleIso.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainQuasiIsomorphism SimplicialSet SimplicialChains SimplicialChainsMaps
  CategoryNerve CategoryStringChains CategoryNerveStringChainTerms CategoryNerveStringChains
  CategoryInducedBarCofinality AugmentedChainHomologyComparison ConstantSimplicialPointChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve
  DPAugmentedChainHomologyComparison DPConstantSimplicialPointChains DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPCategoryNerveAugmentedExact.
Section Exact.
Variable R : pzRingType.
Variable C : category.
Hypothesis hC : category_string_augmented_exact R C.

Lemma nerve_augmentation_surjective (r : R^o) :
  exists x, augmentation R (nerve C) x = r.
Proof.
have [v hv] := proj1 hC r.
exists (string_to_nerve_at R C 0%N v); by rewrite string_to_nerve_augmentation.
Qed.

Lemma nerve_zero_exact (x : term R (nerve C) 0%N) :
  augmentation R (nerve C) x = 0 -> @DPChainComplex.boundary R (chains R (nerve C)) 0 x.
Proof.
move=> hx.
have hs : category_string_augmentation R C (nerve_to_string_at R C 0%N x) = 0.
  by rewrite nerve_to_string_augmentation.
have [w hw] := proj1 (proj2 hC) _ hs.
exists (string_to_nerve_at R C 1%N w).
change (@DPSimplicialChains.boundary R (nerve C) 0%N (string_to_nerve_at R C 1%N w) = x).
by rewrite string_to_nerve_boundary hw string_to_nerve_inverse.
Qed.

Lemma nerve_positive_exact n (x : chain_term (chains R (nerve C)) n.+1) :
  @cycle R (chains R (nerve C)) n.+1 x ->
  @DPChainComplex.boundary R (chains R (nerve C)) n.+1 x.
Proof.
move=> hx.
have hs : @category_string_boundary R C n (nerve_to_string_at R C n.+1 x) = 0.
  rewrite nerve_to_string_boundary.
  change (@DPSimplicialChains.boundary R (nerve C) n x = 0) in hx.
  by rewrite hx linear0.
have [w hw] := proj2 (proj2 hC) n _ hs.
exists (string_to_nerve_at R C n.+2 w).
change (@DPSimplicialChains.boundary R (nerve C) n.+1 (string_to_nerve_at R C n.+2 w) = x).
by rewrite string_to_nerve_boundary hw string_to_nerve_inverse.
Qed.

Definition nerve_to_point_chain := chain_map_of R (to_point (nerve C)).

Definition nerve_point_homology_iso n : @isomorphism (module_category R)
  [the lmodType R of homology (chains R (nerve C)) n]
  [the lmodType R of homology (chains R point) n] :=
  @augmented_comparison_iso R (chains R (nerve C)) (chains R point) nerve_to_point_chain
    (augmentation R (nerve C)) (augmentation R point)
    (@augmentation_boundary R point) (@map_augmentation R (nerve C) point (to_point (nerve C)))
    nerve_augmentation_surjective nerve_zero_exact (@point_zero_exact R)
    nerve_positive_exact (@point_positive_exact R) n.

Theorem nerve_to_point_quasi_isomorphism : quasi_isomorphism (chain_map_of R (to_point (nerve C))).
Proof.
move=> n; split.
- exact (@module_iso_hom_injective R _ _ (nerve_point_homology_iso n)).
- move=> y; exists (module_hom_fun (iso_inv (nerve_point_homology_iso n)) y).
  exact (@module_iso_inv_hom_apply R _ _ (nerve_point_homology_iso n) y).
Qed.

Theorem nerve_point_homology_iso_hom n (q : homology (chains R (nerve C)) n) :
  module_hom_fun (iso_hom (nerve_point_homology_iso n)) q =
  homology_map (chain_map_of R (to_point (nerve C))) n q.
Proof. reflexivity. Qed.
End Exact.
End DPCategoryNerveAugmentedExact.
