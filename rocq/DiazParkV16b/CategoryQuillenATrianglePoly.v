(** The actual Quillen-A projection triangle commutes on native homology,
    by the genuine natural-transformation prism in the varying comma category. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet CategoryNerve
  BisimplicialSet SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementAugmentation
  CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint CategoryCostructuredAugmentationPoly
  CategoryQuillenATotalComma CategoryQuillenATriangleMap CategoryNerveNatTransHomotopy
  ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphismLaws SimplicialChains SimplicialChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPCategoryNerve DPBisimplicialSet
  DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementAugmentation
  DPCategoryCostructuredDiagram DPCategoryCostructuredNerveEndpoint DPCategoryCostructuredAugmentationPoly
  DPCategoryQuillenATotalComma DPCategoryQuillenATriangleMap DPCategoryNerveNatTransHomotopy
  DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphismLaws
  DPSimplicialChains DPSimplicialChainMaps.

Module DPCategoryQuillenATrianglePoly.
Section SimplicialTriangle.
Variables C D : category.
Variable T : functor C D.
Local Notation F := (costructured_nerve_diagram T).

Lemma diagonal_source_projection :
  nat_comp (diagonal_to_comma T) (nerve_map (source_projection T)) = diagonal_augmentation T.
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[s a]].
change (functor_comp (@cell_simplex C D T n s a) (source_projection T) = projected_simplex a).
exact: cell_source_projection.
Qed.

Lemma diagonal_target_projection :
  nat_comp (diagonal_to_comma T) (nerve_map (target_projection T)) = diagonal_base_projection F.
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[s a]].
change (functor_comp (@cell_simplex C D T n s a) (target_projection T) = s).
exact: cell_target_projection.
Qed.

Lemma diagonal_source_composite :
  nat_comp (diagonal_to_comma T) (nerve_map (functor_comp (source_projection T) T)) =
  nat_comp (diagonal_augmentation T) (nerve_map T).
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[s a]].
change (functor_comp (@cell_simplex C D T n s a) (functor_comp (source_projection T) T) =
  functor_comp (projected_simplex a) T).
by rewrite -functor_comp_assoc cell_source_projection.
Qed.
End SimplicialTriangle.

Section Homology.
Variable R : pzRingType.

Lemma simplicial_homology_composition (X Y Z : simplicial_set)
    (f : simplicial_map X Y) (g : simplicial_map Y Z) n (z : homology (chains R X) n) :
  homology_map (chain_map_of R (nat_comp f g)) n z =
  homology_map (chain_map_of R g) n (homology_map (chain_map_of R f) n z).
Proof.
rewrite -homology_map_composition.
apply homology_map_ext; move=>k x; exact: map_composition.
Qed.

Theorem homology_triangle (C D : category) (T : functor C D) n
    (z : homology (chains R (diagonal (replacement (costructured_nerve_diagram T)))) n) :
  homology_map (chain_map_of R (nerve_map T)) n
    (homology_map (chain_map_of R (diagonal_augmentation T)) n z) =
  homology_map (chain_map_of R (diagonal_base_projection (costructured_nerve_diagram T))) n z.
Proof.
rewrite -simplicial_homology_composition -diagonal_source_composite -diagonal_target_projection.
rewrite !simplicial_homology_composition.
symmetry; exact (homology_map_homotopy (nerve_nat_trans_homotopy R (projection_transformation T))
  (homology_map (chain_map_of R (diagonal_to_comma T)) n z)).
Qed.
End Homology.
End DPCategoryQuillenATrianglePoly.

