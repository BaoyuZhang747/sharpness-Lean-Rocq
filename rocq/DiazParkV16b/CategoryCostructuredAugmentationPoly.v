(** Unconditional actual costructured diagonal and total augmentations. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialSet SimplicialChains SimplicialChainsMaps CategoryNerve
 BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyChain BisimplicialAlexanderWhitneyNaturality BisimplicialAlexanderWhitneyEquivalencePoly BisimplicialChainComparisonPoly
 BisimplicialConstantTotal BisimplicialConstantTotalAlexanderWhitney SimplicialReplacementConstants SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementAugmentation
 CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint CategoryCostructuredRowAugmentation CategoryCostructuredTotalAugmentation.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve
 DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyChain DPAlexanderWhitneyNaturality DPAlexanderWhitneyEquivalencePoly DPBisimplicialChainComparisonPoly
 DPBisimplicialConstantTotal DPBisimplicialConstantAlexanderWhitney DPSimplicialReplacementConstants DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementAugmentation
 DPCategoryCostructuredDiagram DPCategoryCostructuredRowAugmentation DPCategoryCostructuredTotalAugmentation.
Local Open Scope ring_scope.
Module DPCategoryCostructuredAugmentationPoly.
Section Constants.
Variable R : pzRingType.
Variable X : simplicial_set.
Lemma horizontal_diagonal_quasi : quasi_isomorphism (chain_map_of R (horizontal_diagonal_map X)).
Proof.
have h n (x:term R (diagonal (horizontal_constant X)) n) : map_at R (horizontal_diagonal_map X) n x=x.
  change (free_map R idfun x=x); exact: free_map_identity.
apply degreewise_bijective_quasi_isomorphism.
- move=>n x y hxy; change (map_at R (horizontal_diagonal_map X) n x=map_at R (horizontal_diagonal_map X) n y) in hxy.
  by rewrite !h in hxy.
- move=>n y; exists y; exact: h.
Qed.
Lemma horizontal_total_projection_quasi : quasi_isomorphism (horizontal_projection R X).
Proof.
apply (@quasi_isomorphism_cancel_first R _ _ _ (alexander_whitney R (horizontal_constant X)) (horizontal_projection R X)); first exact: alexander_whitney_quasi_isomorphism.
apply (@quasi_isomorphism_ext R _ _ (chain_map_of R (horizontal_diagonal_map X))
 (chain_composition (alexander_whitney R (horizontal_constant X)) (horizontal_projection R X))).
- move=>n x; symmetry; exact: horizontal_projection_after_aw.
- exact: horizontal_diagonal_quasi.
Qed.
End Constants.
Section Augmentation.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor C D.
Local Notation F := (costructured_nerve_diagram T).
Definition diagonal_augmentation : simplicial_map (diagonal (replacement F)) (nerve C) :=
 diagonal_coefficient_augmentation (projection_cocone T).
Lemma diagonal_augmentation_formula n (d:simplex (nerve D) n) (s:simplex (fobj F (initial_object d)) n) :
 component diagonal_augmentation n (existT _ d s)=DPCategoryCostructuredNerveEndpoint.projected_simplex s.
Proof. reflexivity. Qed.
Theorem diagonal_augmentation_quasi_isomorphism : quasi_isomorphism (chain_map_of R diagonal_augmentation).
Proof.
apply (@quasi_isomorphism_ext R _ _
 (chain_composition (diagonal_chains_map R (costructured_augmentation T)) (chain_map_of R (horizontal_diagonal_map (nerve C))))
 (chain_map_of R diagonal_augmentation)).
- move=>n x; symmetry; exact: map_composition.
- apply quasi_isomorphism_composition; last exact: horizontal_diagonal_quasi.
  apply bisimplicial_diagonal_quasi_isomorphism_of_total; exact: total_augmentation_quasi_isomorphism.
Qed.
Definition total_augmentation : chain_map (total_chains R (replacement F)) (chains R (nerve C)) :=
 chain_composition (total_chains_map R (costructured_augmentation T)) (horizontal_projection R (nerve C)).
Theorem total_augmentation_to_nerve_quasi_isomorphism : quasi_isomorphism total_augmentation.
Proof.
apply quasi_isomorphism_composition; [exact: total_augmentation_quasi_isomorphism | exact: horizontal_total_projection_quasi].
Qed.
Lemma total_diagonal_augmentation_triangle n (x:term R (diagonal (replacement F)) n) :
 chain_map_at total_augmentation n (chain_map_at (alexander_whitney R (replacement F)) n x)=map_at R diagonal_augmentation n x.
Proof.
change (chain_map_at (horizontal_projection R (nerve C)) n
 (chain_map_at (total_chains_map R (costructured_augmentation T)) n (chain_map_at (alexander_whitney R (replacement F)) n x))=map_at R diagonal_augmentation n x).
rewrite alexander_whitney_natural horizontal_projection_after_aw.
exact (Logic.eq_sym (@map_composition R _ _ _ (diagonal_map (costructured_augmentation T)) (horizontal_diagonal_map (nerve C)) n x)).
Qed.
End Augmentation.
End DPCategoryCostructuredAugmentationPoly.
