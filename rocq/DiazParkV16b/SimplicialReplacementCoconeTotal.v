(** Actual cocone augmentation of replacement total chains and its AW triangle. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  SimplicialSet SimplicialSetYoneda SimplicialChains SimplicialChainsMaps BisimplicialSet BisimplicialChains
  BisimplicialAlexanderWhitneyChain BisimplicialAlexanderWhitneyNaturality
  BisimplicialConstantTotal BisimplicialConstantTotalAlexanderWhitney
  SimplicialReplacementConstants SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementAugmentation
  FirstQuadrantChainTotalSupport SimplicialReplacementDualTotal.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains
  DPAlexanderWhitneyChain DPAlexanderWhitneyNaturality
  DPBisimplicialConstantTotal DPBisimplicialConstantAlexanderWhitney DPSimplicialReplacementConstants
  DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementAugmentation
  DPFirstQuadrantChainSupport DPSimplicialReplacementDualTotal.
Local Open Scope ring_scope.

Module DPSimplicialReplacementCoconeTotal.
Section Augmentation.
Variable R : pzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable X : simplicial_set.
Variable a : nat_trans F (@constant_diagram C simplicial_category X).
Let K := bisimplicial_bicomplex R (replacement F).

Definition cocone_total_augmentation : chain_map (total_chains R (replacement F)) (chains R X) :=
  chain_composition (total_chains_map R (coefficient_augmentation a)) (horizontal_projection R X).

Lemma cocone_total_augmentation_formula n (z : chain_term (total_chains R (replacement F)) n) :
  chain_map_at cocone_total_augmentation n z =
  free_map R (bisimplex_component (coefficient_augmentation a) 0 n) (z 0%N n erefl).
Proof. reflexivity. Qed.

Theorem cocone_total_augmentation_triangle n (z : term R (diagonal (replacement F)) n) :
  chain_map_at cocone_total_augmentation n
    (chain_map_at (alexander_whitney R (replacement F)) n z) =
  map_at R (diagonal_coefficient_augmentation a) n z.
Proof.
change (chain_map_at (horizontal_projection R X) n
  (chain_map_at (total_chains_map R (coefficient_augmentation a)) n
    (chain_map_at (alexander_whitney R (replacement F)) n z)) =
  map_at R (diagonal_coefficient_augmentation a) n z).
rewrite alexander_whitney_natural horizontal_projection_after_aw.
symmetry; exact: map_composition.
Qed.

Lemma cocone_total_augmentation_include_basis n c (x : simplex (fobj F c) n) :
  chain_map_at cocone_total_augmentation n
    (@total_include R K 0 n n erefl (free_basis R (@zero_cell C F c n x))) =
  free_basis R (component (component a c) n x).
Proof.
rewrite cocone_total_augmentation_formula total_include_same free_map_basis.
reflexivity.
Qed.

Theorem cocone_total_augmentation_include n c (x : term R (fobj F c) n) :
  chain_map_at cocone_total_augmentation n
    (@total_include R K 0 n n erefl (free_map R (@zero_cell C F c n) x)) =
  map_at R (component a c) n x.
Proof.
apply (free_lift_ext
  (g := (chain_map_at cocone_total_augmentation n \o @total_include R K 0 n n erefl
    \o free_map R (@zero_cell C F c n) : {linear _ -> _}))
  (h := map_at R (component a c) n)) => y.
change (chain_map_at cocone_total_augmentation n
    (@total_include R K 0 n n erefl (free_map R (@zero_cell C F c n) (free_basis R y))) =
  map_at R (component a c) n (free_basis R y)).
by rewrite free_map_basis cocone_total_augmentation_include_basis map_at_basis.
Qed.
End Augmentation.
End DPSimplicialReplacementCoconeTotal.
