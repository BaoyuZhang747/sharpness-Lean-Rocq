(** The actual chain map induced by the characteristic-simplex adjunction unit.
    No assertion of quasi-isomorphism for arbitrary simplicial sets is made. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplexCategory SimplicialSet SimplicialChains SimplicialChainsMaps
  SingularSet SingularCohomology TopologicalCategory TopologicalSimplexBasic
  TopologicalSimplexAffine TopologicalSimplexContinuity GeometricRealizationCarrier
  GeometricRealizationMaps GeometricRealizationStandardSimplex GeometricRealizationSingularAdjunction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPRealizationUnitChains.
Import DiazParkFreeModule DPChainComplex DPSimplexCategory DPSimplicialSet DPSimplicialChains
  DPSimplicialChainMaps DPSingularSet DPSingularCohomology DPTopological
  DPGeometricRealization DPGeometricRealizationMaps
  DPGeometricRealizationStandardSimplex DPGeometricRealizationSingularAdjunction.

Section Unit.
Variable Real : realType.
Variable R : pzRingType.

Definition realization_unit_chains (X : simplicial_set) :
  chain_map (chains R X) (singular_chains Real R (realization_space Real X)) :=
  chain_map_of R (realization_unit_map Real X).

Lemma realization_unit_basis X n (x : simplex X n) :
  chain_map_at (realization_unit_chains X) n (free_basis R x) =
    free_basis R (@characteristic_map Real X n x).
Proof. exact: map_at_basis. Qed.

Lemma realization_unit_naturality X Y (a : simplicial_map X Y) n (c : term R X n) :
  chain_map_at (singular_chain_map Real R (realization_map Real a)) n
    (chain_map_at (realization_unit_chains X) n c) =
  chain_map_at (realization_unit_chains Y) n
    (chain_map_at (chain_map_of R a) n c).
Proof.
change (map_at R (singular_map Real (realization_map Real a)) n
    (map_at R (realization_unit_map Real X) n c) =
  map_at R (realization_unit_map Real Y) n (map_at R a n c)).
rewrite <- !map_composition.
rewrite (realization_unit_natural Real a). reflexivity.
Qed.

Lemma realization_unit_augmentation X (c : term R X 0%N) :
  augmentation R (singular_set Real (realization_space Real X))
    (chain_map_at (realization_unit_chains X) 0%N c) = augmentation R X c.
Proof. exact: map_augmentation. Qed.

Lemma standard_unit_generator d n (f : ordinal_map n d) :
  chain_map_at (singular_chain_map Real R (standard_evaluation Real d)) n
    (chain_map_at (realization_unit_chains (standard_simplex d)) n (free_basis R f)) =
  free_basis R (DPTopologicalSimplexContinuity.simplex_map Real f).
Proof.
rewrite realization_unit_basis.
change (map_at R (singular_map Real (standard_evaluation Real d)) n
  (free_basis R (@characteristic_map Real (standard_simplex d) n f)) =
  free_basis R (DPTopologicalSimplexContinuity.simplex_map Real f)).
rewrite map_at_basis. apply: f_equal. apply: topological_hom_ext => t.
exact: standard_evaluation_characteristic.
Qed.

End Unit.
End DPRealizationUnitChains.
