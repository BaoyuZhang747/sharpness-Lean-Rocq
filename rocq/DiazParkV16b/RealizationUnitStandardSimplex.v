(** The literal realization-unit map is a homology isomorphism on representables. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalModuleIso.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  SimplicialSet SimplicialChains SingularSet SingularCohomology
  GeometricRealizationCarrier GeometricRealizationStandardSimplex
  RealizationUnitChains StandardSimplexConeChains SingularContractibleChains
  SingularAugmentationContractible SingularHomeomorphismChains AugmentedChainHomologyComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPSimplicialSet DPSimplicialChains DPSingularSet DPSingularCohomology
  DPGeometricRealization DPGeometricRealizationStandardSimplex
  DPRealizationUnitChains DPStandardSimplexConeChains DPSingularHomeomorphismChains
  DPAugmentedChainHomologyComparison.
Local Open Scope ring_scope.

Module DPRealizationUnitStandardSimplex.
Section Standard.
Variable Real : realType.
Variable R : pzRingType.
Variable d : nat.
Let X := standard_simplex d.
Let C := chains R X.
Let D := singular_chains Real R (realization_space Real X).
Let unit := realization_unit_chains Real R X.

Lemma standard_source_augmentation_surjective (r : R^o) :
  exists x, augmentation R X x = r.
Proof.
exists (@simplex_augmentation_section R d r).
exact: simplex_augmentation_sectionK.
Qed.

Lemma standard_target_positive_exact n (x : chain_term D n.+1) :
  @cycle R D n.+1 x -> @DPChainComplex.boundary R D n.+1 x.
Proof.
apply: (@homeomorphism_positive_exact Real R _ _
  (realized_standard_simplex_homeomorphism Real d) n).
exact: DPSingularContractibleChains.simplex_positive_exact.
Qed.

Lemma standard_target_augmentation_exact (x : chain_term D 0%N) :
  augmentation R (singular_set Real (realization_space Real X)) x = 0 ->
  @DPChainComplex.boundary R D 0%N x.
Proof.
apply: (@homeomorphism_augmentation_exact Real R _ _
  (realized_standard_simplex_homeomorphism Real d)).
exact: DPSingularAugmentationContractible.simplex_augmentation_exact.
Qed.

Definition standard_unit_homology_iso n : @isomorphism (module_category R)
  (homology C n) (homology D n).
Proof.
apply: (@augmented_comparison_iso R C D unit
  (augmentation R X) (augmentation R (singular_set Real (realization_space Real X)))).
- exact: augmentation_boundary.
- exact: realization_unit_augmentation.
- exact: standard_source_augmentation_surjective.
- exact: standard_simplex_augmentation_exact.
- exact: standard_target_augmentation_exact.
- exact: standard_simplex_positive_exact.
- exact: standard_target_positive_exact.
Defined.

Lemma standard_unit_homology_iso_hom n (q : homology C n) :
  module_hom_fun (iso_hom (standard_unit_homology_iso n)) q = homology_map unit n q.
Proof. reflexivity. Qed.

End Standard.
End DPRealizationUnitStandardSimplex.
