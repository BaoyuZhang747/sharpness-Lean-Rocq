(** Unconditional actual subgroup geometric sharpness, convergence, and canonical edge. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits FusionSystems FusionSaturation PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection SimplicialSet
 SingularCohomology SingularCochainReplacementEdge RealizationUnitComparison
 LinkingSubgroupRealizationComparison LinkingSubgroupRealizationSharpness CategoryRealizationDecomposition.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPSimplicialSet DPSingularCohomology DPSingularReplacementEdge DPRealizationUnitComparison
 DPLinkingSubgroupRealizationComparison DPLinkingSubgroupRealizationSharpness DPCategoryRealizationDecomposition.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Module DPLinkingSubgroupGeometricSharpness.
Section Geometry.
Variable Real:realType.
Variable S:finGroupType.
Variable F:DPFusionSystem.system S.
Variable L:DPCentricLinking.system F.
Definition subgroup_geometric_cocone := space_cocone Real (DPLinkingOrbit.orbit_projection L).
Definition subgroup_geometric_augmentation_quasi_isomorphism (R:pzRingType) :=
 singular_augmentation_quasi_isomorphism Real (DPLinkingOrbit.orbit_projection L) R.
Definition subgroup_geometric_total_iso (R:comPzRingType) (A:lmodType R) n :=
 total_cohomology_iso Real (DPLinkingOrbit.orbit_projection L) A n.
Definition subgroup_geometric_finite_convergence_iso (R:comPzRingType) (A:lmodType R) p n :=
 finite_convergence_iso Real (DPLinkingOrbit.orbit_projection L) A p n.
Variable p:nat.
Variable hS:p.-group [set: S].
Variable sat:DPFusionSaturation.saturated F p.
Theorem field_positive_limits_unconditional (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) :
 singular_positive_limits_vanish Real A (subgroup_space_diagram Real L).
Proof.
exact (@field_positive_limits Real S F L p hS sat K charp A
 (fun X=>realization_unit_quasi_isomorphism Real [the comPzRingType of (K:Type)] X)).
Qed.
Definition field_edge_iso (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n :=
 @limit_iso Real _ _ (DPLinkingOrbit.orbit_projection L) [the comPzRingType of (K:Type)] A
 (@field_positive_limits_unconditional K charp A) n.
Theorem field_edge_iso_component (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n z P :
 module_limit_val (module_hom_fun (iso_hom (field_edge_iso charp A n)) z) P =
 singular_cohomology_map Real (component subgroup_geometric_cocone P) A n z.
Proof. exact: limit_iso_component. Qed.
Variable hp:prime p.
Theorem primes_inverted_positive_limits_unconditional (R:comPzRingType)
 (localR:DPPrimeLocalUniversal.primes_inverted p R) (A:lmodType R) :
 singular_positive_limits_vanish Real A (subgroup_space_diagram Real L).
Proof.
exact (@primes_inverted_positive_limits Real S F L p hp hS sat R localR A
 (fun X=>realization_unit_quasi_isomorphism Real R X)).
Qed.
Definition primes_inverted_edge_iso (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n :=
 @limit_iso Real _ _ (DPLinkingOrbit.orbit_projection L) R A
 (@primes_inverted_positive_limits_unconditional R localR A) n.
Theorem primes_inverted_edge_iso_component (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n z P :
 module_limit_val (module_hom_fun (iso_hom (primes_inverted_edge_iso localR A n)) z) P =
 singular_cohomology_map Real (component subgroup_geometric_cocone P) A n z.
Proof. exact: limit_iso_component. Qed.
End Geometry.
End DPLinkingSubgroupGeometricSharpness.
