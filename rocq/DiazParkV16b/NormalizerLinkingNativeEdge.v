(** The normalizer edge in literal native chain-automorphism cohomology coordinates. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor HomologicalModuleIso FusionSystems FusionSaturation PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory LinkingChainAutomorphisms NormalizerOrdinaryCoefficient
 NormalizerLinkingChainEvaluation NormalizerLinkingChainAutomorphismChart NormalizerLinkingGeometricSharpness
 NormalizerLinkingRealizationSharpness NormalizerLinkingRealizationCoordinates ModuleLimitIsoComponents
 CategoryNerve SingularCohomology GeometricRealizationMaps GroupClassifyingCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPNormalizerChainIndex DPLinkingChainAutomorphisms
 DPNormalizerOrdinaryCoefficient DPNormalizerLinkingChainAutomorphismChart DPNormalizerLinkingGeometricSharpness
 DPNormalizerLinkingRealizationSharpness DPNormalizerLinkingRealizationCoordinates
 DPCategoryNerve DPSingularCohomology DPGeometricRealizationMaps DPGroupClassifyingCohomology.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Module DPNormalizerLinkingNativeEdge.
Section Edge.
Variable Real:realType.
Variable S:finGroupType.
Variable F:DPFusionSystem.system S.
Variable L:DPCentricLinking.system F.
Variable p:nat.
Variable hS:p.-group [set: S].
Variable sat:DPFusionSaturation.saturated F p.
Local Notation r := (@canonical_representative S F).
Local Notation hr := (@canonical_representative_class S F).
Local Notation E := (DPNormalizerLinkingChainEvaluation.evaluation L).
Definition native_limit_iso (R:comPzRingType) (A:lmodType R) n :=
 @DPModuleLimitIsoComponents.limit_iso R (opposite (index_category F)) _ _
 (@normalizer_native_coefficient_iso Real R A S F L n).
Definition field_native_edge_iso (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n :=
 module_iso_comp (@field_edge_iso Real S F L p hS sat K charp A n)
 (native_limit_iso A n).
Theorem field_native_edge_component (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n z d :
 module_limit_val (module_hom_fun (iso_hom (field_native_edge_iso charp A n)) z) d =
 module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
 (singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z).
Proof.
change (module_limit_val (module_hom_fun (iso_hom (native_limit_iso A n))
 (module_hom_fun (iso_hom (@field_edge_iso Real S F L p hS sat K charp A n)) z)) d=
 module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
 (singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z)).
rewrite DPModuleLimitIsoComponents.limit_iso_component field_edge_iso_component.
exact (@fibre_native_evaluation_coordinate Real [the comPzRingType of (K:Type)] A S F L d (r d) (hr d) n z).
Qed.
Variable hp:prime p.
Definition primes_inverted_native_edge_iso (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n :=
 module_iso_comp (@primes_inverted_edge_iso Real S F L p hS sat hp R localR A n)
 (native_limit_iso A n).
Theorem primes_inverted_native_edge_component (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n z d :
 module_limit_val (module_hom_fun (iso_hom (primes_inverted_native_edge_iso localR A n)) z) d =
 module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
 (singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z).
Proof.
change (module_limit_val (module_hom_fun (iso_hom (native_limit_iso A n))
 (module_hom_fun (iso_hom (@primes_inverted_edge_iso Real S F L p hS sat hp R localR A n)) z)) d=
 module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
 (singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z)).
rewrite DPModuleLimitIsoComponents.limit_iso_component primes_inverted_edge_iso_component.
exact (@fibre_native_evaluation_coordinate Real R A S F L d (r d) (hr d) n z).
Qed.
End Edge.
End DPNormalizerLinkingNativeEdge.
