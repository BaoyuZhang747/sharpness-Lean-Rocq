(** The actual normalizer decomposition of the uncompleted linking-system realization.
    Evaluation, coefficient comparisons and all positive-limit inputs are constructed. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryComma FusionSystems FusionSaturation PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem NormalizerLinkingChainCategory NormalizerLinkingChainProjection NormalizerLinkingChainEvaluation NormalizerLinkingEvaluationCofinality
 CategoryNerve SingularCohomology GeometricRealizationMaps SingularCochainReplacementEdge
 NormalizerLinkingRealizationSharpness CategoryRealizationEvaluationDecomposition.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPCategoryNerve DPSingularCohomology DPGeometricRealizationMaps DPSingularReplacementEdge
 DPNormalizerLinkingEvaluationCofinality DPNormalizerLinkingRealizationSharpness DPCategoryRealizationEvaluationDecomposition.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Module DPNormalizerLinkingGeometricSharpness.
Section Geometry.
Variable Real:realType.
Variable S:finGroupType.
Variable F:DPFusionSystem.system S.
Variable L:DPCentricLinking.system F.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation E := (DPNormalizerLinkingChainEvaluation.evaluation L).
Definition normalizer_geometric_cocone := space_cocone Real P E.
Definition normalizer_geometric_augmentation_quasi_isomorphism (R:comPzRingType) :=
 @singular_augmentation_quasi_isomorphism Real _ _ _ P E R (@evaluation_nerve_quasi_isomorphism R S F L).
Definition normalizer_geometric_total_iso (R:comPzRingType) (A:lmodType R) n :=
 @total_cohomology_iso Real _ _ _ P E R (@evaluation_nerve_quasi_isomorphism R S F L) A n.
Definition normalizer_geometric_finite_convergence_iso (R:comPzRingType) (A:lmodType R) p n :=
 @finite_convergence_iso Real _ _ _ P E R (@evaluation_nerve_quasi_isomorphism R S F L) A p n.
Variable p:nat.
Variable hS:p.-group [set: S].
Variable sat:DPFusionSaturation.saturated F p.
Definition field_edge_iso (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n :=
 @limit_iso Real _ _ _ P E [the comPzRingType of (K:Type)]
 (@evaluation_nerve_quasi_isomorphism [the comPzRingType of (K:Type)] S F L) A
 (@field_positive_limits Real S F L p hS sat K charp A) n.
Theorem field_edge_iso_component (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K) n z d :
 module_limit_val (module_hom_fun (iso_hom (field_edge_iso charp A n)) z) d =
 singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (costructured_projection P d) E))) A n z.
Proof. exact: limit_iso_component. Qed.
Variable hp:prime p.
Definition primes_inverted_edge_iso (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n :=
 @limit_iso Real _ _ _ P E R (@evaluation_nerve_quasi_isomorphism R S F L) A
 (@primes_inverted_positive_limits Real S F L p hp hS sat R localR A) n.
Theorem primes_inverted_edge_iso_component (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R)
 (A:lmodType R) n z d :
 module_limit_val (module_hom_fun (iso_hom (primes_inverted_edge_iso localR A n)) z) d =
 singular_cohomology_map Real (realization_map Real (nerve_map (functor_comp (costructured_projection P d) E))) A n z.
Proof. exact: limit_iso_component. Qed.
End Geometry.
End DPNormalizerLinkingGeometricSharpness.
