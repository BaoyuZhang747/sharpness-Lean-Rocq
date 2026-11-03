(** Both actual normalizer coefficients and the literal native edge, from Route B. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup all_classical reals topology.
From DiazPark Require Import Category CategoryComma CategoryModules CategoryModuleLimits CategoryModuleExactness
 CategoryDerivedLimits HomologicalModuleIso BarHigherLimitVanishing FusionSystems FusionSaturation.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory LinkingChainAutomorphisms
 NormalizerOrdinaryCoefficient NormalizerLinkingRealizationSharpness
 NormalizerLinkingChainProjection NormalizerLinkingChainEvaluation NormalizerLinkingChainAutomorphismChart
 NormalizerLinkingEvaluationCofinality NormalizerLinkingRealizationCoordinates
 CategoryRealizationEvaluationDecomposition ModuleLimitIsoComponents
 SingularCochainReplacementEdge CategoryNerve SingularCohomology
 GeometricRealizationCarrier GeometricRealizationMaps GroupClassifyingCohomology.
From DiazParkV28 Require Import GroupCohomologyRouteB NormalizerComparisonRouteB.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DiazParkBarHigherLimitVanishing
 DPNormalizerChainIndex DPLinkingChainAutomorphisms DPNormalizerOrdinaryCoefficient
 DPNormalizerLinkingRealizationSharpness DPNormalizerLinkingEvaluationCofinality
 DPNormalizerLinkingChainAutomorphismChart DPNormalizerLinkingRealizationCoordinates
 DPCategoryNerve DPSingularCohomology DPGeometricRealization DPGeometricRealizationMaps
 DPGroupClassifyingCohomology DPSingularReplacementEdge.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28NormalizerSharpness.
Section Normalizer.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Variable charp : p \in [pchar K].
Variable A : lmodType K.
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation r := (@canonical_representative S F).
Local Notation hr := (@canonical_representative_class S F).
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation E := (DPNormalizerLinkingChainEvaluation.evaluation L).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).

Theorem native_field_higher_limits_zero n j :
  forall z : derived_limit K (@coefficient S F L K A n) j.+1, z = 0.
Proof.
apply/(module_iso_zero_iff
  (@DPV28NormalizerComparison.field_higher_limit_iso S F L p hS sat r hr K charp A n j.+1)).
exact (@DPV28GroupCohomologySharpness.field_higher_limits_zero S F p hS sat K charp A n j).
Qed.

Theorem field_positive_limits :
  singular_positive_limits_vanish Real A (normalizer_space_diagram Real L).
Proof.
move=> n j x.
pose e := @normalizer_native_higher_limit_iso Real R A S F L n j.+1.
apply (module_iso_hom_injective (e := e)); rewrite module_hom_zero.
exact (@native_field_higher_limits_zero n j (module_hom_fun (iso_hom e) x)).
Qed.

Definition field_edge_iso n :=
  @DPCategoryRealizationEvaluationDecomposition.limit_iso Real _ _ _ P E R
    (@evaluation_nerve_quasi_isomorphism R S F L) A field_positive_limits n.

Theorem field_edge_component n z d :
  module_limit_val (module_hom_fun (iso_hom (field_edge_iso n)) z) d =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (functor_comp (costructured_projection P d) E))) A n z.
Proof. exact: DPCategoryRealizationEvaluationDecomposition.limit_iso_component. Qed.

Definition native_limit_iso n :=
  @DPModuleLimitIsoComponents.limit_iso R (opposite (index_category F)) _ _
    (@normalizer_native_coefficient_iso Real R A S F L n).

Definition native_edge_iso n :=
  module_iso_comp (field_edge_iso n) (native_limit_iso n).

Theorem native_edge_component n z d :
  module_limit_val (module_hom_fun (iso_hom (native_edge_iso n)) z) d =
  module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z).
Proof.
change (module_limit_val (module_hom_fun (iso_hom (native_limit_iso n))
  (module_hom_fun (iso_hom (field_edge_iso n)) z)) d =
  module_hom_fun (iso_hom (group_comparison_iso Real A (chain_automorphism_group L (r d)) n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (functor_comp (automorphism_chart L (r d)) E))) A n z)).
rewrite DPModuleLimitIsoComponents.limit_iso_component field_edge_component.
exact (@fibre_native_evaluation_coordinate Real R A S F L d (r d) (hr d) n z).
Qed.
End Normalizer.
End DPV28NormalizerSharpness.
