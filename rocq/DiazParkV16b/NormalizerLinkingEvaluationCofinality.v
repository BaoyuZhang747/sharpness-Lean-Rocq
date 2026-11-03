(** Unconditional native chain comparison for actual first-subgroup evaluation
    on compatible linking chains. Every concrete comma contraction is built. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem NormalizerLinkingChainCategory
  NormalizerLinkingChainEvaluation NormalizerLinkingEvaluationPoints NormalizerLinkingEvaluationTerminal
  NormalizerLinkingEvaluationCoreflection CategoryStringTerminalExact CategoryStringExactnessTransport
  CategoryInducedBarCofinality CategoryQuillenA CategoryNerve SimplicialChains SimplicialChainsMaps
  ChainQuasiIsomorphism CategoryStringChains CategoryStringChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPNormalizerLinkingChainCategory DPNormalizerLinkingChainEvaluation
  DPNormalizerLinkingEvaluationPoints DPNormalizerLinkingEvaluationTerminal
  DPNormalizerLinkingEvaluationCoreflection DPCategoryNerve DPSimplicialChains DPSimplicialChainMaps
  DPChainQuasiIsomorphism.

Module DPNormalizerLinkingEvaluationCofinality.
Theorem evaluation_under_augmented_exact (R : pzRingType) (S : finGroupType)
    (F : DPFusionSystem.system S) (L : DPCentricLinking.system F)
    (P : DPFusionOrbit.centric_object F) :
  category_string_augmented_exact R (evaluation_under L P).
Proof.
apply (@DPCategoryStringExactnessTransport.exact_right_of_adjunction R
  (evaluation_under L P) (evaluation_points L P) (image_coreflection L P)
  (points_inclusion L P) (image_coreflection_adjunction L P)).
exact (DPCategoryStringTerminalExact.terminal_augmented_exact (points_terminal L P) R).
Qed.

Theorem evaluation_chain_quasi_isomorphism (R : pzRingType) (S : finGroupType)
    (F : DPFusionSystem.system S) (L : DPCentricLinking.system F) :
  quasi_isomorphism (category_string_chain_map R (evaluation L)).
Proof.
apply DPCategoryQuillenA.structured_chain_quasi_isomorphism=> P.
exact: evaluation_under_augmented_exact.
Qed.

Theorem evaluation_nerve_quasi_isomorphism (R : pzRingType) (S : finGroupType)
    (F : DPFusionSystem.system S) (L : DPCentricLinking.system F) :
  quasi_isomorphism (chain_map_of R (nerve_map (evaluation L))).
Proof.
apply DPCategoryQuillenA.structured_nerve_quasi_isomorphism=> P.
exact: evaluation_under_augmented_exact.
Qed.
End DPNormalizerLinkingEvaluationCofinality.
