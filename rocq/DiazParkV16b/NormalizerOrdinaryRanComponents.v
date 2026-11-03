(** The actual Ran transpose has the manuscript restriction component at
    every subgroup in the constructed Sylow normalizer collection. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryComma CategoryStructured FusionSystems FusionOrbit FusionSaturation FusionCentralizerMaps.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory NormalizerOrbitPairCategory NormalizerOrbitPairProjection
  LinkingChainActingHom GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  NormalizerOrdinaryCoefficient NormalizerOrdinaryChainComparison NormalizerOrdinaryChainNormalization
  NormalizerOrdinaryRanMap ChainNormalizerFusionOrbit ChainNormalizerCohomologyLimit
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaStructured
  NormalizerProjectionCommaStructuredLimits NormalizerProjectionCommaGroupLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerOrbitPair
  DPLinkingChainActingHom DPGroupCohomologyPullback DPGroupCohomologyOrbitCoefficient
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryChainComparison
  DPNormalizerOrdinaryChainNormalization DPNormalizerOrdinaryRanMap
  DPNormalizerProjectionCommaRepresentatives DPNormalizerProjectionCommaStructuredLimits.
Local Open Scope group_scope.

Module DPNormalizerOrdinaryRanComponents.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation r := (@index_representative S F L p hS sat).
Local Notation hr := (@index_representative_class S F L p hS sat).
Local Notation M := (@representative_coefficient S F L r hr R A n).
Local Notation eta := (@comparison S F L r hr R A n).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation B := (@DPNormalizerProjectionCommaStructured.pair_coefficient S F R
  (centric_coefficient F A n)).

Theorem comparison_collection_coordinate (d : index_object F)
    (P : DPChainNormalizerFusionOrbit.collection_category L (r d)) :
    module_hom_comp (component eta d)
      (module_limit_projection (functor_comp (structured_projection (functor_op proj) d) B)
        (@collection_point S F L p hS sat d P)) =
    pull A (@DPChainNormalizerCohomologyLimit.collection_group_hom S F L (r d) P) n.
Proof.
rewrite comparison_coordinate.
pose X := @collection_point S F L p hS sat d P.
change (compose (fmap M (structured_arrow X))
  (compose (iso_hom (@chain_comparison S F L r hr R A n (r d)))
    (pull A (acting_hom L (acting_normalizes (structured_source X))) n)) =
  pull A (@DPChainNormalizerCohomologyLimit.collection_group_hom S F L (r d) P) n).
rewrite -compose_assoc.
have hn := @representative_chain_comparison_identity S F L r hr R A n d (structured_arrow X).
change (compose (fmap M (structured_arrow X))
  (iso_hom (@chain_comparison S F L r hr R A n (r d))) = identity (fobj M d)) in hn.
rewrite hn compose_id_left.
have ha : acting_normalizes (structured_source X) = @collection_acts S F L (r d) P.
  apply Prop_irrelevance.
rewrite ha collection_acting_hom; reflexivity.
Qed.

Theorem comparison_collection_value (d : index_object F)
    (P : DPChainNormalizerFusionOrbit.collection_category L (r d)) z :
    module_limit_val (module_hom_fun (component eta d) z)
      (@collection_point S F L p hS sat d P) =
    module_hom_fun (pull A (@DPChainNormalizerCohomologyLimit.collection_group_hom S F L (r d) P) n) z.
Proof.
exact (congr1 (fun f => module_hom_fun f z) (comparison_collection_coordinate P)).
Qed.
End Comparison.
End DPNormalizerOrdinaryRanComponents.
