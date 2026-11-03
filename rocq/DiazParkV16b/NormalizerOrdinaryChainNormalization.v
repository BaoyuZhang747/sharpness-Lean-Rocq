(** Literal normalization at representative chains and their actual local
    acting subgroups. These equations fix the final Ran comparison maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit FusionCentralizerMaps.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  LinkingChainRestrictionUniqueness GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  NormalizerOrdinaryCoefficient NormalizerOrdinaryChainComparison
  LinkingChainActingHom ChainNormalizerCohomologyLimit ChainNormalizerFusionOrbit
  NormalizerChainNormalizer NormalizerChainEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPLinkingChainRestrictionUniqueness
  DPGroupCohomologyPullback DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryChainComparison
  DPLinkingChainActingHom DPNormalizerChain DPNormalizerChainEmbedding.

Module DPNormalizerOrdinaryChainNormalization.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation M := (@representative_coefficient S F L r hr R A n).

Theorem representative_chain_comparison_identity (d : I)
    (u : hom I (chain_class (r d)) d) :
  module_hom_comp (@fmap _ _ M d (chain_class (r d)) u)
    (iso_hom (@chain_comparison S F L r hr R A n (r d))) =
  module_hom_id (fobj M d).
Proof.
change (module_hom_comp
  (pull A (restriction_morphism (@arrow_chain_map S F L r hr _ _ u)) n)
  (pull A (restriction_morphism (@chain_to_representative S F L r hr (r d))) n) =
    module_hom_id (fobj M d)).
rewrite -pull_composition -composite_restriction.
rewrite (@chain_map_pull_unique S F L _ _
  (composite_chain_map (@chain_to_representative S F L r hr (r d))
    (@arrow_chain_map S F L r hr _ _ u)) (identity_chain_map L (r d)) R A n).
rewrite identity_restriction pull_identity; reflexivity.
Qed.
End Comparison.

Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable P : DPChainNormalizerFusionOrbit.collection_category L c.

Definition collection_acts : DPFusionSubgroup.ambient (val P) \subset normalizer c :=
  DPFusionSubgroup.ambient_sub (val P).

Theorem collection_acting_hom :
  @acting_hom S F L c (DPFusionSubgroup.ambient (val P)) collection_acts =
    @DPChainNormalizerCohomologyLimit.collection_group_hom S F L c P.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext=> x.
rewrite DPChainNormalizerCohomologyLimit.collection_group_hom_value.
change (normalizer_embedding L (@acting_normalizer S F c
  (DPFusionSubgroup.ambient (val P)) collection_acts x) =
    normalizer_embedding L (subg (normalizer c) (val x))).
congr (normalizer_embedding L _); apply val_inj.
symmetry; exact (@DPFusionSubgroup.ambient_subgK S (normalizer c) (val P) (val x) (valP x)).
Qed.
End Collection.
End DPNormalizerOrdinaryChainNormalization.
