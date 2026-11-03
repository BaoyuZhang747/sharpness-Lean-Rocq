(** Local normalizer/comma acyclicity with the new native cohomology theorem. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits HomologicalModuleIso
 BarHigherLimitVanishing FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
 NormalizerChainNormalizer NormalizerChainEmbedding ChainNormalizerFusionModel
 ChainNormalizerFusionSaturation ChainNormalizerBottomCollection ChainNormalizerFusionCollection
 ChainNormalizerCohomologyCoefficient ChainNormalizerCohomologyHigherLimits
 GroupCohomologyOrbitCoefficient NormalizerChainIndexCategory NormalizerOrbitPairProjection
 NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaHigherLimits
 NormalizerProjectionCommaStructured CategoryRanAcyclicComparisonResolution.
From DiazParkV29 Require Import MainCohomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainEmbedding
 DPChainNormalizerFusionModel DPChainNormalizerCohomologyCoefficient
 DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
 DPNormalizerProjectionCommaHigherLimits DPNormalizerProjectionCommaStructured
 DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV29NormalizerLocal.
Section Local.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.

Theorem field_ambient_collection_higher_zero (c : chain F)
    (hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c))
    (K : fieldType) (charp : p \in [pchar K]) (A : lmodType K) (n j : nat) :
  forall q : derived_limit K (@ambient_coefficient S F L c p sat K A n) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff
  (@DPChainNormalizerCohomologyHigherLimits.ambient_collection_derived_iso S F L p hS sat c hs K A n j.+1)).
exact (@DPV29GroupCohomologySharpness.field_higher_limits_zero _ (local_system L c) p
  (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
  (@DPChainNormalizerFusionSaturation.local_saturated S F L c p hs) K charp A n j).
Qed.

Theorem field_structured_higher_zero (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n (d : index_object F) j :
  forall q : derived_limit K (@structured_coefficient S F d K
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)) j.+1, q = 0.
Proof.
apply/(module_iso_zero_iff (@structured_collection_derived_iso S F L p hS sat d K
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j.+1)).
exact (@field_ambient_collection_higher_zero (@index_representative S F L p hS sat d)
  (@index_representative_sylow S F L p hS sat d) K charp A n j).
Qed.

Theorem field_ran_comma_acyclic (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :
  ran_comma_positive_acyclic K (functor_op (DPNormalizerOrbitPairProjection.projection F))
    (@pair_coefficient S F K (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Proof. exact (fun d j => @field_structured_higher_zero K charp A n d j). Qed.
End Local.
End DPV29NormalizerLocal.
