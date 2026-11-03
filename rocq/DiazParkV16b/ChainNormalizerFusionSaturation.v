(** Saturation of the actual chain-normalizer fusion system on the already
    constructed Sylow representatives. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding NormalizerChainTransport
  LinkingChainAutomorphismStabilizerSylow ChainNormalizerFusionModel
  FiniteGroupFusionEmbeddingSaturation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChain
  DPNormalizerChainEmbedding DPNormalizerChainTransport DPChainNormalizerFusionModel.
Local Open Scope group_scope.

Module DPChainNormalizerFusionSaturation.
Section Saturation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.

Theorem local_saturated
  (hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c)) :
  DPFusionSaturation.saturated (local_system L c) p.
Proof.
exact (DPFiniteGroupFusionEmbeddingSaturation.saturated (normalizer_embedding_injm L c) hs).
Qed.

Theorem exists_saturated_normalizer_transport
  (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p) :
  exists (Q : {group S}) (f : DPFusion.map (val (top c)) Q)
    (hf : DPFusionSystem.allowed F f),
    DPFusion.image f = Q /\ DPFusionSystem.fully_centralized F Q /\
    p.-Sylow([set: chain_automorphism_group L (@transport S F c Q f hf)])
      (normalizer_image L (@transport S F c Q f hf)) /\
    DPFusionSaturation.saturated (local_system L (@transport S F c Q f hf)) p.
Proof.
have [Q [f [hf [honto [hc hs]]]]] :=
  DPLinkingChainNormalizerSylow.exists_sylow_normalizer_transport L c hS sat.
exists Q, f, hf; split=> //; split=> //; split=> //.
exact (DPFiniteGroupFusionEmbeddingSaturation.saturated
  (normalizer_embedding_injm L (@transport S F c Q f hf)) hs).
Qed.
End Saturation.
End DPChainNormalizerFusionSaturation.

Check DPChainNormalizerFusionSaturation.exists_saturated_normalizer_transport.
Print Assumptions DPChainNormalizerFusionSaturation.local_saturated.
Print Assumptions DPChainNormalizerFusionSaturation.exists_saturated_normalizer_transport.
