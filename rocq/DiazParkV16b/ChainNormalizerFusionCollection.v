(** Actual all-degree restriction to the ambient-centric collection on a
    Sylow normalizer chain, and constructed such chains in every fusion class. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup sylow boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding NormalizerChainTransport
  ChainNormalizerFusionModel ChainNormalizerFusionOrbit ChainNormalizerBottomCollection
  ChainNormalizerFusionSaturation ChainNormalizerFusionCollectionAdapter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChain
  DPNormalizerChainEmbedding DPNormalizerChainTransport DPChainNormalizerFusionModel
  DPChainNormalizerFusionOrbit DPChainNormalizerFusionSaturation.
Local Open Scope group_scope.

Module DPChainNormalizerFusionCollection.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis hS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.

Definition sylow_collection_derived_iso (c : chain F)
    (hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c))
    (R : pzRingType)
    (D : module_codiagram R (centric_orbit_category (local_system L c))) n :
  @isomorphism (module_category R) (derived_limit R D n)
    (derived_limit R
      (@DPChainNormalizerFusionCollectionAdapter.literal_restriction S F L c p sat R D) n) :=
  @DPChainNormalizerFusionCollectionAdapter.collection_derived_iso S F L c p sat R
    (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
    (@local_saturated S F L c p hs)
    (@DPChainNormalizerBottomCollection.centric_radical_ambient_centric S F L c p hS) D n.

Variable c : chain F.

Definition transport_data := {Q : {group S} & DPFusionSystem.arrow F (val (top c)) Q}.
Definition transport_chain (d : transport_data) : chain F :=
  @transport S F c (projT1 d) (val (projT2 d)) (valP (projT2 d)).

Definition sylow_transport_property (d : transport_data) : Prop :=
  DPFusion.image (val (projT2 d)) = projT1 d /\
  DPFusionSystem.fully_centralized F (projT1 d) /\
  p.-Sylow([set: chain_automorphism_group L (transport_chain d)])
    (normalizer_image L (transport_chain d)).

Lemma sylow_transport_exists : exists d : transport_data, sylow_transport_property d.
Proof.
have [Q [f [hf [ho [hc [hs _]]]]]] :=
  exists_saturated_normalizer_transport L c hS sat.
pose a : DPFusionSystem.arrow F (val (top c)) Q := Sub f hf.
exists (existT (fun Q => DPFusionSystem.arrow F (val (top c)) Q) Q a).
split; first exact ho.
split; first exact hc.
have he : valP a = hf := Prop_irrelevance _ _.
change (is_true (p.-Sylow([set: chain_automorphism_group L
  (@transport S F c Q f (valP a))])
  (normalizer_image L (@transport S F c Q f (valP a))))).
by rewrite he.
Qed.

Definition chosen_transport : transport_data := proj1_sig (cid sylow_transport_exists).

Lemma chosen_transport_spec : sylow_transport_property chosen_transport.
Proof. exact (proj2_sig (cid sylow_transport_exists)). Qed.

Definition sylow_representative : chain F := transport_chain chosen_transport.

Lemma representative_top_image :
  DPFusion.image (val (projT2 chosen_transport)) = projT1 chosen_transport.
Proof. exact (proj1 chosen_transport_spec). Qed.

Lemma representative_top_fully_centralized :
  DPFusionSystem.fully_centralized F (projT1 chosen_transport).
Proof. exact (proj1 (proj2 chosen_transport_spec)). Qed.

Lemma representative_sylow :
  p.-Sylow([set: chain_automorphism_group L sylow_representative])
    (normalizer_image L sylow_representative).
Proof. exact (proj2 (proj2 chosen_transport_spec)). Qed.

Lemma representative_saturated :
  DPFusionSaturation.saturated (local_system L sylow_representative) p.
Proof. exact: local_saturated representative_sylow. Qed.

Definition representative_collection_derived_iso (R : pzRingType)
    (D : module_codiagram R (centric_orbit_category (local_system L sylow_representative))) n :
  @isomorphism (module_category R) (derived_limit R D n)
    (derived_limit R
      (@DPChainNormalizerFusionCollectionAdapter.literal_restriction
        S F L sylow_representative p sat R D) n) :=
  sylow_collection_derived_iso representative_sylow D n.

End Collection.
End DPChainNormalizerFusionCollection.
