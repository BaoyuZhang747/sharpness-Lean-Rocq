(** The proper ambient-centric collection contains every centric radical
    subgroup of the actual chain-normalizer fusion system. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionRadical
  FusionCentralizerMaps FusionCentricBasics.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding ChainNormalizerFusionModel
  ChainNormalizerBottomNormal FiniteGroupFusionEmbeddingImage FiniteGroupFusionEmbeddingRadical.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChain DPNormalizerChainEmbedding DPChainNormalizerBottom.
Local Open Scope group_scope.

Module DPChainNormalizerBottomCollection.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Hypothesis hS : p.-group [set: S].
Local Notation N := [subg (normalizer c)]%type.
Local Notation E := (normalizer_embedding_morphism L c).
Local Notation H := (DPChainNormalizerFusionModel.local_system L c).

Lemma normalizer_carrier_pgroup : p.-group [set: N].
Proof. rewrite /pgroup cardsT card_sub; exact (pgroupS (subsetT (normalizer c)) hS). Qed.

Theorem centric_radical_contains_bottom (P : {group N}) :
  DPFusionSystem.centric H P -> DPFusionRadical.radical H p P ->
  bottom_subgroup c \subset P.
Proof.
move=> hc hr.
have ho := @DPFiniteGroupFusionEmbeddingRadical.normal_p_subgroup_contained
  N (DPLinkingChainAutomorphisms.chain_automorphism_group L c) E
  (normalizer_embedding_injm L c) p normalizer_carrier_pgroup
  (bottom_image L c) (bottom_image_normal L c) (bottom_image_pgroup L c hS)
  (bottom_image_sub L c) P hc hr.
apply/subsetP=> x hx.
have he : E x \in bottom_image L c := mem_morphim E (in_setT x) hx.
have ha := subsetP ho _ he.
have hi := DPFiniteGroupFusionEmbeddingImage.ambient_repr (normalizer_embedding_injm L c) ha.
by rewrite invmE ?inE in hi.
Qed.

Theorem centric_radical_ambient_contains_bottom (P : {group N}) :
  DPFusionSystem.centric H P -> DPFusionRadical.radical H p P ->
  val (bottom c) \subset DPFusionSubgroup.ambient P.
Proof.
move=> hc hr.
have h := morphimS (@sgval _ (normalizer c)) (centric_radical_contains_bottom hc hr).
change (is_true (DPFusionSubgroup.ambient (bottom_subgroup c) \subset
  DPFusionSubgroup.ambient P)) in h.
by rewrite bottom_subgroup_ambient in h.
Qed.

Theorem centric_radical_ambient_centric (P : {group N}) :
  DPFusionSystem.centric H P -> DPFusionRadical.radical H p P ->
  DPFusionSystem.centric F (DPFusionSubgroup.ambient P).
Proof.
move=> hc hr; exact (DPFusionCentricBasics.centric_overgroup
  (centric_radical_ambient_contains_bottom hc hr) (valP (bottom c))).
Qed.
End Collection.
End DPChainNormalizerBottomCollection.

Check DPChainNormalizerBottomCollection.centric_radical_ambient_centric.
Print Assumptions DPChainNormalizerBottomCollection.centric_radical_contains_bottom.
Print Assumptions DPChainNormalizerBottomCollection.centric_radical_ambient_centric.
