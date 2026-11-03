(** The actual simultaneous-normalizer image is Sylow when its actual
    fusion automizer is Sylow; saturation constructs such image chains. *)
From mathcomp Require Import all_boot all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionCentricBasics GroupKNormalizer.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects
  LinkingChainAutomorphisms LinkingChainAutomorphismStabilizerEquivalence
  NormalizerChainNormalizer NormalizerChainEmbedding NormalizerChainStabilizer
  NormalizerChainTransport NormalizerChainSylowAutomizer.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPLinkingChainStabilizerEquivalence DPNormalizerChain DPNormalizerChainEmbedding
  DPNormalizerChainStabilizer DPNormalizerChainTransport DPNormalizerChainSylowAutomizer.
Local Open Scope group_scope.

Module DPLinkingChainNormalizerSylow.
Section Sylow.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation P := (val (top c)).
Local Notation K := (fusion_stabilizer c).
Local Notation C := (chain_automorphism_group L c).

Lemma ambient_automorphism_full (Q : {group S}) :
  ambient_automorphism_group [set: S]%G Q = DPFusionSaturation.ambient_aut_group Q.
Proof.
apply val_inj.
change (restrm (subsetIr [set: S] 'N(Q)) (conj_aut Q) @* 'N_[set: S](Q) =
  conj_aut Q @* 'N(Q)).
by rewrite morphim_restrm setTI setIid.
Qed.

Theorem simultaneous_normalizer_order :
  #|normalizer c| = (#|'Z(P)| * #|DPFusionSaturation.ambient_aut_group P :&: K|)%N.
Proof.
rewrite normalizer_eq_k_normalizer k_normalizer_card setTI
  (DPFusionCentricBasics.centric_centralizer_center (valP (top c))).
by rewrite /k_automorphism_group ambient_automorphism_full.
Qed.

Variable p : nat.
Hypothesis hS : p.-group [set: S].

Theorem normalizer_image_sylow
  (hK : p.-Sylow(K) (DPFusionSaturation.ambient_aut_group P :&: K)) :
  p.-Sylow([set: C]) (normalizer_image L c).
Proof.
have hZ : p.-nat #|'Z(P)| := pgroupS (subsetT 'Z(P)) hS.
apply/pHallP; split; first exact: subsetT.
rewrite normalizer_image_card simultaneous_normalizer_order cardsT chain_automorphism_order
  partnM ?cardG_gt0 // (part_pnat_id hZ) -(card_Hall hK).
reflexivity.
Qed.
End Sylow.

Section Representatives.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Hypothesis hS : p.-group [set: S].
Local Notation P := (val (top c)).

Theorem exists_sylow_normalizer_transport (sat : DPFusionSaturation.saturated F p) :
  exists (Q : {group S}) (f : DPFusion.map P Q)
    (hf : DPFusionSystem.allowed F f),
    DPFusion.image f = Q /\ DPFusionSystem.fully_centralized F Q /\
    p.-Sylow([set: chain_automorphism_group L (@transport S F c Q f hf)])
      (normalizer_image L (@transport S F c Q f hf)).
Proof.
have [Q [f [hf [honto [hc hs]]]]] := exists_sylow_automizer_transport c hS sat.
exists Q, f, hf; split=> //; split=> //.
exact: (@normalizer_image_sylow S F L (@transport S F c Q f hf) p hS hs).
Qed.
End Representatives.
End DPLinkingChainNormalizerSylow.

Check DPLinkingChainNormalizerSylow.normalizer_image_sylow.
Check DPLinkingChainNormalizerSylow.exists_sylow_normalizer_transport.
Print Assumptions DPLinkingChainNormalizerSylow.simultaneous_normalizer_order.
Print Assumptions DPLinkingChainNormalizerSylow.normalizer_image_sylow.
Print Assumptions DPLinkingChainNormalizerSylow.exists_sylow_normalizer_transport.
