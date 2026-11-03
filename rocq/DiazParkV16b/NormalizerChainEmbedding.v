(** The actual simultaneous normalizer embeds in the actual compatible
    linking-chain automorphism group. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainNormalizer NormalizerChainTransporter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms
  DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChain DPNormalizerChainTransporter.
Local Open Scope group_scope.

Module DPNormalizerChainEmbedding.
Section Embedding.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation N := [subg (normalizer c)]%type.
Local Notation I := 'I_(length c).+1.

Definition coordinate_normalizer (s : N) (i : I) : [subg 'N(subgroup c i)] :=
  Sub (val s) (subsetP (@normalizer_sub S F c i) _ (valP s)).

Definition coordinate (s : N) (i : I) : automorphism_group L (entry c i) :=
  normalizer_map L (coordinate_normalizer s i).

Lemma coordinate_mul (s t : N) (i : I) : coordinate (s * t) i = coordinate s i * coordinate t i.
Proof.
have he : coordinate_normalizer (s * t) i = coordinate_normalizer s i * coordinate_normalizer t i.
  apply val_inj; reflexivity.
rewrite /coordinate he; exact: normalizer_map_mul.
Qed.

Definition normalizer_tuple (s : N) : tuple_group L c := [ffun i => coordinate s i].

Lemma normalizer_tuple_compatible (s : N) : compatible (normalizer_tuple s).
Proof.
apply/compatibleP=> i j hij; rewrite /normalizer_tuple !ffunE.
rewrite /coordinate /normalizer_map /chain_inclusion /inclusion -!transporter_compose.
congr (linking_transporter L _); apply val_inj.
change (val s * 1 = 1 * val s); by rewrite mulg1 mul1g.
Qed.

Definition normalizer_embedding (s : N) : chain_automorphism_group L c.
Proof.
apply: (Sub (normalizer_tuple s)); by rewrite inE normalizer_tuple_compatible.
Defined.

Lemma normalizer_embedding_projection (s : N) (i : I) :
  projection i (normalizer_embedding s) = coordinate s i.
Proof. change (normalizer_tuple s i = coordinate s i); by rewrite /normalizer_tuple ffunE. Qed.

Lemma normalizer_embedding_mul (s t : N) :
  normalizer_embedding (s * t) = normalizer_embedding s * normalizer_embedding t.
Proof.
apply val_inj; apply/ffunP=> i.
change (normalizer_tuple (s * t) i = (normalizer_tuple s * normalizer_tuple t) i).
by rewrite tuple_mulE /normalizer_tuple !ffunE coordinate_mul.
Qed.

Lemma normalizer_embedding_morphic : morphic [set: N] normalizer_embedding.
Proof. apply/morphicP=> s t _ _; exact: normalizer_embedding_mul. Qed.

Definition normalizer_embedding_morphism :
    {morphism [set: N] >-> chain_automorphism_group L c} :=
  [morphism of morphm normalizer_embedding_morphic].

Theorem normalizer_embedding_injective : injective normalizer_embedding.
Proof.
move=> s t he.
have h0 := congr1 (fun a : chain_automorphism_group L c => projection ord0 a) he.
rewrite !normalizer_embedding_projection in h0.
have hn := normalizer_map_injective h0.
have hv := congr1 (fun x : [subg 'N(subgroup c ord0)] => val x) hn.
apply val_inj; exact hv.
Qed.

Theorem normalizer_embedding_injm : 'injm normalizer_embedding_morphism.
Proof. apply/injmP=> s t _ _; exact: normalizer_embedding_injective. Qed.

Definition normalizer_image : {group (chain_automorphism_group L c)} :=
  (normalizer_embedding_morphism @* [set: N])%G.

Theorem normalizer_image_card : #|normalizer_image| = #|normalizer c|.
Proof.
rewrite /normalizer_image (card_injm normalizer_embedding_injm (subxx _)).
by rewrite cardsT card_sub.
Qed.

End Embedding.
End DPNormalizerChainEmbedding.

Print Assumptions DPNormalizerChainEmbedding.normalizer_embedding_injective.
Print Assumptions DPNormalizerChainEmbedding.normalizer_image_card.

