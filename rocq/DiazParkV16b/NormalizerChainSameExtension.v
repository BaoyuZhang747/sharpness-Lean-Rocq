(** Same-chain arbitrary-carrier extensions are exactly the literal minimal-join
    extensions used by the actual local normalizer fusion system. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainEndoselection NormalizerChainExtensionPreimages
  NormalizerChainExtensions ChainNormalizerFusionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices
  DPNormalizerChainEndoselection DPNormalizerChainExtensionPreimages
  DPNormalizerChainExtensions DPChainNormalizerFusion.
Local Open Scope group_scope.

Module DPNormalizerChainSameExtension.
Section Same.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.

Section ToJoin.
Variable a : extension c c f.

Lemma same_entry_sub_carrier i : subgroup c i \subset carrier a.
Proof. have h := entry_sub_carrier a i; by rewrite endoselection_index in h. Qed.

Lemma same_entry_image i : map_morphism (extension_map a) @* subgroup c i = subgroup c i.
Proof. have h := entry_images a i; by rewrite endoselection_index in h. Qed.

Lemma same_join_sub_carrier : join_subgroup c P \subset carrier a.
Proof.
apply/joing_subP; split; [exact: same_entry_sub_carrier ord_max | exact: acting_sub].
Qed.

Lemma same_join_preimage : join_subgroup c P \subset
    preimage (extension_map a) (join_subgroup c Q).
Proof.
apply/joing_subP; split; apply/subsetP=> x hx; rewrite preimage_mem; apply/andP; split.
- exact: subsetP (same_entry_sub_carrier ord_max) _ hx.
- apply (subsetP (top_sub_join c Q)).
  rewrite -(same_entry_image ord_max).
  exact: mem_morphim (subsetP (same_entry_sub_carrier ord_max) _ hx) hx.
- exact: subsetP (acting_sub a) _ hx.
- rewrite (on_acting a hx); exact: subsetP (acting_sub_join c Q) _ (map_into f hx).
Qed.

Definition join_restriction := restrict (extension_map a) same_join_sub_carrier.

Lemma join_restriction_sub : image join_restriction \subset join_subgroup c Q.
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
rewrite map_morphismE /join_restriction restrict_in //.
have h := subsetP same_join_preimage _ hx.
by move: h; rewrite preimage_mem; move/andP=> [_].
Qed.

Definition join_map : DPFusion.map (join_subgroup c P) (join_subgroup c Q) :=
  corestrict join_restriction_sub.

Lemma join_mapE x : x \in join_subgroup c P -> join_map x = extension_map a x.
Proof. move=> hx; by rewrite /join_map corestrict_in // /join_restriction restrict_in. Qed.

Lemma join_map_allowed : DPFusionSystem.allowed F join_map.
Proof.
apply: DPFusionSystem.corestriction_allowed.
exact: DPFusionSystem.restriction_allowed (extension_allowed a).
Qed.

Lemma join_map_preserves i : image (restrict join_map (@entry_sub_join S F c P i)) = subgroup c i.
Proof.
apply: val_inj; change
 (map_morphism (restrict join_map (@entry_sub_join S F c P i)) @* subgroup c i = subgroup c i).
rewrite /restrict of_morphism_image im_restrm -{2}(same_entry_image i).
apply: eq_in_morphim.
- by rewrite (setIidPr (@entry_sub_join S F c P i)) (setIidPr (same_entry_sub_carrier i)).
- move=> x hx; exact: join_mapE (subsetP (@entry_sub_join S F c P i) _ hx).
Qed.

Theorem extension_to_join : normalizer_extension c f.
Proof.
apply/normalizer_extensionP; exists join_map; split; first exact: join_map_allowed.
split; first exact: join_map_preserves.
move=> x hx; rewrite join_mapE ?(subsetP (acting_sub_join c P) _ hx) //; exact: on_acting.
Qed.
End ToJoin.

Theorem extension_of_join : normalizer_extension c f -> inhabited (extension c c f).
Proof.
move/normalizer_extensionP=> [b [hb [hi hf]]].
pose b' := DPFusion.compose b (inclusion (subsetT (join_subgroup c Q))).
have hb' : DPFusionSystem.allowed F b' :=
  DPFusionSystem.composition_closed hb (DPFusionSystem.inclusion_allowed F _).
have he : forall x, x \in join_subgroup c P -> b' x = b x.
  move=> x hx; by rewrite /b' compose_in // inclusion_in ?map_into.
have ha : forall x, x \in P -> b' x = f x.
  move=> x hx; rewrite he ?(subsetP (acting_sub_join c P) _ hx) //; exact: hf.
have him : forall i, map_morphism b' @* subgroup c (index (DPNormalizerChainIndices.identity c) i)
    = subgroup c i.
  move=> i; rewrite identity_index.
  have h := congr1 val (hi i).
  change (map_morphism (restrict b (@entry_sub_join S F c P i)) @* subgroup c i = subgroup c i) in h.
  rewrite /restrict of_morphism_image im_restrm in h.
  rewrite -{2}h; apply: eq_morphim=> x hx; exact: he hx.
apply: inhabits.
refine (@Build_extension S F c c P Q f (DPNormalizerChainIndices.identity c)
  (join_subgroup c P) (acting_sub_join c P) _ b' hb' ha him).
rewrite identity_index; exact: top_sub_join.
Qed.

Theorem same_extension_iff_join : inhabited (extension c c f) <-> normalizer_extension c f.
Proof. split; [move=> [a]; exact: extension_to_join a | exact: extension_of_join]. Qed.

End Same.
End DPNormalizerChainSameExtension.
